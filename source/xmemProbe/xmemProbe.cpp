// Local RE tooling for the virus-os-decompile project, NOT part of upstream gearmulator.
//
// Boots the real DSP56300 TI2 firmware, loads a real factory preset with the Vocoder
// engaged, lets it run long enough to process notes, then dumps specific X-memory
// ranges to test the "single-instance, ownership-arbitrated 32-slot harmonic engine"
// (X:$b52/$b53 claim flags, X:0x49800 32-slot table) hypothesis documented in
// doc/dsp56300_synth_engine.md. See insights.md for background.
//
// Modeled closely on virusConsoleLib/consoleApp.cpp's ConsoleApp::run(), just with a
// memory dump instead of/after audio rendering.

#include <algorithm>
#include <iomanip>
#include <fstream>
#include <iostream>
#include <limits>
#include <vector>

#include <csignal>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <fcntl.h>
#include <unistd.h>

// Fault-address capture for the FM-Mode-3 ("Noise") SIGBUS investigation
// (work/dsp_fm_noise_sigbus_findings.md). DefaultMemoryValidator does no bounds
// checking and the JIT indexes the DSP memory buffer directly, so a
// firmware-computed out-of-range DSP address faults the host process. We register
// the DSP memory-buffer base/size ranges, then on SIGBUS/SIGSEGV map the faulting
// host address back to a DSP (area, word offset) and print it.
namespace dsp56k { class DSP; }  // forward decl; full type (getPC) used only in dspPcLine below

namespace {
struct MemRange { const char* label; uintptr_t base; uintptr_t end; };
MemRange g_memRanges[8];
sig_atomic_t g_numMemRanges = 0;
dsp56k::DSP* g_faultDsp1 = nullptr;
dsp56k::DSP* g_faultDsp2 = nullptr;
int dspPcLine(char* _buf, size_t _n);  // defined after dsp.h include
void registerMemRange(const char* _label, const void* _base, size_t _wordCount)
{
	if (g_numMemRanges >= 8) return;
	MemRange& r = g_memRanges[g_numMemRanges++];
	r.label = _label;
	r.base = reinterpret_cast<uintptr_t>(_base);
	r.end = r.base + _wordCount * sizeof(uint32_t);
}

// Host-code-range <-> DSP-PC-range map of every JIT block ever created, appended from
// AddrTracker::onJitBlockCreated (2026-07-21, FM-Noise SIGBUS MMU trace). Ring buffer,
// scanned newest-first at fault time so host-address reuse after block destruction
// resolves to the most recent (= live) block. Plain C types only: written on the DSP
// threads, read from the signal handler.
struct JitBlockRec { uintptr_t hostStart; uintptr_t hostEnd; uint32_t pcFirst; uint32_t pcNext; char dsp; };
constexpr size_t kMaxJitBlockRecs = 1 << 18;
JitBlockRec g_jitBlockRecs[kMaxJitBlockRecs];
volatile size_t g_numJitBlockRecs = 0;  // monotonically increasing; index mod kMaxJitBlockRecs
void recordJitBlock(char _dsp, const void* _host, size_t _codeSize, uint32_t _pcFirst, uint32_t _pcNext)
{
	const size_t i = g_numJitBlockRecs;
	JitBlockRec& r = g_jitBlockRecs[i % kMaxJitBlockRecs];
	r.hostStart = reinterpret_cast<uintptr_t>(_host);
	r.hostEnd = r.hostStart + _codeSize;
	r.pcFirst = _pcFirst;
	r.pcNext = _pcNext;
	r.dsp = _dsp;
	g_numJitBlockRecs = i + 1;
}

// Print every /proc/self/maps line whose range contains one of the two addresses --
// definitively classifies the faulting host PC (exe .text vs JIT anon page vs lib) and
// the fault address (unmapped vs reserved-PROT_NONE region). Streaming parse, no malloc.
void printMapsLinesContaining(uintptr_t _a, uintptr_t _b)
{
	const int fd = open("/proc/self/maps", O_RDONLY);
	if (fd < 0) return;
	static char chunk[8192];
	static char line[512];
	size_t lineLen = 0;
	ssize_t got;
	while ((got = read(fd, chunk, sizeof(chunk))) > 0)
	{
		for (ssize_t i = 0; i < got; ++i)
		{
			const char c = chunk[i];
			if (c != '\n')
			{
				if (lineLen < sizeof(line) - 1) line[lineLen++] = c;
				continue;
			}
			line[lineLen] = 0;
			char* endp = nullptr;
			const uintptr_t s = strtoull(line, &endp, 16);
			const uintptr_t e = (endp && *endp == '-') ? strtoull(endp + 1, nullptr, 16) : 0;
			if ((_a >= s && _a < e) || (_b >= s && _b < e))
			{
				char out[600];
				const int n = snprintf(out, sizeof(out), "[FAULT] maps: %s%s%s\n", line,
					(_a >= s && _a < e) ? " <-- host PC" : "",
					(_b >= s && _b < e) ? " <-- fault addr" : "");
				(void)!write(2, out, n);
			}
			lineLen = 0;
		}
	}
	close(fd);
}
void faultHandler(int _sig, siginfo_t* _info, void* _ucontext)
{
	const uintptr_t addr = reinterpret_cast<uintptr_t>(_info->si_addr);
	char buf[256];
	int n = snprintf(buf, sizeof(buf), "\n[FAULT] signal %d at host addr %p\n", _sig, _info->si_addr);
	(void)!write(2, buf, n);
	// Host PC from ucontext (ARM64 Linux). If PC == fault addr -> instruction-fetch fault
	// (the JIT executed a bad computed jump/call); if different -> a data access fault.
	uintptr_t pc = 0;
	if (_ucontext)
	{
		const auto* uc = static_cast<const ucontext_t*>(_ucontext);
#if defined(__aarch64__)
		pc = uc->uc_mcontext.pc;
#elif defined(__x86_64__)
		pc = uc->uc_mcontext.gregs[REG_RIP];
#endif
		n = snprintf(buf, sizeof(buf), "[FAULT] host PC %p (%s)\n", reinterpret_cast<void*>(pc),
			pc == addr ? "INSTRUCTION-FETCH: JIT jumped to bad address" : "data access");
		(void)!write(2, buf, n);
#if defined(__aarch64__)
		// Full GP register dump: with the faulting instruction's encoding this identifies
		// the base and index registers and their exact values (the dirty >24-bit DSP
		// address is expected in one of these).
		for (int i = 0; i < 31; i += 2)
		{
			if (i + 1 < 31)
				n = snprintf(buf, sizeof(buf), "[FAULT] x%-2d = %016llx  x%-2d = %016llx\n",
					i, static_cast<unsigned long long>(uc->uc_mcontext.regs[i]),
					i + 1, static_cast<unsigned long long>(uc->uc_mcontext.regs[i + 1]));
			else
				n = snprintf(buf, sizeof(buf), "[FAULT] x%-2d = %016llx\n",
					i, static_cast<unsigned long long>(uc->uc_mcontext.regs[i]));
			(void)!write(2, buf, n);
		}
		n = snprintf(buf, sizeof(buf), "[FAULT] sp  = %016llx\n",
			static_cast<unsigned long long>(uc->uc_mcontext.sp));
		(void)!write(2, buf, n);
		// Faulting instruction word plus context (data-access fault only: PC itself is
		// executable and therefore readable; skip if the fault WAS the instruction fetch).
		if (pc && pc != addr)
		{
			const uint32_t* code = reinterpret_cast<const uint32_t*>(pc);
			n = snprintf(buf, sizeof(buf),
				"[FAULT] code @pc-8: %08x %08x [%08x] %08x %08x\n",
				code[-2], code[-1], code[0], code[1], code[2]);
			(void)!write(2, buf, n);
		}
#endif
	}
	// Which mappings (if any) contain the host PC and the fault address?
	printMapsLinesContaining(pc, addr);
	// Map host PC back to the JIT block that contains it -> the block's DSP P-memory
	// range, i.e. the faulting DSP instruction is within [pcFirst, pcNext).
	{
		const size_t total = g_numJitBlockRecs;
		const size_t scan = total < kMaxJitBlockRecs ? total : kMaxJitBlockRecs;
		bool found = false;
		for (size_t k = 0; k < scan && !found; ++k)
		{
			const JitBlockRec& r = g_jitBlockRecs[(total - 1 - k) % kMaxJitBlockRecs];
			if (pc >= r.hostStart && pc < r.hostEnd)
			{
				n = snprintf(buf, sizeof(buf),
					"[FAULT] host PC is inside JIT block dsp%c P:$%06x..$%06x (host %p+0x%zx, %zu blocks seen)\n",
					r.dsp, r.pcFirst, r.pcNext - 1, reinterpret_cast<void*>(r.hostStart),
					pc - r.hostStart, total);
				(void)!write(2, buf, n);
				found = true;
			}
		}
		if (!found)
		{
			n = snprintf(buf, sizeof(buf),
				"[FAULT] host PC not in any recorded JIT block (%zu blocks seen)\n", total);
			(void)!write(2, buf, n);
		}
	}
	// Best-effort DSP PC (last-synced; may be the current JIT block start under JIT).
	if (g_faultDsp1)
	{
		n = dspPcLine(buf, sizeof(buf));
		(void)!write(2, buf, n);
	}
	for (int i = 0; i < g_numMemRanges; ++i)
	{
		const uintptr_t base = g_memRanges[i].base;
		const uintptr_t end = g_memRanges[i].end;
		const char* label = g_memRanges[i].label;
		const size_t words = (end - base) / sizeof(uint32_t);
		if (addr >= base && addr < end)
			n = snprintf(buf, sizeof(buf), "[FAULT] inside %s: DSP word offset 0x%zx\n",
				label, (addr - base) / sizeof(uint32_t));
		else
			n = snprintf(buf, sizeof(buf), "[FAULT] vs %s base %p: delta %+ld words (range 0x%zx words)\n",
				label, reinterpret_cast<void*>(base),
				(static_cast<long>(addr) - static_cast<long>(base)) / static_cast<long>(sizeof(uint32_t)), words);
		(void)!write(2, buf, n);
	}
	_exit(137);
}
void installFaultHandler()
{
	struct sigaction sa{};
	sa.sa_sigaction = faultHandler;
	sa.sa_flags = SA_SIGINFO;
	sigaction(SIGBUS, &sa, nullptr);
	sigaction(SIGSEGV, &sa, nullptr);
}
}

#include "virusConsoleLib/audioProcessor.h"

#include "virusLib/device.h"
#include "virusLib/microcontroller.h"
#include "virusLib/romfile.h"
#include "virusLib/romloader.h"

#include "dsp56kEmu/audio.h"
#include "dsp56kEmu/memory.h"
#include "dsp56kEmu/debuggerinterface.h"
#include "dsp56kEmu/dsp.h"
#include "dsp56kEmu/jitblockruntimedata.h"
#include "dsp56kBase/semaphore.h"
#include "baseLib/filesystem.h"

// Milestone 4 Phase B (work/8051_oracle_milestone4_design_2026-07-28.md): the byte-triplet <->
// 24-bit-word assembler used by the "hdi08_relay" mode below. Kept as a same-directory copy
// (reconstitution recipe: doc/tooling.md's xmemProbe section) rather than a relative
// "../../../gearmulator_local_tools/..." include, since the Docker build only bind-mounts
// dsp56300/gearmulator itself (per doc/tooling.md), not its parent dsp56300/ directory, so a
// parent-relative include would not resolve inside the container.
#include "hdi08_triplet_assembler.h"

#include <atomic>
#include <chrono>
#include <thread>
#include <map>
#include <set>
#include <sstream>

using namespace virusLib;
using namespace synthLib;

namespace {
int dspPcLine(char* _buf, size_t _n)
{
	return snprintf(_buf, _n, "[FAULT] DSP1 PC ~P:$%06x  DSP2 PC ~P:$%06x\n",
		g_faultDsp1 ? g_faultDsp1->getPC().toWord() : 0,
		g_faultDsp2 ? g_faultDsp2->getPC().toWord() : 0);
}
}

namespace
{
	void dumpRange(const dsp56k::Memory& _mem, dsp56k::EMemArea _area, const char* _areaName, uint32_t _addr, uint32_t _count, std::ostream& _out)
	{
		_out << "--- " << _areaName << ":0x" << std::hex << _addr << " (" << std::dec << _count << " words) ---\n";
		for (uint32_t i = 0; i < _count; ++i)
		{
			const auto v = _mem.get(_area, _addr + i);
			_out << std::hex << std::uppercase;
			_out << "  " << _areaName << ":$" << (_addr + i) << " = $" << v << "\n";
		}
		_out << std::dec;
	}

	// Walks the active-voice linked list per doc/dsp56300_synth_engine.md's "Active-voice
	// linked-list traversal" + func_000de0/de1/de2 sections: the confirmed top-level driver
	// (func_000de0) seeds r1=0 before the *first* iterator call, which reads X:(r1+$1) == X:$1 --
	// i.e. X:$1 is the real head-of-list global cell (not r1=0x1f38 directly, which is only used
	// as the mid-loop *reset* value/sentinel). Each subsequent step reads X:(r1+$1) as the current
	// node's "next" field and advances r1 to it. Termination is genuinely ambiguous between two
	// documented readings -- func_000113's caller-facing description says "checks r1==0x1f38", but
	// the concrete func_000de2 driver code tests "a==0" (a is the freshly-read next-pointer value)
	// -- so this walk defensively treats *either* a 0 or a 0x1f38 next-value as list-end, plus a
	// visited-set cycle guard, so a wrong assumption here fails safe (stops walking) rather than
	// looping forever or silently misreporting the count.
	//
	// Per-node fields dumped are restricted to offsets this project has actually documented and
	// traced a read/write for (not guessed): +$1 (next pointer, implicit in the walk itself),
	// +$2 (the field func_00024c caches into X:$54136 when resolving a voice's primary), +$3 (the
	// per-voice state/gate field func_000de4 and func_04f630 both touch every tick), +$27 (the
	// validity/gate field func_000124 checks, also used as a scatter-table index by one
	// func_00024c caller pattern), and +$126 (the primary-voice back-pointer func_00024c reads and
	void dumpVoiceLinkedList(const dsp56k::Memory& _mem, std::ostream& _out)
	{
		_out << "--- Active-voice linked-list walk (head cell X:$1F39, next field node+$1, sentinel/reset value X:$0) ---\n";
		std::vector<uint32_t> visited;
		uint32_t r1 = 0x1F38; // bootstrap: X:(0x1F38+$1) == X:$1F39, the true head-of-list cell
		int count = 0;

		while (true)
		{
			if (count >= 100)
			{
				_out << "  -- WALK LIMIT (100) REACHED, stopping.\n";
				break;
			}
			_out << "  step " << count << ": read X:$" << std::hex << std::uppercase << (r1 + 0x1) << " = ";
			const auto next = _mem.get(dsp56k::MemArea_X, r1 + 0x1);
			_out << "$" << next << "\n";

			if (next == 0x0)
			{
				_out << "  -- terminator reached (0), stopping.\n";
				break;
			}
			if (std::find(visited.begin(), visited.end(), next) != visited.end())
			{
				_out << "  -- CYCLE DETECTED (node $" << std::hex << std::uppercase << next
					<< std::dec << " already visited), stopping to avoid an infinite loop.\n";
				break;
			}
			visited.push_back(next);
			r1 = next;
			++count;

			const auto f2 = _mem.get(dsp56k::MemArea_X, r1 + 0x2);
			const auto f3 = _mem.get(dsp56k::MemArea_X, r1 + 0x3);
			const auto f27 = _mem.get(dsp56k::MemArea_X, r1 + 0x27);
			const auto f126 = _mem.get(dsp56k::MemArea_X, r1 + 0x126);
			// verification-pass shortlist item #3: doc/dsp56300_synth_engine.md:845-849's
			// "y:(r0+$2c)" oscillator type-code check -- r0 is a working-register copy of the same
			// per-voice base this list walk resolves via r1 (same convention documented elsewhere
			// in this codebase), so reading Y:(node+$2c) here (X: too, for comparison) should be the
			// live value that field check compares against -3/2.
			const auto f2cX = _mem.get(dsp56k::MemArea_X, r1 + 0x2c);
			const auto f2cY = _mem.get(dsp56k::MemArea_Y, r1 + 0x2c);
			_out << "  node " << count << ": addr=X:$" << std::hex << std::uppercase << r1
				<< "  +$2=$" << f2 << "  +$3=$" << f3 << "  +$27=$" << f27
				<< "  +$126(primary-back-ptr)=$" << f126
				<< "  +$2c(X)=$" << f2cX << "  +$2c(Y)=$" << f2cY << std::dec << "\n";
		}
		_out << "TOTAL ACTIVE-VOICE NODES: " << count << "\n";
	}

	// "vm_watch" mode: follow-up to work/dsp_c9e8_chorus_live_sweep_findings.md, which ruled out
	// Chorus (all 7 modes, all 4 knobs) as func_05c9e8's trigger and flagged that the harness only
	// ever snapshots once at the very end of an 8s render -- invisible to any transient-only
	// trigger (patch-load crossfade, program-change, envelope retrigger) regardless of which
	// parameter is swept. This mode instead dumps the VM's struct range (X:$5c670-$5c6ff, both
	// DSPs) at multiple points across a single continuous render, bracketing a chain of candidate
	// trigger events (Delay/Phaser/Reverb Mode on/off, a MIDI Program Change, a second Note On)
	// fired at spaced-out audioCallbackCount checkpoints via the same live-SysEx/MIDI mechanism the
	// "unison_live"-style experiments above already use.
	//
	// 2026-07-15 redesign, after a real deadlock was root-caused (see
	// work/dsp_c9e8_vm_watch_findings.md): an earlier version of this mode chunked the render into
	// many separate AudioProcessor segments (dump between segments, construct a fresh
	// AudioProcessor per segment). That design reliably renders its FIRST segment, then hangs
	// (0.01% CPU, indefinitely) the moment a SECOND AudioProcessor is constructed against the same
	// already-booted DspSingle -- confirmed independent of segment count/size (reproduces with as
	// few as 2 segments, not just the original 300-segment fine-grained attempt). Root cause inside
	// gearmulator's own producer/consumer plumbing not chased further (out of this project's scope
	// -- xmemProbe is local tooling, not a thing we maintain). Fix: never construct more than one
	// AudioProcessor. This version renders ONCE for the whole duration and performs every dump
	// directly inside the existing per-sample ESAI callback, the same call context that already
	// safely sends live SysEx/MIDI events mid-render elsewhere in this file -- so no new
	// cross-thread memory access pattern is introduced.

	// "pc_trace" mode: work/dsp_osc_thread3_live_probe_and_correction.md left a genuinely open
	// question -- does the P-memory chain $055e0a->$055e25->$055e46->$055e5d->$055e74->$055eb8
	// (containing a jsr to the illegal-opcode address $04f947) actually execute in normal
	// operation, or is it dead/vestigial like the already-confirmed-dead func_054ba6? Static
	// re-reading can't settle this (that's exactly what made it a boundary in the first place).
	// dsp56kEmu already ships a DebuggerInterface hook (debuggerinterface.h) that isn't wired up
	// to anything in this build -- onJitBlockCreated fires once per newly-JIT-compiled block with
	// its [pcFirst, pcNext) P-memory range, which is a cheap, non-invasive way to ask "was this
	// address ever the target of code the JIT actually compiled" without needing a full
	// per-instruction interpreter-mode trace (g_useJIT is a compile-time constant on this
	// platform, not runtime-switchable, so per-instruction onExec tracing isn't available without
	// a separate non-JIT build). Indirect jumps like the chain's own `jmp (r5)` end a JIT block,
	// so each chain step should compile as its own block with a start PC matching our target
	// addresses closely, if it's ever reached at all.
	// `doc/instrument_defects.md` class 23's rule, IMPLEMENTED rather than merely written down:
	// "an instrument must assert its own preconditions and refuse to emit an empty result."
	//
	// Without this, the two known failure modes both present as a tidy report in which every
	// target reads NOT REACHED and the exit code is 0 -- indistinguishable from a genuine
	// all-negative result, and read as one on 2026-08-02
	// (work/page112_sweep_coverage_gap_2026-08-02.md). A zero from an instrument must be LOUD
	// and distinguishable from "not installed".
	//
	// Returns an empty string when the instrument is trustworthy, otherwise the reason.
	inline std::string coverageInstrumentFatal(const size_t _dsp1Blocks)
	{
#if !defined(DSP56K_DEBUGGER_HOOKS) || !DSP56K_DEBUGGER_HOOKS
		return "DSP56K_DEBUGGER_HOOKS is not compiled in, so onJitBlockCreated is never called and "
		       "this mode can only ever report zero. Verify the GENERATED build (build.ninja / "
		       "flags.make), never CMakeCache.txt -- the cache records what was ASKED FOR, the "
		       "generated build records what will be COMPILED.";
#elif defined(DSP56K_FORCE_INTERPRETER) && DSP56K_FORCE_INTERPRETER
		(void)_dsp1Blocks;
		return "this is a FORCE_INTERPRETER build. Nothing is JIT-compiled, so JIT-block coverage "
		       "is VACUOUS BY CONSTRUCTION here -- not empty because the firmware did nothing. Run "
		       "this on the JIT build; use the interpreter build only for modes counting executed "
		       "PCs.";
#else
		// Runtime floor. A healthy run on 5.1.7.00 compiles ~3,700 distinct blocks on dsp1
		// (measured 2026-08-02: 3,697 dsp1 / 3,287 dsp2). The documented broken state produced
		// THREE -- dspthread.cpp's deferred-attach reset silently unhooking the tracker after
		// ~128 instructions. 100 sits far below the healthy figure and far above the broken one,
		// so it discriminates the two rather than merely being nonzero.
		constexpr size_t kMinBlocks = 100;
		if (_dsp1Blocks < kMinBlocks)
			return "dsp1 compiled only " + std::to_string(_dsp1Blocks) + " distinct JIT blocks, "
			       "below the floor of " + std::to_string(kMinBlocks) + ". A healthy run is "
			       "~3,700. A tiny nonzero count is the signature of the tracker being UNHOOKED "
			       "mid-run (see dspthread.cpp's deferred-attach comment), not of a quiet firmware.";
		return {};
#endif
	}

	// Emits the banner to both the report and the console, so neither a file reader nor a
	// shell-scripted caller can miss it. Callers must return NON-ZERO after this.
	inline void writeInstrumentFatal(std::ostream& _out, const std::string& _reason)
	{
		const std::string banner =
			"\n================ INSTRUMENT PRECONDITION FAILED ================\n"
			"MEASURED NOTHING USABLE. Do not read this report as evidence of\n"
			"absence -- it is evidence of an uninstalled instrument.\n\n"
			"  " + _reason + "\n"
			"===============================================================\n";
		_out << banner;
		std::cout << banner;
	}

	class AddrTracker final : public dsp56k::DebuggerInterface
	{
	public:
		AddrTracker(dsp56k::DSP& _dsp, std::string _label) : DebuggerInterface(_dsp), m_label(std::move(_label)) {}

		void onJitBlockCreated(const dsp56k::JitDspMode&, const dsp56k::JitBlockRuntimeData* _block) override
		{
			if (!_block)
				return;
			m_blockStarts.insert(_block->getPCFirst());
			m_blockRanges.emplace_back(_block->getPCFirst(), _block->getPCNext());
			// Also record the block's host code range for the SIGBUS handler's
			// host-PC -> DSP-PC mapping (FM-Noise MMU trace, 2026-07-21).
			recordJitBlock(m_label.empty() ? '?' : m_label.back(),
				reinterpret_cast<const void*>(_block->getFunc()), _block->getCodeSize(),
				_block->getPCFirst(), _block->getPCNext());
		}

		bool covers(dsp56k::TWord _addr) const
		{
			for (const auto& r : m_blockRanges)
				if (_addr >= r.first && _addr < r.second)
					return true;
			return false;
		}

		const std::string m_label;
		std::set<dsp56k::TWord> m_blockStarts;
		std::vector<std::pair<dsp56k::TWord, dsp56k::TWord>> m_blockRanges;
	};

	// =============================================================================================
	// SPECULATIVE-COMPILATION FLAG (2026-08-03) -- why a BLOCK-START is not evidence of execution
	// =============================================================================================
	//
	// AddrTracker above records onJitBlockCreated, i.e. block CREATION. gearmulator's JIT compiles
	// BOTH ARMS of a conditional branch when the PARENT block is compiled:
	//
	//   jitblock.cpp:401       terminationReason = Branch;
	//                          branchIsConditional = hasField(instA, Field_CCCC)
	//                                             || hasField(instA, Field_bbbbb);
	//   jitblock.cpp:414       child          = _chain->getChildBlock(&_rt, branchTarget);
	//   jitblock.cpp:425       nonBranchChild = _chain->getChildBlock(&_rt, pcLast);  // if conditional
	//   jitblockchain.cpp:325  getChildBlock -> create(_pc, /*_execute=*/false);
	//   jitblockchain.cpp:411  emit() fires onJitBlockCreated UNCONDITIONALLY.
	//
	// So an address that is the target of a jXX/bXX can appear in the block-start list HAVING NEVER
	// RUN. Measured 2026-08-03: with Delay Send 90, $50F14 appears while $50F1D -- its own DO-loop
	// body eight words later -- does not. That is the exact signature of a speculatively compiled,
	// never-taken branch, and it was read as execution for a day
	// (work/f14_anomaly_and_second_override_2026-08-03.md).
	//
	// The rule that made this mechanical rather than a note in a work file: a prose-only lesson is a
	// backlog item, not a record (AGENTS.md, "an incident is not closed until it has a GATE").
	//
	// WHAT THE TABLE IS. Every P address that is the static direct target of a conditional branch,
	// extracted from work/vti2_pmem_full_disasm_repaired.txt by tools/gen_speculative_targets.py
	// using the SAME PREDICATE the JIT uses -- the branch opcode carries a CCCC condition field or a
	// bbbbb bit-number field (dsp56kEmu/opcodeinfo.h: every entry flagged OpFlagBranch |
	// OpFlagCondition). That covers Jcc/Bcc/JScc/BScc and the bit-test branches
	// Jclr/Jset/JSclr/JSset/Brclr/Brset/BSclr/BSset.
	//
	// WHAT IT IS NOT -- read this before treating an UNFLAGGED address as safe:
	//
	//  * It is a FLOOR on speculation risk, not a certificate. Speculation CASCADES: jitblock.cpp:414
	//    calls getChildBlock for UNCONDITIONAL direct branches too (it merely skips the
	//    nonBranchChild), so a bsr/jmp target reached from inside a speculatively-compiled block can
	//    itself be speculatively compiled. Modelling that needs a full CFG with dsp56kEmu's exact
	//    block-termination rules and is deliberately out of scope here. 1,708 addresses in this image
	//    are unconditional-branch targets and are NOT flagged.
	//  * Dynamic targets -- `jmp (rn)`, `Bcc Rn` -- are genuinely unreachable by speculation:
	//    getBranchTarget returns g_dynamicAddress and jitblock.cpp:409 sets childAddr without ever
	//    calling getChildBlock. 601 such sites. This is why $000A58 (reached only via `jmp (r2)`) is
	//    correctly unflagged.
	//  * The table is derived from a STATIC listing, so regions of data disassembled as code
	//    contribute false positives. 18.0% of the 3,724 dsp1 block starts in a real run are flagged,
	//    so the annotation discriminates rather than painting everything.
	//
	// A FLAGGED address may still have executed. The flag says "this entry cannot distinguish the
	// two"; the distinguishing evidence is a DOWNSTREAM block start inside the same function (the
	// $50F1D test above), or covered-mid-block on an address past the branch.
	//
	// GENERATED by tools/gen_speculative_targets.py -- do not hand-edit.
	// Source: work/vti2_pmem_full_disasm_repaired.txt
	// 4402 distinct addresses that are the static target of a conditional branch.
	static const uint32_t g_condBranchTargets[] = {
		0x00000, 0x00002, 0x00004, 0x00006, 0x00008, 0x0000A, 0x0000C, 0x0000E, 0x00010, 0x00012, 0x00014, 0x00016,
		0x00018, 0x0001C, 0x0001E, 0x00030, 0x0004E, 0x0007E, 0x00101, 0x00103, 0x00104, 0x00105, 0x00106, 0x00107,
		0x00108, 0x00109, 0x0010A, 0x0010B, 0x0010C, 0x0010D, 0x0010E, 0x0010F, 0x00110, 0x00111, 0x00112, 0x00113,
		0x00114, 0x00115, 0x00116, 0x00117, 0x00118, 0x00119, 0x0011B, 0x0011C, 0x0011D, 0x0011E, 0x0011F, 0x00122,
		0x00124, 0x00125, 0x00127, 0x0012A, 0x00147, 0x0015A, 0x0017B, 0x0019B, 0x001A2, 0x001C8, 0x001E1, 0x001E9,
		0x001F0, 0x00204, 0x00205, 0x00206, 0x00207, 0x00208, 0x00209, 0x0020A, 0x0020B, 0x0020C, 0x0020D, 0x0020E,
		0x0020F, 0x00210, 0x00212, 0x00213, 0x00214, 0x00215, 0x00216, 0x00217, 0x00218, 0x00219, 0x0021A, 0x0021B,
		0x0021D, 0x0021E, 0x0021F, 0x00220, 0x00221, 0x00222, 0x00224, 0x00229, 0x00230, 0x0023C, 0x0023F, 0x002A0,
		0x002BA, 0x002BC, 0x002BF, 0x002C6, 0x002C7, 0x002C8, 0x002D3, 0x002D8, 0x002E5, 0x002F1, 0x00301, 0x00302,
		0x00303, 0x00304, 0x00305, 0x00306, 0x00307, 0x00308, 0x00309, 0x0030A, 0x0030B, 0x0030C, 0x0030D, 0x0030E,
		0x0030F, 0x00310, 0x00311, 0x00312, 0x00313, 0x00314, 0x00315, 0x00316, 0x00317, 0x00318, 0x0031B, 0x0031E,
		0x00320, 0x00323, 0x00325, 0x00326, 0x0032A, 0x0032C, 0x00336, 0x00337, 0x0033F, 0x00341, 0x00344, 0x00345,
		0x0039D, 0x003A9, 0x00400, 0x00401, 0x00402, 0x00403, 0x00404, 0x00405, 0x00406, 0x00407, 0x00408, 0x00409,
		0x0040A, 0x0040B, 0x0040C, 0x0040D, 0x0040E, 0x0040F, 0x00410, 0x00411, 0x00412, 0x00413, 0x00414, 0x00415,
		0x00416, 0x00417, 0x00419, 0x0041A, 0x0041E, 0x00429, 0x0042E, 0x0045C, 0x0045D, 0x00469, 0x0046C, 0x00483,
		0x00492, 0x0049E, 0x004A4, 0x004D1, 0x004E4, 0x004FD, 0x00500, 0x00501, 0x00502, 0x00503, 0x00504, 0x00505,
		0x00506, 0x00507, 0x00508, 0x00509, 0x0050A, 0x0050B, 0x0050C, 0x0050D, 0x0050E, 0x0050F, 0x00510, 0x00511,
		0x00512, 0x00513, 0x00515, 0x00516, 0x00517, 0x00518, 0x00519, 0x0051C, 0x0051D, 0x0051E, 0x00521, 0x00524,
		0x00526, 0x0052C, 0x0052E, 0x00532, 0x00543, 0x00549, 0x00575, 0x0057E, 0x0058F, 0x0059B, 0x005AF, 0x005D1,
		0x005D2, 0x005DB, 0x005E5, 0x005F6, 0x005FB, 0x00600, 0x00601, 0x00602, 0x00603, 0x00604, 0x00605, 0x00606,
		0x00607, 0x00608, 0x00609, 0x0060A, 0x0060B, 0x0060C, 0x0060D, 0x0060E, 0x0060F, 0x00610, 0x00611, 0x00612,
		0x00613, 0x00614, 0x00615, 0x00616, 0x00617, 0x00618, 0x00619, 0x0061B, 0x0061C, 0x0061D, 0x0061E, 0x00622,
		0x00625, 0x00626, 0x00627, 0x0062E, 0x0063F, 0x00640, 0x00646, 0x00650, 0x00657, 0x00679, 0x00687, 0x00696,
		0x00699, 0x006C8, 0x006CE, 0x006D8, 0x006FF, 0x00700, 0x00701, 0x00702, 0x00703, 0x00704, 0x00705, 0x00706,
		0x00707, 0x00708, 0x00709, 0x0070A, 0x0070B, 0x0070C, 0x0070D, 0x0070E, 0x0070F, 0x00710, 0x00711, 0x00712,
		0x00713, 0x00714, 0x00715, 0x00716, 0x00717, 0x00718, 0x00719, 0x0071A, 0x0071B, 0x0071C, 0x0071E, 0x0071F,
		0x00723, 0x00725, 0x00726, 0x00737, 0x0074E, 0x00754, 0x0076A, 0x00773, 0x007BB, 0x007D9, 0x007FD, 0x00800,
		0x00801, 0x00802, 0x00803, 0x00804, 0x00805, 0x00806, 0x00807, 0x00808, 0x00809, 0x0080A, 0x0080B, 0x0080C,
		0x0080D, 0x0080E, 0x0080F, 0x00810, 0x00811, 0x00812, 0x00813, 0x00814, 0x00815, 0x00816, 0x00818, 0x00819,
		0x0081B, 0x0081C, 0x0081E, 0x0081F, 0x00825, 0x0082C, 0x00852, 0x00861, 0x00864, 0x00869, 0x0087F, 0x008A1,
		0x008B3, 0x008D0, 0x008D1, 0x008E3, 0x008ED, 0x008F8, 0x008FA, 0x008FC, 0x00902, 0x00903, 0x00904, 0x00905,
		0x00906, 0x00907, 0x00908, 0x00909, 0x0090A, 0x0090B, 0x0090C, 0x0090D, 0x0090E, 0x0090F, 0x00910, 0x00911,
		0x00912, 0x00913, 0x00914, 0x00915, 0x00916, 0x00917, 0x0091A, 0x0091B, 0x0091F, 0x00924, 0x00925, 0x00926,
		0x00929, 0x0092C, 0x00933, 0x0093C, 0x00948, 0x009CA, 0x009E2, 0x00A02, 0x00A03, 0x00A04, 0x00A05, 0x00A06,
		0x00A07, 0x00A08, 0x00A09, 0x00A0A, 0x00A0B, 0x00A0C, 0x00A0D, 0x00A0E, 0x00A0F, 0x00A10, 0x00A11, 0x00A12,
		0x00A13, 0x00A14, 0x00A15, 0x00A16, 0x00A17, 0x00A18, 0x00A19, 0x00A1A, 0x00A1B, 0x00A1C, 0x00A1D, 0x00A1F,
		0x00A21, 0x00A25, 0x00A28, 0x00A2C, 0x00A31, 0x00A6F, 0x00B00, 0x00B03, 0x00B04, 0x00B05, 0x00B06, 0x00B07,
		0x00B08, 0x00B09, 0x00B0A, 0x00B0B, 0x00B0C, 0x00B0D, 0x00B0E, 0x00B0F, 0x00B10, 0x00B11, 0x00B12, 0x00B13,
		0x00B14, 0x00B15, 0x00B16, 0x00B17, 0x00B18, 0x00B19, 0x00B1A, 0x00B1C, 0x00B1D, 0x00B1F, 0x00B22, 0x00B25,
		0x00B27, 0x00B29, 0x00B2D, 0x00B3A, 0x00B5E, 0x00B7A, 0x00BCF, 0x00BE5, 0x00BE9, 0x00C01, 0x00C03, 0x00C04,
		0x00C05, 0x00C06, 0x00C07, 0x00C08, 0x00C09, 0x00C0A, 0x00C0B, 0x00C0C, 0x00C0D, 0x00C0E, 0x00C0F, 0x00C10,
		0x00C11, 0x00C12, 0x00C13, 0x00C14, 0x00C15, 0x00C16, 0x00C17, 0x00C18, 0x00C19, 0x00C1A, 0x00C1E, 0x00C1F,
		0x00C24, 0x00C27, 0x00C30, 0x00C38, 0x00C4B, 0x00C7E, 0x00CA1, 0x00CB4, 0x00CBC, 0x00CC6, 0x00CE9, 0x00D00,
		0x00D02, 0x00D03, 0x00D04, 0x00D05, 0x00D06, 0x00D07, 0x00D08, 0x00D09, 0x00D0A, 0x00D0B, 0x00D0C, 0x00D0D,
		0x00D0E, 0x00D0F, 0x00D10, 0x00D11, 0x00D12, 0x00D13, 0x00D14, 0x00D15, 0x00D16, 0x00D18, 0x00D1A, 0x00D1D,
		0x00D1E, 0x00D1F, 0x00D20, 0x00D34, 0x00DC6, 0x00DD3, 0x00DDE, 0x00DDF, 0x00DE1, 0x00DEB, 0x00DEF, 0x00E00,
		0x00E01, 0x00E02, 0x00E03, 0x00E04, 0x00E05, 0x00E06, 0x00E07, 0x00E08, 0x00E09, 0x00E0A, 0x00E0B, 0x00E0C,
		0x00E0D, 0x00E0E, 0x00E0F, 0x00E10, 0x00E11, 0x00E12, 0x00E13, 0x00E14, 0x00E15, 0x00E17, 0x00E18, 0x00E19,
		0x00E1A, 0x00E1B, 0x00E1C, 0x00E1D, 0x00E1F, 0x00E22, 0x00E24, 0x00E27, 0x00E2B, 0x00E2D, 0x00E2E, 0x00E31,
		0x00E34, 0x00E42, 0x00E48, 0x00E53, 0x00E9E, 0x00ED4, 0x00EDC, 0x00EF1, 0x00F00, 0x00F01, 0x00F02, 0x00F03,
		0x00F04, 0x00F05, 0x00F06, 0x00F07, 0x00F08, 0x00F09, 0x00F0A, 0x00F0B, 0x00F0C, 0x00F0D, 0x00F0E, 0x00F0F,
		0x00F10, 0x00F11, 0x00F12, 0x00F13, 0x00F15, 0x00F16, 0x00F17, 0x00F18, 0x00F19, 0x00F1A, 0x00F1C, 0x00F1E,
		0x00F20, 0x00F21, 0x00F22, 0x00F23, 0x00F25, 0x00F31, 0x00F41, 0x00F45, 0x00F59, 0x00F66, 0x00F82, 0x01053,
		0x0105A, 0x01107, 0x01111, 0x01120, 0x01129, 0x01138, 0x01151, 0x0116C, 0x011BF, 0x011CA, 0x011E4, 0x011EC,
		0x011FB, 0x01202, 0x01222, 0x01232, 0x0123D, 0x0C77E, 0x15FC0, 0x1896D, 0x193A7, 0x19F54, 0x1A1D9, 0x1B112,
		0x1B61F, 0x1BB14, 0x1C589, 0x1C6CA, 0x1C821, 0x1D326, 0x1DC7A, 0x1E235, 0x1EAEF, 0x1EB99, 0x1F20C, 0x1FBFD,
		0x1FCAE, 0x20000, 0x200BE, 0x20767, 0x24514, 0x264A2, 0x30000, 0x359CE, 0x35B58, 0x40000, 0x45351, 0x45363,
		0x45387, 0x453E2, 0x45937, 0x469D4, 0x469F4, 0x46A8B, 0x46D24, 0x46D2A, 0x46D31, 0x46D37, 0x46DB7, 0x46DB9,
		0x46DBC, 0x46DC1, 0x46FA2, 0x47221, 0x4729B, 0x472CF, 0x47313, 0x4754B, 0x4755B, 0x47564, 0x47570, 0x47791,
		0x477D3, 0x47B3F, 0x47B65, 0x47B86, 0x47BBA, 0x47BC3, 0x47C8E, 0x47CC0, 0x47CCB, 0x47CD8, 0x47CFE, 0x47D05,
		0x47D0C, 0x47D12, 0x47D19, 0x47D2E, 0x47D36, 0x47D3E, 0x47D47, 0x47D51, 0x47E86, 0x47E91, 0x47EFA, 0x47F03,
		0x47F5E, 0x47FC6, 0x47FF3, 0x4801A, 0x48027, 0x48031, 0x48038, 0x48072, 0x48079, 0x48084, 0x48085, 0x480AF,
		0x480C4, 0x480CB, 0x480D4, 0x480D8, 0x480E0, 0x480E1, 0x48100, 0x48104, 0x48113, 0x4812A, 0x48169, 0x481C5,
		0x481D1, 0x481D7, 0x481F0, 0x481F7, 0x481F8, 0x48201, 0x4823B, 0x4823E, 0x4823F, 0x48242, 0x48243, 0x48245,
		0x48246, 0x48264, 0x4826A, 0x48272, 0x48284, 0x48287, 0x4828F, 0x48295, 0x4829D, 0x482AB, 0x482AF, 0x482B3,
		0x482CC, 0x482CF, 0x482D0, 0x482D3, 0x482D4, 0x482E1, 0x482FB, 0x4830D, 0x4831C, 0x48320, 0x4832B, 0x4832E,
		0x48332, 0x48337, 0x48372, 0x4837C, 0x4838C, 0x4839E, 0x483A5, 0x483D0, 0x483FC, 0x48408, 0x4840C, 0x4840E,
		0x48410, 0x48413, 0x48416, 0x48419, 0x4841C, 0x4841D, 0x4841F, 0x48433, 0x48441, 0x48452, 0x48499, 0x4849F,
		0x484AE, 0x484C6, 0x484D3, 0x48591, 0x485A2, 0x48669, 0x4866A, 0x48670, 0x48672, 0x4867E, 0x4F143, 0x4F16D,
		0x4F17C, 0x4F1EC, 0x4F200, 0x4F214, 0x4F223, 0x4F233, 0x4F280, 0x4F297, 0x4F2A4, 0x4F2BB, 0x4F2ED, 0x4F2EF,
		0x4F360, 0x4F365, 0x4F38A, 0x4F390, 0x4F396, 0x4F3A1, 0x4F419, 0x4F42A, 0x4F43B, 0x4F45F, 0x4F467, 0x4F487,
		0x4F488, 0x4F4F4, 0x4F50A, 0x4F50B, 0x4F537, 0x4F54D, 0x4F552, 0x4F56A, 0x4F5DD, 0x4F5E1, 0x4F5E4, 0x4F5F7,
		0x4F623, 0x4F630, 0x4F680, 0x4F696, 0x4F6B3, 0x4F6CA, 0x4F6D6, 0x4F6E4, 0x4F70E, 0x4F74E, 0x4F784, 0x4F7D2,
		0x4F7FF, 0x4F80D, 0x4F837, 0x4F83D, 0x4F84D, 0x4F871, 0x4F87A, 0x4F88A, 0x4F8CB, 0x4F8EC, 0x4F8F4, 0x4F92B,
		0x4FA32, 0x4FA3E, 0x4FA5A, 0x4FA66, 0x4FAA4, 0x4FAB5, 0x4FABA, 0x4FAE3, 0x4FAE7, 0x4FB27, 0x4FB2D, 0x4FB8B,
		0x4FBC4, 0x4FBF2, 0x4FBF6, 0x4FC13, 0x4FC17, 0x4FC6B, 0x4FC77, 0x4FCAD, 0x4FCCA, 0x4FCE3, 0x4FCFA, 0x4FD00,
		0x4FD5D, 0x4FD6A, 0x4FD75, 0x4FD7E, 0x4FD93, 0x4FDC4, 0x4FDCF, 0x4FE12, 0x4FE33, 0x4FE48, 0x4FE75, 0x4FECE,
		0x4FF54, 0x4FF87, 0x4FF9C, 0x4FFCF, 0x4FFD2, 0x50000, 0x500CC, 0x50104, 0x5011D, 0x50153, 0x5015C, 0x50165,
		0x5016E, 0x50179, 0x50184, 0x5018C, 0x5019B, 0x501AA, 0x501D6, 0x50249, 0x50251, 0x5035F, 0x5043D, 0x50444,
		0x50463, 0x504EA, 0x504F1, 0x50517, 0x5051D, 0x50544, 0x5054A, 0x50564, 0x5057F, 0x505B5, 0x505FF, 0x5060D,
		0x50625, 0x50636, 0x5064F, 0x50659, 0x5066E, 0x5068B, 0x506A6, 0x506AC, 0x5070D, 0x50730, 0x50764, 0x5078A,
		0x50799, 0x509E3, 0x509FA, 0x50B1A, 0x50B3C, 0x50B6D, 0x50BCA, 0x50C42, 0x50C6F, 0x50CA7, 0x50CD0, 0x50D16,
		0x50D1C, 0x50D38, 0x50DF2, 0x50E3A, 0x50E5D, 0x50E88, 0x50EDD, 0x50EF4, 0x50F14, 0x50FC2, 0x5115B, 0x51178,
		0x51184, 0x51198, 0x511AE, 0x511C0, 0x511C6, 0x51271, 0x51277, 0x51298, 0x512A3, 0x512A6, 0x51337, 0x51364,
		0x51371, 0x51416, 0x5141F, 0x51422, 0x51423, 0x51430, 0x51431, 0x5143E, 0x51458, 0x5148C, 0x514B7, 0x514C2,
		0x514F9, 0x5150A, 0x51526, 0x5153B, 0x51544, 0x51557, 0x51566, 0x51585, 0x5159F, 0x51619, 0x5161E, 0x51632,
		0x51637, 0x5163B, 0x5164D, 0x51650, 0x5165C, 0x5166F, 0x51681, 0x51684, 0x51690, 0x516A4, 0x516AE, 0x516EE,
		0x51718, 0x51726, 0x51727, 0x5175E, 0x51764, 0x51768, 0x51772, 0x51778, 0x5177D, 0x51783, 0x51797, 0x5179C,
		0x517AE, 0x517B8, 0x517BC, 0x517CC, 0x517D9, 0x517E7, 0x517EE, 0x517FB, 0x5186A, 0x51882, 0x51898, 0x518BA,
		0x518C4, 0x518E3, 0x518F8, 0x5191F, 0x51939, 0x51941, 0x5194D, 0x519CC, 0x519FC, 0x51A10, 0x51A34, 0x51A5F,
		0x51A73, 0x51A78, 0x51AA9, 0x51AC7, 0x51AD8, 0x51AEE, 0x51B11, 0x51B23, 0x51B35, 0x51B63, 0x51B75, 0x51B87,
		0x51BD7, 0x51D1D, 0x51D5E, 0x51D83, 0x51D90, 0x51EE4, 0x51EE9, 0x51EEE, 0x51EF3, 0x51EF8, 0x51EFD, 0x51F02,
		0x51F07, 0x51F0C, 0x51F11, 0x51F16, 0x51F1B, 0x51F26, 0x51F2B, 0x51F30, 0x51F32, 0x51F35, 0x51F3A, 0x51F3F,
		0x51F44, 0x51F49, 0x51F4E, 0x51F53, 0x51F58, 0x51F5D, 0x51F64, 0x51F69, 0x51F74, 0x51F77, 0x51FAB, 0x51FCD,
		0x51FDC, 0x52001, 0x52003, 0x5200C, 0x5200E, 0x52089, 0x520F7, 0x5212B, 0x52162, 0x52172, 0x52178, 0x5219E,
		0x521AB, 0x521B3, 0x521B5, 0x521D8, 0x52231, 0x5226E, 0x52280, 0x522A0, 0x522B7, 0x522C9, 0x522D4, 0x522DE,
		0x522E9, 0x522F5, 0x522FC, 0x5231D, 0x52342, 0x5235B, 0x52367, 0x5238B, 0x5239F, 0x523DF, 0x523EB, 0x523ED,
		0x5244F, 0x5245F, 0x52466, 0x52471, 0x52483, 0x52484, 0x524D1, 0x524E0, 0x524F1, 0x524F4, 0x5252F, 0x52531,
		0x52535, 0x5257B, 0x52586, 0x5258D, 0x52594, 0x5259A, 0x525C2, 0x525E8, 0x52626, 0x52645, 0x52656, 0x52668,
		0x52691, 0x526B3, 0x52768, 0x52778, 0x52780, 0x52795, 0x527A5, 0x52802, 0x52828, 0x5285D, 0x528E7, 0x52902,
		0x5294A, 0x52975, 0x529A5, 0x529C9, 0x529CD, 0x52A0A, 0x52A19, 0x52A3D, 0x52A44, 0x52A54, 0x52A7B, 0x52AB6,
		0x52AC3, 0x52AC9, 0x52AD5, 0x52AFD, 0x52B19, 0x52B27, 0x52B37, 0x52B43, 0x52B69, 0x52B7A, 0x52BA0, 0x52BE6,
		0x52BF4, 0x52C0F, 0x52C42, 0x52C4F, 0x52C6A, 0x52C9D, 0x52CAA, 0x52CBD, 0x52CC9, 0x52CD9, 0x52CDB, 0x52CE6,
		0x52CEE, 0x52D0A, 0x52D2B, 0x52D3A, 0x52D45, 0x52D4A, 0x52D52, 0x52D59, 0x52D6B, 0x52DB6, 0x52DE7, 0x52DF4,
		0x52E29, 0x52E58, 0x52E69, 0x52E8A, 0x52ED2, 0x52EE0, 0x52F34, 0x52FC2, 0x52FC6, 0x52FD1, 0x52FD5, 0x52FFE,
		0x5300A, 0x53012, 0x5306B, 0x5307D, 0x53148, 0x5326D, 0x53285, 0x53292, 0x5329A, 0x532AF, 0x532B1, 0x532CA,
		0x532CD, 0x532EA, 0x532FF, 0x53301, 0x53379, 0x5337F, 0x53385, 0x533C3, 0x533DE, 0x53406, 0x53417, 0x5342B,
		0x5344B, 0x5346B, 0x53476, 0x5347D, 0x534A0, 0x534B5, 0x534D7, 0x534E1, 0x534F0, 0x5351A, 0x5352D, 0x53533,
		0x5353D, 0x53548, 0x53569, 0x5358F, 0x53595, 0x535AA, 0x535AF, 0x535C0, 0x535C2, 0x535D3, 0x535DD, 0x535F1,
		0x535F5, 0x53608, 0x5360A, 0x53619, 0x5361E, 0x5362B, 0x53647, 0x53657, 0x53665, 0x53683, 0x5368A, 0x536A4,
		0x536B8, 0x536BD, 0x536DD, 0x536E2, 0x53823, 0x5385F, 0x5389A, 0x538A7, 0x538B3, 0x538BE, 0x538EE, 0x538F8,
		0x53907, 0x5391F, 0x539A1, 0x539E9, 0x53A19, 0x53A72, 0x53AC9, 0x53B17, 0x53B2B, 0x53B41, 0x53B5D, 0x53B96,
		0x53BB5, 0x53BBC, 0x53BBF, 0x53BC6, 0x53BD7, 0x53BE7, 0x53C03, 0x53C15, 0x53C1B, 0x53C1C, 0x53C36, 0x53C38,
		0x53D27, 0x53D44, 0x53D5A, 0x53D6C, 0x53DA4, 0x53DEE, 0x53DF5, 0x53E14, 0x53E4B, 0x53E85, 0x53E98, 0x53EE0,
		0x53F1A, 0x53F62, 0x53F92, 0x53FEB, 0x54042, 0x540E1, 0x54110, 0x5414C, 0x54153, 0x54160, 0x54173, 0x54185,
		0x54198, 0x5419E, 0x541AD, 0x541CB, 0x541D8, 0x541E2, 0x541F6, 0x541FE, 0x54214, 0x54219, 0x5422C, 0x542AA,
		0x542F4, 0x542FB, 0x543B8, 0x543D0, 0x543E2, 0x54400, 0x5443D, 0x54481, 0x544CF, 0x544DE, 0x544E9, 0x544F8,
		0x5450E, 0x54515, 0x5451C, 0x54546, 0x54579, 0x545A1, 0x545B8, 0x545BF, 0x545C8, 0x545CF, 0x545F4, 0x54619,
		0x54667, 0x54714, 0x54759, 0x5476A, 0x54796, 0x547B5, 0x547BD, 0x547CD, 0x547D4, 0x547E5, 0x547ED, 0x547F8,
		0x54802, 0x54825, 0x54838, 0x5483F, 0x54848, 0x5484C, 0x5485F, 0x5486B, 0x5486C, 0x54877, 0x54887, 0x5488B,
		0x548A2, 0x548B7, 0x548FA, 0x5494F, 0x5495C, 0x54999, 0x549BF, 0x549C7, 0x54A02, 0x54A63, 0x54A70, 0x54ADB,
		0x54AF7, 0x54B0C, 0x54BD1, 0x54C14, 0x54C2A, 0x54C45, 0x54C5E, 0x54C79, 0x54C91, 0x54CA8, 0x54CBA, 0x54CBD,
		0x54CD7, 0x54CF6, 0x54D0C, 0x54D1B, 0x54D6B, 0x54DC4, 0x54ED1, 0x54F32, 0x54F44, 0x54F6B, 0x54F99, 0x54FA9,
		0x55008, 0x5500F, 0x55019, 0x5501F, 0x5502E, 0x550C0, 0x550D7, 0x550E2, 0x550E5, 0x5520D, 0x55253, 0x55259,
		0x55267, 0x552A5, 0x552AB, 0x552B4, 0x552B6, 0x552DB, 0x552DE, 0x552F1, 0x5530A, 0x5533F, 0x55353, 0x55354,
		0x55364, 0x55366, 0x553BC, 0x553CA, 0x553E1, 0x553F2, 0x55409, 0x55413, 0x55427, 0x554C4, 0x554C6, 0x554E3,
		0x55526, 0x5552A, 0x55548, 0x55566, 0x5557C, 0x5557E, 0x555A6, 0x555AA, 0x555B5, 0x555F4, 0x555F6, 0x555F8,
		0x55619, 0x5562B, 0x55636, 0x55642, 0x55643, 0x55644, 0x55645, 0x5569E, 0x556A0, 0x556CC, 0x556CF, 0x556D1,
		0x556D4, 0x556DF, 0x556E2, 0x556E9, 0x556EC, 0x556F9, 0x556FC, 0x5571A, 0x5571D, 0x5571F, 0x55722, 0x55724,
		0x55727, 0x55755, 0x55772, 0x55775, 0x55776, 0x55779, 0x55799, 0x5579C, 0x557A2, 0x557A5, 0x557C1, 0x557C4,
		0x557CB, 0x557CE, 0x557DE, 0x557E1, 0x55801, 0x55804, 0x5580A, 0x5580D, 0x55841, 0x55844, 0x55850, 0x55853,
		0x55877, 0x5587A, 0x5587D, 0x558C4, 0x558CA, 0x558CF, 0x558DE, 0x5590A, 0x55912, 0x55916, 0x55919, 0x5595F,
		0x55965, 0x5599B, 0x5599C, 0x559A8, 0x559B3, 0x559B8, 0x559C4, 0x559DD, 0x559EE, 0x559F7, 0x559FE, 0x55A28,
		0x55A2F, 0x55A48, 0x55A51, 0x55A5F, 0x55A7E, 0x55A88, 0x55AA0, 0x55AAC, 0x55ABC, 0x55AD6, 0x55ADD, 0x55AE8,
		0x55AE9, 0x55B3D, 0x55CB3, 0x55D38, 0x55E93, 0x55EF4, 0x55F19, 0x55F34, 0x55F37, 0x55F5B, 0x55FF7, 0x55FFE,
		0x56006, 0x56046, 0x56052, 0x56067, 0x56077, 0x5607B, 0x5607C, 0x56096, 0x560A7, 0x560CD, 0x56119, 0x5612C,
		0x56189, 0x56197, 0x561AA, 0x561E5, 0x561EC, 0x5620A, 0x56261, 0x56268, 0x562A1, 0x562E8, 0x562EE, 0x562F0,
		0x56350, 0x56356, 0x56358, 0x563A6, 0x563A8, 0x563CE, 0x563D4, 0x563D6, 0x563FC, 0x56436, 0x5645D, 0x56482,
		0x56499, 0x564A8, 0x564BD, 0x564C2, 0x564C4, 0x564C7, 0x56500, 0x5650F, 0x56516, 0x56517, 0x56518, 0x5651C,
		0x56521, 0x56523, 0x56525, 0x56527, 0x56531, 0x56533, 0x56535, 0x56536, 0x5653E, 0x56540, 0x56542, 0x56544,
		0x56549, 0x5655A, 0x56567, 0x56576, 0x5657E, 0x56585, 0x56586, 0x56587, 0x56591, 0x565B1, 0x565BF, 0x565D7,
		0x565FA, 0x565FD, 0x5664D, 0x566A1, 0x566A7, 0x566AB, 0x566B3, 0x56747, 0x5675F, 0x56769, 0x5676A, 0x5676C,
		0x56780, 0x5679C, 0x567B7, 0x567BD, 0x567D2, 0x567EA, 0x56833, 0x5686F, 0x56870, 0x56877, 0x5687C, 0x56888,
		0x5688F, 0x56894, 0x568AA, 0x568B6, 0x568E9, 0x568EC, 0x568FD, 0x56914, 0x5691A, 0x56930, 0x56946, 0x5696C,
		0x56970, 0x56975, 0x56979, 0x56986, 0x5698A, 0x5698D, 0x569A4, 0x569A7, 0x569BE, 0x569C1, 0x569C9, 0x569D1,
		0x569D8, 0x569DB, 0x569F2, 0x569F5, 0x569FB, 0x569FC, 0x56A04, 0x56A0C, 0x56A0F, 0x56A26, 0x56A29, 0x56A40,
		0x56A43, 0x56A4B, 0x56A4F, 0x56A57, 0x56A5A, 0x56A5D, 0x56A6A, 0x56A74, 0x56A82, 0x56A84, 0x56A8A, 0x56A9E,
		0x56AB8, 0x56AD2, 0x56AEC, 0x56B01, 0x56B06, 0x56B11, 0x56B14, 0x56B20, 0x56B3A, 0x56B49, 0x56B7D, 0x56B8D,
		0x56B90, 0x56C47, 0x56C4A, 0x56C69, 0x56C6C, 0x56C81, 0x56C84, 0x56DAE, 0x56E4B, 0x56E55, 0x56E5B, 0x56E72,
		0x56E89, 0x56E9C, 0x56EA6, 0x56EAC, 0x56EC8, 0x56F2E, 0x56F34, 0x56F39, 0x56F3A, 0x56F4B, 0x56F6B, 0x56F7F,
		0x56F85, 0x56F91, 0x56FA3, 0x56FA6, 0x56FA9, 0x56FAF, 0x56FB4, 0x56FB7, 0x56FBA, 0x56FC0, 0x56FC6, 0x56FDE,
		0x56FE8, 0x56FEB, 0x56FF1, 0x56FF4, 0x56FFA, 0x57009, 0x5700A, 0x5700F, 0x57014, 0x57017, 0x5701D, 0x57026,
		0x57028, 0x57041, 0x57054, 0x57057, 0x5705A, 0x57060, 0x57080, 0x57083, 0x5708D, 0x5709A, 0x5709D, 0x570C0,
		0x570C3, 0x570D0, 0x570E0, 0x570E7, 0x570EC, 0x570EF, 0x57102, 0x57106, 0x57128, 0x57138, 0x5714B, 0x5714E,
		0x57168, 0x57175, 0x57177, 0x5717A, 0x57183, 0x571B6, 0x571BA, 0x571D4, 0x571D5, 0x571DC, 0x57226, 0x57227,
		0x5722B, 0x5723B, 0x5723D, 0x57252, 0x57259, 0x57267, 0x57271, 0x57278, 0x57279, 0x57282, 0x5728B, 0x5728C,
		0x57295, 0x5729A, 0x5729D, 0x572C4, 0x572D9, 0x572E7, 0x572EF, 0x572F1, 0x572F5, 0x572FA, 0x572FD, 0x57303,
		0x57309, 0x5730D, 0x5730F, 0x57315, 0x5731B, 0x5731C, 0x5731F, 0x57321, 0x57322, 0x57323, 0x57326, 0x57327,
		0x5732A, 0x57331, 0x57339, 0x57391, 0x573A4, 0x573A8, 0x573AD, 0x573AE, 0x573B3, 0x573B5, 0x573B6, 0x573B7,
		0x573C8, 0x573D8, 0x573DA, 0x573DF, 0x573EC, 0x573EE, 0x573F3, 0x573FA, 0x57400, 0x57406, 0x5740A, 0x5740F,
		0x57413, 0x57418, 0x5741A, 0x5741C, 0x5741E, 0x5741F, 0x5742B, 0x5742F, 0x57433, 0x5743A, 0x57443, 0x57453,
		0x5746B, 0x57471, 0x5747F, 0x57481, 0x5748D, 0x57497, 0x574A7, 0x574AD, 0x574B6, 0x574B7, 0x574CC, 0x574CE,
		0x574D0, 0x574D6, 0x574E7, 0x574F1, 0x574F3, 0x574F8, 0x574FD, 0x57503, 0x57505, 0x57507, 0x57509, 0x5750C,
		0x57519, 0x5751F, 0x57523, 0x57529, 0x5752F, 0x57533, 0x57535, 0x57538, 0x5753C, 0x57540, 0x57544, 0x57549,
		0x5754B, 0x57558, 0x5756B, 0x5756C, 0x57587, 0x5758A, 0x5758E, 0x575A0, 0x575A2, 0x575A6, 0x575B7, 0x575B8,
		0x575BE, 0x575C7, 0x575C8, 0x575D3, 0x575ED, 0x575EF, 0x575F1, 0x575FB, 0x5760A, 0x57612, 0x57614, 0x57619,
		0x5761A, 0x5762A, 0x57638, 0x5763B, 0x57648, 0x57654, 0x57656, 0x57659, 0x57667, 0x57671, 0x5768C, 0x5768F,
		0x57699, 0x5769B, 0x576A5, 0x576B1, 0x576D1, 0x576F0, 0x576F9, 0x5771F, 0x57733, 0x57755, 0x57768, 0x57769,
		0x5776B, 0x57774, 0x5777E, 0x5778A, 0x577C7, 0x577CB, 0x577CF, 0x577E7, 0x577EC, 0x577EF, 0x577F2, 0x577FA,
		0x577FD, 0x57804, 0x57807, 0x5780C, 0x5780E, 0x57811, 0x57818, 0x5781B, 0x57822, 0x57825, 0x57829, 0x5782C,
		0x57835, 0x57838, 0x5783E, 0x5783F, 0x57842, 0x57843, 0x5784D, 0x57850, 0x57854, 0x57857, 0x5785A, 0x57861,
		0x57864, 0x5786B, 0x5786E, 0x57875, 0x57878, 0x57879, 0x5787E, 0x5788B, 0x57896, 0x578A2, 0x578A6, 0x578A7,
		0x578A9, 0x578AD, 0x578D1, 0x578D4, 0x578E2, 0x578E5, 0x578F4, 0x578F7, 0x578F8, 0x578F9, 0x578FB, 0x578FF,
		0x5791D, 0x5792A, 0x5792E, 0x57931, 0x57932, 0x5793A, 0x57944, 0x57945, 0x57947, 0x5794B, 0x5797A, 0x5797D,
		0x57980, 0x57983, 0x57996, 0x57997, 0x57999, 0x5799D, 0x579CC, 0x579CF, 0x579D2, 0x579D5, 0x579D8, 0x579DB,
		0x579EE, 0x579F0, 0x579F2, 0x579F3, 0x579F4, 0x579F8, 0x579FF, 0x57A01, 0x57A27, 0x57A2A, 0x57A59, 0x57A5C,
		0x57A83, 0x57A86, 0x57A9B, 0x57A9D, 0x57A9F, 0x57AA1, 0x57AA5, 0x57AD4, 0x57AD7, 0x57B06, 0x57B09, 0x57B30,
		0x57B33, 0x57B48, 0x57B4A, 0x57B4C, 0x57B4E, 0x57B52, 0x57B7A, 0x57B7D, 0x57BA4, 0x57BA7, 0x57BC6, 0x57BC9,
		0x57C45, 0x57C56, 0x57C7A, 0x57C86, 0x57C9E, 0x57CB5, 0x57CC6, 0x57CCC, 0x57CE8, 0x57CF2, 0x57CF7, 0x57D00,
		0x57D0C, 0x57D0F, 0x57D15, 0x57D17, 0x57D29, 0x57D3A, 0x57D3C, 0x57D3E, 0x57D45, 0x57D70, 0x57D81, 0x57D91,
		0x57D94, 0x57D9C, 0x57D9F, 0x57DA4, 0x57DBB, 0x57DBC, 0x57DCB, 0x57DE5, 0x57DE6, 0x57DEA, 0x57DED, 0x57DF6,
		0x57E18, 0x57E30, 0x57E3B, 0x57E4F, 0x57E95, 0x57EA2, 0x57F48, 0x57FBE, 0x57FDB, 0x57FDD, 0x58024, 0x58026,
		0x58031, 0x58052, 0x5806E, 0x58090, 0x580EC, 0x58101, 0x58116, 0x58120, 0x58122, 0x58130, 0x58134, 0x58136,
		0x58139, 0x581C2, 0x581E3, 0x581E6, 0x58240, 0x58246, 0x58261, 0x5826A, 0x5827A, 0x5828E, 0x58297, 0x582C1,
		0x58317, 0x58573, 0x58747, 0x58761, 0x58843, 0x58A70, 0x58A88, 0x58AB2, 0x58B20, 0x58B2D, 0x58B8A, 0x58B95,
		0x58BA5, 0x58BBA, 0x58C31, 0x58E45, 0x58F17, 0x58F20, 0x58F31, 0x58F3E, 0x58F86, 0x58FA4, 0x58FB2, 0x58FC5,
		0x58FCE, 0x58FDD, 0x59007, 0x5903D, 0x59075, 0x5907A, 0x59082, 0x5908A, 0x5908C, 0x590D5, 0x590DF, 0x590E2,
		0x590E4, 0x590EA, 0x590FA, 0x59131, 0x59140, 0x59142, 0x59157, 0x59186, 0x5918F, 0x591B1, 0x591E9, 0x5922D,
		0x5923E, 0x59240, 0x5929C, 0x5929E, 0x592A7, 0x592AB, 0x592B0, 0x592B6, 0x592B8, 0x592E3, 0x59311, 0x59333,
		0x5934C, 0x5937A, 0x59404, 0x59406, 0x59437, 0x59474, 0x59476, 0x594BC, 0x594BE, 0x594FD, 0x5958C, 0x5958E,
		0x595B6, 0x595EC, 0x595F4, 0x59602, 0x59604, 0x59648, 0x5964A, 0x596B2, 0x59726, 0x59864, 0x598EA, 0x599FB,
		0x59B9F, 0x59BCE, 0x59D7E, 0x59FAB, 0x5A7B3, 0x5A7C1, 0x5A7E4, 0x5A809, 0x5A84D, 0x5A855, 0x5A863, 0x5A8DB,
		0x5A8EF, 0x5A8F7, 0x5A905, 0x5A944, 0x5A97D, 0x5A991, 0x5A9F8, 0x5AA35, 0x5ACA9, 0x5ACC6, 0x5ACED, 0x5AD07,
		0x5AD20, 0x5AD21, 0x5AD35, 0x5AD3F, 0x5AD49, 0x5AD54, 0x5AD5E, 0x5AD68, 0x5AD7A, 0x5AD8C, 0x5ADBC, 0x5ADCB,
		0x5ADD1, 0x5ADD9, 0x5ADED, 0x5ADEF, 0x5ADF0, 0x5ADF7, 0x5ADFF, 0x5AE0B, 0x5AE26, 0x5AF6D, 0x5AF7A, 0x5B006,
		0x5B010, 0x5B02B, 0x5B039, 0x5B078, 0x5B084, 0x5B086, 0x5B0C4, 0x5B0C6, 0x5B0F9, 0x5B12D, 0x5B138, 0x5B13A,
		0x5B13D, 0x5B144, 0x5B14F, 0x5B169, 0x5B17F, 0x5B189, 0x5B18A, 0x5B18C, 0x5B1B1, 0x5B1BE, 0x5B1C9, 0x5B1D0,
		0x5B1D6, 0x5B1D8, 0x5B1F8, 0x5B202, 0x5B20E, 0x5B225, 0x5B22E, 0x5B230, 0x5B233, 0x5B23D, 0x5B264, 0x5B26C,
		0x5B26E, 0x5B278, 0x5B27A, 0x5B286, 0x5B28C, 0x5B28E, 0x5B2D5, 0x5B35B, 0x5B368, 0x5B36A, 0x5B3DA, 0x5B41C,
		0x5B47D, 0x5B4CD, 0x5B4D8, 0x5B4DA, 0x5B4E5, 0x5B502, 0x5B508, 0x5B52A, 0x5B52C, 0x5B56E, 0x5B570, 0x5B5B5,
		0x5B5C0, 0x5B5CE, 0x5B5CF, 0x5B5E0, 0x5B5E2, 0x5B5EA, 0x5B5F0, 0x5B629, 0x5B62E, 0x5B632, 0x5B634, 0x5B66C,
		0x5B67A, 0x5B67E, 0x5B680, 0x5B697, 0x5B6A2, 0x5B6A4, 0x5B708, 0x5B716, 0x5B718, 0x5B750, 0x5B752, 0x5B76C,
		0x5B7A1, 0x5B7C7, 0x5B7D6, 0x5B7D8, 0x5BB69, 0x5BB8C, 0x5BCC7, 0x5BCCD, 0x5BCF5, 0x5BD1F, 0x5BD28, 0x5BD2E,
		0x5BD34, 0x5BD3D, 0x5BD77, 0x5C163, 0x5C195, 0x5C1A2, 0x5C1B1, 0x5C1BB, 0x5C1F0, 0x5C220, 0x5C222, 0x5C234,
		0x5C257, 0x5C289, 0x5C28F, 0x5C294, 0x5C296, 0x5C2A9, 0x5C2AF, 0x5C2C0, 0x5C2C2, 0x5C2EE, 0x5C2F0, 0x5C354,
		0x5C356, 0x5C39C, 0x5C39E, 0x5C3B1, 0x5C3C9, 0x5C3D6, 0x5C3D8, 0x5C3EA, 0x5C42C, 0x5C435, 0x5C454, 0x5C465,
		0x5C467, 0x5C46B, 0x5C47B, 0x5C4D4, 0x5C4D6, 0x5C4F6, 0x5C506, 0x5C511, 0x5C51B, 0x5C526, 0x5C52A, 0x5C52C,
		0x5C530, 0x5C549, 0x5C595, 0x5C59A, 0x5C5F6, 0x5C5F8, 0x5C645, 0x5C65A, 0x5C65C, 0x5C68F, 0x5C691, 0x5C698,
		0x5C69A, 0x5C6A1, 0x5C6A8, 0x5C6AA, 0x5C6AB, 0x5C6AD, 0x5C6B4, 0x5C6B9, 0x5C6BA, 0x5C6BC, 0x5C6C0, 0x5C6C5,
		0x5C6C9, 0x5C6CC, 0x5C6CF, 0x5C6D6, 0x5C6D8, 0x5C6D9, 0x5C6E2, 0x5C6E7, 0x5C6EA, 0x5C6EE, 0x5C6F3, 0x5C6F7,
		0x5C6FA, 0x5C701, 0x5C703, 0x5C70F, 0x5C711, 0x5C7F4, 0x5C854, 0x5C85B, 0x5C9D7, 0x5C9DA, 0x5C9E8, 0x5CBFB,
		0x5CC54, 0x5CC5F, 0x5CC60, 0x5CC80, 0x5CD69, 0x5CD88, 0x5CDA9, 0x5CDC8, 0x5CDE3, 0x5CE05, 0x5CE21, 0x5CE41,
		0x5CE67, 0x5CEF4, 0x5CEF5, 0x5CF30, 0x5CF48, 0x5CF5D, 0x5CF9F, 0x5CFA8, 0x5CFDB, 0x5CFDE, 0x5CFE6, 0x5D009,
		0x5D016, 0x5D018, 0x5D01A, 0x5D01D, 0x5D02E, 0x5D043, 0x5D050, 0x5D099, 0x5D0BB, 0x5D0C3, 0x5D0C8, 0x5D0CF,
		0x5D10D, 0x5D120, 0x5D124, 0x5D130, 0x5D135, 0x5D140, 0x5D146, 0x5D14D, 0x5D193, 0x5D19C, 0x5D1AD, 0x5D1BE,
		0x5D1C6, 0x5D1D0, 0x5D1DA, 0x5D1E4, 0x5D1EE, 0x5D1F8, 0x5D202, 0x5D20C, 0x5D20F, 0x5D216, 0x5D262, 0x5D280,
		0x5D283, 0x5D28D, 0x5D29A, 0x5D29D, 0x5D2B4, 0x5D2B7, 0x5D2CE, 0x5D2D1, 0x5D2E8, 0x5D2EB, 0x5D302, 0x5D305,
		0x5D31C, 0x5D31F, 0x5D336, 0x5D339, 0x5D341, 0x5D350, 0x5D353, 0x5D360, 0x5D36A, 0x5D37A, 0x5D394, 0x5D3A5,
		0x5D3AE, 0x5D3BE, 0x5D3C1, 0x5D3C8, 0x5D3D3, 0x5D3D6, 0x5D3D8, 0x5D3E2, 0x5D3E8, 0x5D3EB, 0x5D3ED, 0x5D3FC,
		0x5D3FD, 0x5D400, 0x5D402, 0x5D412, 0x5D415, 0x5D416, 0x5D417, 0x5D427, 0x5D42A, 0x5D42C, 0x5D430, 0x5D43C,
		0x5D43F, 0x5D441, 0x5D451, 0x5D454, 0x5D456, 0x5D466, 0x5D469, 0x5D46B, 0x5D47F, 0x5D480, 0x5D4F1, 0x5D506,
		0x5D51B, 0x5D530, 0x5D535, 0x5D545, 0x5D54D, 0x5D553, 0x5D55A, 0x5D56F, 0x5D584, 0x5D599, 0x5D5CF, 0x5D5D1,
		0x5D5D9, 0x5D5E5, 0x5D5EF, 0x5D5F1, 0x5D5FD, 0x5D604, 0x5D616, 0x5D62F, 0x5D649, 0x5D64C, 0x5D660, 0x5D680,
		0x5D686, 0x5D693, 0x5D6AC, 0x5D6DE, 0x5D6DF, 0x5D6E1, 0x5D6ED, 0x5D6EF, 0x5D723, 0x5D72A, 0x5D72F, 0x5D732,
		0x5D739, 0x5D73A, 0x5D75C, 0x5D75F, 0x5D765, 0x5D766, 0x5D767, 0x5D76B, 0x5D76D, 0x5D772, 0x5D778, 0x5D77A,
		0x5D782, 0x5D79E, 0x5D7A2, 0x5D7A5, 0x5D7AA, 0x5D7BB, 0x5D7C3, 0x5D7E1, 0x5D7E4, 0x5D7E7, 0x5D7EE, 0x5D7F6,
		0x5D81D, 0x5D829, 0x5D860, 0x5D88F, 0x5D8B1, 0x5D8B6, 0x5D8BD, 0x5D8F4, 0x5D923, 0x5D945, 0x5D94A, 0x5D951,
		0x5D981, 0x5D9A8, 0x5D9C2, 0x5D9C7, 0x5D9CE, 0x5D9E1, 0x5D9EC, 0x5D9EE, 0x5D9FF, 0x5DA24, 0x5DA2F, 0x5DA31,
		0x5DA33, 0x5DA42, 0x5DA5A, 0x5DA6E, 0x5DA7A, 0x5DA90, 0x5DA9C, 0x5DA9E, 0x5DAA2, 0x5DAE5, 0x5DB4B, 0x5DB57,
		0x5DB7C, 0x5DB7F, 0x5DB97, 0x5DBAE, 0x5DBB2, 0x5DBB3, 0x5DBB7, 0x5DBCD, 0x5DBE4, 0x5DBF0, 0x5DBF6, 0x5DC0B,
		0x5DC28, 0x5DC56, 0x5DC5D, 0x5DC75, 0x5DCB0, 0x5DD0B, 0x5DD94, 0x5DDA1, 0x5DDA3, 0x5DDA6, 0x5DDB0, 0x5DDB3,
		0x5DDDC, 0x5DDDF, 0x5DDE1, 0x5DE0E, 0x5DE11, 0x5DE20, 0x5DE23, 0x5DE32, 0x5DE35, 0x5DE58, 0x5DE5B, 0x5DE6A,
		0x5DE6D, 0x5DE71, 0x5DE76, 0x5DE9C, 0x5DE9F, 0x5DEAE, 0x5DEB1, 0x5DEB7, 0x5DEBA, 0x5DEBD, 0x5DEC0, 0x5DEC3,
		0x5DEFF, 0x5DF02, 0x5DF74, 0x5DF77, 0x5E072, 0x5E083, 0x5E091, 0x5E094, 0x5E099, 0x5E09B, 0x5E09F, 0x5E0A2,
		0x5E0A9, 0x5E0AA, 0x5E0AC, 0x5E0B3, 0x5E0B6, 0x5E0BD, 0x5E0C0, 0x5E0C7, 0x5E0CA, 0x5E0DD, 0x5E0E3, 0x5E0E4,
		0x5E0E7, 0x5E0F2, 0x5E0F5, 0x5E0FC, 0x5E0FF, 0x5E106, 0x5E109, 0x5E110, 0x5E113, 0x5E11A, 0x5E11D, 0x5E120,
		0x5E12E, 0x5E130, 0x5E13F, 0x5E155, 0x5E159, 0x5E166, 0x5E16A, 0x5E171, 0x5E174, 0x5E17E, 0x5E180, 0x5E185,
		0x5E186, 0x5E18F, 0x5E191, 0x5E195, 0x5E197, 0x5E1A4, 0x5E1A9, 0x5E1AA, 0x5E1AD, 0x5E1AE, 0x5E1B5, 0x5E1BD,
		0x5E1BF, 0x5E1C2, 0x5E1C7, 0x5E1CB, 0x5E1CE, 0x5E1D1, 0x5E1D3, 0x5E1D4, 0x5E1D8, 0x5E1EF, 0x5E1F7, 0x5E200,
		0x5E208, 0x5E21A, 0x5E227, 0x5E22E, 0x5E232, 0x5E234, 0x5E23C, 0x5E241, 0x5E244, 0x5E245, 0x5E246, 0x5E24F,
		0x5E252, 0x5E256, 0x5E257, 0x5E258, 0x5E25B, 0x5E25E, 0x5E260, 0x5E261, 0x5E2D0, 0x5E2D9, 0x5E2E3, 0x5E2E9,
		0x5E300, 0x5E324, 0x5E327, 0x5E32A, 0x5E332, 0x5E334, 0x5E335, 0x5E33A, 0x5E343, 0x5E348, 0x5E34B, 0x5E354,
		0x5E356, 0x5E358, 0x5E359, 0x5E362, 0x5E365, 0x5E373, 0x5E374, 0x5E377, 0x5E384, 0x5E386, 0x5E3AF, 0x5E3C7,
		0x5E3C8, 0x5E3CE, 0x5E3D4, 0x5E3EB, 0x5E3F9, 0x5E415, 0x5E41F, 0x5E425, 0x5E441, 0x5E442, 0x5E454, 0x5E469,
		0x5E46C, 0x5E476, 0x5E479, 0x5E47F, 0x5E498, 0x5E4A2, 0x5E4A5, 0x5E4A7, 0x5E4AB, 0x5E4AD, 0x5E4B2, 0x5E4B3,
		0x5E4C4, 0x5E4E4, 0x5E4F8, 0x5E4FE, 0x5E50A, 0x5E51C, 0x5E51F, 0x5E522, 0x5E528, 0x5E52D, 0x5E539, 0x5E53D,
		0x5E53F, 0x5E540, 0x5E545, 0x5E557, 0x5E561, 0x5E564, 0x5E56A, 0x5E56D, 0x5E573, 0x5E583, 0x5E58D, 0x5E58F,
		0x5E590, 0x5E595, 0x5E596, 0x5E5A1, 0x5E5AC, 0x5E5CD, 0x5E5D0, 0x5E5E0, 0x5E5E6, 0x5E5F9, 0x5E5FC, 0x5E605,
		0x5E606, 0x5E60A, 0x5E60F, 0x5E613, 0x5E616, 0x5E62B, 0x5E631, 0x5E637, 0x5E639, 0x5E63A, 0x5E63B, 0x5E63C,
		0x5E63E, 0x5E63F, 0x5E644, 0x5E648, 0x5E665, 0x5E668, 0x5E67B, 0x5E67F, 0x5E6B2, 0x5E6C0, 0x5E6C9, 0x5E6CA,
		0x5E6CC, 0x5E6D1, 0x5E6D4, 0x5E6D7, 0x5E6E2, 0x5E6E4, 0x5E6E6, 0x5E6EB, 0x5E6EE, 0x5E6FB, 0x5E6FD, 0x5E700,
		0x5E716, 0x5E727, 0x5E72B, 0x5E72C, 0x5E72F, 0x5E731, 0x5E734, 0x5E736, 0x5E738, 0x5E73E, 0x5E745, 0x5E74B,
		0x5E763, 0x5E769, 0x5E776, 0x5E78C, 0x5E78E, 0x5E794, 0x5E79D, 0x5E79E, 0x5E7A5, 0x5E7B3, 0x5E7BC, 0x5E7C3,
		0x5E7CC, 0x5E7CF, 0x5E7D5, 0x5E7D8, 0x5E7F8, 0x5E7FA, 0x5E801, 0x5E802, 0x5E819, 0x5E822, 0x5E824, 0x5E825,
		0x5E826, 0x5E83F, 0x5E84B, 0x5E84E, 0x5E867, 0x5E86C, 0x5E86F, 0x5E871, 0x5E874, 0x5E87E, 0x5E88B, 0x5E89B,
		0x5E8A1, 0x5E8AE, 0x5E8CA, 0x5E8D4, 0x5E8D5, 0x5E8DE, 0x5E8EB, 0x5E900, 0x5E903, 0x5E914, 0x5E918, 0x5E930,
		0x5E939, 0x5E93A, 0x5E942, 0x5E955, 0x5E965, 0x5E96A, 0x5E96C, 0x5E96E, 0x5E983, 0x5E986, 0x5E993, 0x5E9AB,
		0x5E9AF, 0x5E9C0, 0x5E9C3, 0x5E9C6, 0x5E9C7, 0x5E9D3, 0x5EA0D, 0x5EA1C, 0x5EA23, 0x5EA31, 0x5EA33, 0x5EA43,
		0x5EA91, 0x5EAA5, 0x5EAB8, 0x5EAC7, 0x5EAD2, 0x5EAD4, 0x5EADB, 0x5EB07, 0x5EB0F, 0x5EB12, 0x5EB20, 0x5EB34,
		0x5EB38, 0x5EB58, 0x5EB74, 0x5EB9F, 0x5EBE2, 0x5EC03, 0x5EC13, 0x5EC1A, 0x5EC59, 0x5EC5B, 0x5EC60, 0x5EC6B,
		0x5ECB6, 0x5ECE9, 0x5ECED, 0x5ED07, 0x5ED08, 0x5ED0F, 0x5ED59, 0x5ED5A, 0x5ED5E, 0x5ED6E, 0x5ED70, 0x5ED85,
		0x5ED8C, 0x5ED9A, 0x5EDA4, 0x5EDAB, 0x5EDAC, 0x5EDB5, 0x5EDBE, 0x5EDBF, 0x5EDC8, 0x5EDCD, 0x5EDD0, 0x5EE0C,
		0x5EE1A, 0x5EE28, 0x5EE2D, 0x5EE30, 0x5EE36, 0x5EE48, 0x5EE4F, 0x5EE56, 0x5EE5A, 0x5EE6C, 0x5EEBE, 0x5EEC4,
		0x5EED8, 0x5EEDB, 0x5EEE5, 0x5EEE9, 0x5EEEB, 0x5EEFA, 0x5EEFB, 0x5EF07, 0x5EF41, 0x5EF66, 0x5EF88, 0x5EF93,
		0x5EFA0, 0x5EFDF, 0x5F008, 0x5F01C, 0x5F023, 0x5F02A, 0x5F02F, 0x5F034, 0x5F038, 0x5F03C, 0x5F071, 0x5F07D,
		0x5F086, 0x5F09C, 0x5F0A5, 0x5F0C7, 0x5F0C9, 0x5F0CA, 0x5F0CB, 0x5F0D3, 0x5F0D4, 0x5F0DA, 0x5F0E1, 0x5F0EE,
		0x5F0F5, 0x5F103, 0x5F10A, 0x5F117, 0x5F11E, 0x5F131, 0x5F134, 0x5F13B, 0x5F13D, 0x5F13F, 0x5F141, 0x5F143,
		0x5F14D, 0x5F15C, 0x5F15F, 0x5F162, 0x5F16C, 0x5F17B, 0x5F17E, 0x5F195, 0x5F19B, 0x5F19D, 0x5F1A0, 0x5F1A2,
		0x5F1F0, 0x5F200, 0x5F207, 0x5F25B, 0x5F2AB, 0x5F321, 0x5F336, 0x5F360, 0x5F364, 0x5F37B, 0x5F399, 0x5F3B4,
		0x5F404, 0x5F407, 0x5F41E, 0x5F42E, 0x5F439, 0x5F481, 0x5F4D3, 0x5F51D, 0x5F521, 0x5F524, 0x5F530, 0x5F533,
		0x5F537, 0x5F539, 0x5F53E, 0x5F562, 0x5F573, 0x5F581, 0x5F596, 0x5F5E7, 0x5F5FE, 0x5F613, 0x5F632, 0x5F635,
		0x5F640, 0x5F642, 0x5F6C5, 0x5F717, 0x5F72E, 0x5F74A, 0x5F74F, 0x5F7FE, 0x5F801, 0x5F85E, 0x5FA2A, 0x5FBC5,
		0x5FBDE, 0x5FC19, 0x5FC1C, 0x5FC2A, 0x5FC2F, 0x5FCA1, 0x5FCA2, 0x5FCFE, 0x61957, 0x619CF, 0x619D5, 0x61AE1,
		0x61B0C, 0x61B86, 0x61BA9, 0x61D08, 0x61D20, 0x6205F, 0x62063, 0x62066, 0x620B0, 0x620C0, 0x620F0, 0x62112,
		0x62118, 0x62195, 0x62199, 0x621BE, 0x621CC, 0x6220B, 0x6220D, 0x6220F, 0x62213, 0x62215, 0x62410, 0x6241D,
		0x6250A, 0x62545, 0x625C8, 0x62642, 0x626C8, 0x62B35, 0x62B4C, 0x62B63, 0x62B65, 0x62B67, 0x62B68, 0x62B69,
		0x62B6B, 0x62BC0, 0x62BC2, 0x62BCA, 0x62BCE, 0x62BE3, 0x62BE5, 0x62BF0, 0x62BF2, 0x62BFC, 0x62C3B, 0x62C40,
		0x62C45, 0x62C60, 0x62C67, 0x62C6D, 0x62C6E, 0x62C75, 0x62C7C, 0x62C8C, 0x62CAD, 0x62CAF, 0x62CB0, 0x62CB6,
		0x62CB7, 0x62CBD, 0x62CBE, 0x62CC4, 0x62CCA, 0x62CD1, 0x62CD7, 0x62CDE, 0x62CE1, 0x62CFD, 0x62D01, 0x62D05,
		0x62D0F, 0x62D12, 0x62D20, 0x62D45, 0x62D52, 0x62D63, 0x62D6C, 0x62D70, 0x62D7E, 0x62D83, 0x62D86, 0x62D89,
		0x62D8B, 0x62D8D, 0x62D95, 0x62D97, 0x62D9A, 0x62D9C, 0x62DC0, 0x62DC6, 0x62DCD, 0x62DE6, 0x62E1B, 0x62E27,
		0x62E3E, 0x62E44, 0x62E45, 0x62EED, 0x62EF9, 0x62F6F, 0x6301F, 0x6302E, 0x6308E, 0x63093, 0x631A6, 0x6320C,
		0x63211, 0x63290, 0x632A0, 0x632D4, 0x63313, 0x63314, 0x63316, 0x63324, 0x6332E, 0x63333, 0x63410, 0x63413,
		0x63519, 0x635F6, 0x635FD, 0x6365F, 0x63C4F, 0x63C63, 0x63C94, 0x63DD0, 0x63EE6, 0x63F06, 0x63FE9, 0x6425A,
		0x6433C, 0x643C0, 0x643DC, 0x6448C, 0x6448F, 0x6455E, 0x64571, 0x6465B, 0x64702, 0x6470E, 0x647BD, 0x647BF,
		0x648E6, 0x649C4, 0x649E7, 0x64A11, 0x64B3C, 0x64BFA, 0x64C10, 0x64C34, 0x64C53, 0x64D54, 0x64D82, 0x64D8A,
		0x64DBC, 0x64DD9, 0x64DF0, 0x64DFD, 0x64E45, 0x64E50, 0x64EA4, 0x64ED2, 0x64ED4, 0x64EE2, 0x64F01, 0x64F0B,
		0x64F22, 0x64F5B, 0x64F5D, 0x64F78, 0x64FB0, 0x64FC1, 0x64FFD, 0x65001, 0x6503C, 0x6503E, 0x65051, 0x65053,
		0x65066, 0x65068, 0x6506F, 0x65072, 0x6508B, 0x6508E, 0x650A0, 0x650B9, 0x650BA, 0x650BC, 0x650BD, 0x650BE,
		0x650C0, 0x650D3, 0x650DB, 0x650DE, 0x650E1, 0x650E9, 0x650EA, 0x6510F, 0x65113, 0x65116, 0x6514E, 0x65151,
		0x65158, 0x6516E, 0x65185, 0x65189, 0x651AE, 0x651B5, 0x651D5, 0x651DF, 0x651E8, 0x65205, 0x6520F, 0x65211,
		0x65227, 0x65229, 0x65237, 0x6525D, 0x65261, 0x65270, 0x65280, 0x6528F, 0x652A4, 0x652BA, 0x652BF, 0x652DB,
		0x652DF, 0x652E9, 0x652EA, 0x65314, 0x65326, 0x65337, 0x6533B, 0x6534B, 0x65354, 0x65360, 0x65375, 0x65376,
		0x6537A, 0x6537C, 0x65386, 0x653A3, 0x653AE, 0x653DB, 0x653DD, 0x653E3, 0x653E7, 0x6541B, 0x65436, 0x6543B,
		0x65445, 0x6544A, 0x6544C, 0x6545E, 0x65460, 0x65463, 0x6547E, 0x6548F, 0x65490, 0x6549D, 0x654A8, 0x654B9,
		0x654C6, 0x654DF, 0x654E0, 0x654EB, 0x654FC, 0x65501, 0x65527, 0x6552C, 0x65534, 0x65538, 0x6553B, 0x6553D,
		0x65561, 0x65564, 0x65566, 0x6557F, 0x65586, 0x65589, 0x65590, 0x65593, 0x655AA, 0x655C4, 0x655CF, 0x655E0,
		0x655EE, 0x655F0, 0x655F8, 0x655F9, 0x65607, 0x65616, 0x65617, 0x65628, 0x65636, 0x6563A, 0x6564E, 0x6565A,
		0x65661, 0x65667, 0x6567A, 0x6567B, 0x65682, 0x65683, 0x65685, 0x65689, 0x6568A, 0x6568D, 0x65694, 0x656D5,
		0x656D6, 0x656D8, 0x656E2, 0x656EC, 0x65702, 0x65704, 0x6570C, 0x65711, 0x65713, 0x6572D, 0x6574A, 0x65752,
		0x65754, 0x65756, 0x65758, 0x6575C, 0x65765, 0x65769, 0x6577E, 0x65780, 0x65782, 0x65788, 0x6578F, 0x65797,
		0x657A8, 0x657C5, 0x657C6, 0x657CF, 0x657D1, 0x657D2, 0x657DE, 0x657EB, 0x657F9, 0x657FA, 0x65800, 0x65832,
		0x6583D, 0x6585E, 0x65861, 0x65884, 0x658B1, 0x658B6, 0x658B7, 0x658BA, 0x658BF, 0x658CD, 0x65902, 0x65905,
		0x65945, 0x65960, 0x6597C, 0x65980, 0x65990, 0x659DF, 0x659E1, 0x659E3, 0x659E7, 0x65A14, 0x65A1C, 0x65A85,
		0x65A87, 0x65A8F, 0x65A96, 0x65A99, 0x65A9B, 0x65B06, 0x65B15, 0x65B19, 0x65B31, 0x65B3C, 0x65B59, 0x65BE2,
		0x65C0C, 0x65C10, 0x65C63, 0x65C94, 0x65C9E, 0x65DA4, 0x65DB7, 0x65E09, 0x65E16, 0x65E1B, 0x65E41, 0x65E4B,
		0x65E61, 0x65EAD, 0x65ECD, 0x65F75, 0x65F83, 0x65FCA, 0x65FD9, 0x660C8, 0x66157, 0x66168, 0x661DB, 0x662F3,
		0x66306, 0x663EE, 0x6641B, 0x664A0, 0x664D4, 0x6650D, 0x6651A, 0x6651D, 0x6653D, 0x6656E, 0x665A6, 0x665EA,
		0x665F6, 0x66694, 0x66695, 0x666AE, 0x666E5, 0x6673F, 0x66773, 0x6679A, 0x667A2, 0x667DD, 0x6683C, 0x6687D,
		0x66884, 0x66890, 0x668AF, 0x668BB, 0x668D3, 0x66996, 0x6699C, 0x669A6, 0x669FA, 0x66A34, 0x66A6C, 0x66AAC,
		0x66AB2, 0x66B2E, 0x66B31, 0x66B52, 0x66B5C, 0x66BB4, 0x66BC4, 0x66BD0, 0x66BD1, 0x66BD2, 0x66C56, 0x66CB9,
		0x66D09, 0x66D17, 0x66D1B, 0x66D41, 0x66D5C, 0x66D74, 0x66D7E, 0x66D85, 0x66DFB, 0x66E2C, 0x66E2D, 0x66E85,
		0x66EA3, 0x66EAB, 0x66F6C, 0x66F99, 0x66FBE, 0x66FC5, 0x66FCE, 0x66FEE, 0x66FF4, 0x66FFA, 0x66FFD, 0x6702E,
		0x67072, 0x67073, 0x6707F, 0x67099, 0x670B3, 0x670C3, 0x670C6, 0x670ED, 0x67124, 0x67152, 0x6717B, 0x671A8,
		0x671AA, 0x68DB5, 0x68E18, 0x68E1A, 0x68E4C, 0x68EC7, 0x68ECB, 0x68EEC, 0x68F21, 0x68F3A, 0x68F48, 0x68F4B,
		0x68F77, 0x68FC1, 0x68FCE, 0x68FE6, 0x68FF6, 0x69019, 0x69020, 0x69046, 0x6906F, 0x6907A, 0x6909A, 0x690A3,
		0x690CC, 0x690F8, 0x691A1, 0x691C3, 0x691CE, 0x691CF, 0x691EB, 0x691ED, 0x69260, 0x692C5, 0x692C9, 0x692F7,
		0x69317, 0x6931F, 0x69330, 0x69379, 0x693C8, 0x693CB, 0x693D4, 0x693F0, 0x69411, 0x69415, 0x69438, 0x69446,
		0x6944E, 0x69455, 0x69475, 0x69497, 0x6949C, 0x694C5, 0x694CB, 0x694D0, 0x694D1, 0x69525, 0x69545, 0x6954A,
		0x69557, 0x69570, 0x69571, 0x69574, 0x69576, 0x6957A, 0x69596, 0x6959A, 0x6959E, 0x695A9, 0x695E5, 0x69602,
		0x6962A, 0x6962C, 0x69638, 0x69685, 0x69687, 0x6968F, 0x696A3, 0x696EF, 0x696F2, 0x696FA, 0x6970F, 0x6971B,
		0x6972E, 0x69732, 0x69735, 0x69791, 0x69793, 0x6979E, 0x697AB, 0x697E0, 0x6980E, 0x69815, 0x69851, 0x69865,
		0x69867, 0x69872, 0x69878, 0x6987D, 0x6987E, 0x6987F, 0x6988F, 0x698B8, 0x698BA, 0x698E1, 0x69916, 0x69922,
		0x69973, 0x69993, 0x699AC, 0x699F1, 0x699FA, 0x699FF, 0x69A04, 0x69A18, 0x69A1B, 0x69A55, 0x69A82, 0x69A90,
		0x69A9D, 0x69AA9, 0x69BD5, 0x69C8A, 0x69D2D, 0x69EEE, 0x69F02, 0x69F06, 0x69FE2, 0x6A014, 0x6A279, 0x6A297,
		0x6A318, 0x6A324, 0x6A34B, 0x6A367, 0x6A377, 0x6A381, 0x6A386, 0x6A3B2, 0x6A3B3, 0x6A3CB, 0x6A3FB, 0x6A416,
		0x6A417, 0x6A41A, 0x6A42B, 0x6A450, 0x6A4B0, 0x6A4CD, 0x6A4FE, 0x6A584, 0x6A599, 0x6A59B, 0x6A600, 0x6A60F,
		0x6A625, 0x6A630, 0x6A6A1, 0x6A6AE, 0x6A6CB, 0x6A6D5, 0x6A76B, 0x6A78A, 0x6A7F8, 0x6A803, 0x6A80E, 0x6A81B,
		0x6A86C, 0x6A8A5, 0x6A8C9, 0x6A8E1, 0x6A97F, 0x6A9A1, 0x6A9D0, 0x6A9E8, 0x6A9F3, 0x6AA07, 0x6AB14, 0x6AD55,
		0x6AE00, 0x6AE2A, 0x6AF3B, 0x6AF3E, 0x6AF42, 0x6AF45, 0x6AF55, 0x6AFA2, 0x6AFC3, 0x6AFC6, 0x6AFCB, 0x6AFD5,
		0x6B01C, 0x6B025, 0x6B028, 0x6B037, 0x6B043, 0x6B055, 0x6B05D, 0x6B064, 0x6B080, 0x6B0B2, 0x6B0B8, 0x6B0B9,
		0x6B0C8, 0x6B0CB, 0x6B0CD, 0x6B0CE, 0x6B0CF, 0x6B0D2, 0x6B0D6, 0x6B0D9, 0x6B0F1, 0x6B0F3, 0x6B103, 0x6B10C,
		0x6B117, 0x6B11D, 0x6B11E, 0x6B11F, 0x6B138, 0x6B146, 0x6B14D, 0x6B16A, 0x6B16D, 0x6B170, 0x6B17F, 0x6B187,
		0x6B18D, 0x6B194, 0x6B1AA, 0x6B1BA, 0x6B1C1, 0x6B1CB, 0x6B1DA, 0x6B1ED, 0x6B1F6, 0x6B1FA, 0x6B1FD, 0x6B213,
		0x6B232, 0x6B233, 0x6B234, 0x6B237, 0x6B24B, 0x6B24C, 0x6B277, 0x6B27B, 0x6B291, 0x6B29B, 0x6B29D, 0x6B29E,
		0x6B2A0, 0x6B2A5, 0x6B2A7, 0x6B2AC, 0x6B2D6, 0x6B2DE, 0x6B2F4, 0x6B2F6, 0x6B2FA, 0x6B2FF, 0x6B32C, 0x6B331,
		0x6B336, 0x6B342, 0x6B364, 0x6B3A2, 0x6B3A4, 0x6B3AC, 0x6B3B2, 0x6B3E4, 0x6B3FC, 0x6B422, 0x6B42B, 0x6B43B,
		0x6B451, 0x6B45C, 0x6B4A3, 0x6B4A5, 0x6B4A7, 0x6B4A9, 0x6B4B4, 0x6B4EB, 0x6B4ED, 0x6B51D, 0x6B525, 0x6B542,
		0x6B54B, 0x6B580, 0x6B584, 0x6B590, 0x6B594, 0x6B596, 0x6B64E, 0x6B6AB, 0x6B6EF, 0x6B6FF, 0x6B755, 0x6B774,
		0x6B794, 0x6B891, 0x6B966, 0x6B989, 0x6BA1A, 0x6BA2E, 0x6BA62, 0x6BB31, 0x6BB68, 0x6BBD8, 0x6BC9E, 0x6BD16,
		0x6BD37, 0x6BD3B, 0x6BD4A, 0x6BD4F, 0x6BDDE, 0x6BDE6, 0x6BDF0, 0x6BE02, 0x6BE33, 0x6BE4B, 0x6BE4D, 0x6BE70,
		0x6BE80, 0x6BE81, 0x6BE96, 0x6BEA0, 0x6BEB0, 0x6BEB2, 0x6BED3, 0x6BED5, 0x6BEDA, 0x6BEF5, 0x6BEF9, 0x6BF05,
		0x6BF08, 0x6BF29, 0x6BF2A, 0x6BF38, 0x6BF4F, 0x6BF54, 0x6BF55, 0x6BF5D, 0x6BF6C, 0x6BF74, 0x6BF75, 0x6BF7F,
		0x6BF84, 0x6BF8D, 0x6BF96, 0x6BFAA, 0x6BFD4, 0x6BFDA, 0x6BFDD, 0x6BFFA, 0x6C029, 0x6C02A, 0x6C033, 0x6C037,
		0x6C042, 0x6C048, 0x6C04F, 0x6C054, 0x6C07E, 0x6C080, 0x6C088, 0x6C08C, 0x6C0B7, 0x6C0C9, 0x6C0DF, 0x6CD4E,
		0x6CDC5, 0x6CDC6, 0x6CE59, 0x6CE6A, 0x6CEC4, 0x6CEE6, 0x6CEF1, 0x6CEF2, 0x6CEF9, 0x6CEFD, 0x6CEFF, 0x6CFA2,
		0x6CFE8, 0x6D012, 0x6D02E, 0x6D03E, 0x6D040, 0x6D04E, 0x6D056, 0x6D05B, 0x6D05F, 0x6D061, 0x6D067, 0x6D0E0,
		0x6D16E, 0x6D1AC, 0x6D1BE, 0x6D1D0, 0x6D1DC, 0x6D219, 0x6D22E, 0x6D283, 0x6D28D, 0x6D28F, 0x6D291, 0x6D294,
		0x6D2B8, 0x6D2BD, 0x6D2E3, 0x6D310, 0x6D313, 0x6D321, 0x6D336, 0x6D34E, 0x6D355, 0x6D370, 0x6D387, 0x6D38C,
		0x6D390, 0x6D399, 0x6D39B, 0x6D3C9, 0x6D3CA, 0x6D3CB, 0x6D3CC, 0x6D3E0, 0x6D3F4, 0x6D3FA, 0x6D3FD, 0x6D407,
		0x6D43A, 0x6D440, 0x6D44E, 0x6D467, 0x6D46A, 0x6D47D, 0x6D47E, 0x6D4D3, 0x6D4E3, 0x6D4FF, 0x6D500, 0x6D529,
		0x6D53A, 0x6D548, 0x6D54F, 0x6D55E, 0x6D574, 0x6D593, 0x6D5A3, 0x6D5E5, 0x6D5E8, 0x6D5EE, 0x6D5F0, 0x6D5FE,
		0x6D60C, 0x6D60E, 0x6D640, 0x6D649, 0x6D6D2, 0x6D70C, 0x6D72A, 0x6D730, 0x6D7BB, 0x6D7EA, 0x6D802, 0x6D810,
		0x6D813, 0x6D830, 0x6D8A4, 0x6D8A9, 0x6D8AC, 0x6D927, 0x6D92F, 0x6DA26, 0x6DA41, 0x6DA82, 0x6DA8A, 0x6DAB9,
		0x6DB1B, 0x6DBA2, 0x6DC32, 0x6DC3B, 0x6DC42, 0x6DC70, 0x6DC8D, 0x6DCCE, 0x6DCD2, 0x6DCF8, 0x6DD02, 0x6DD03,
		0x6DD3A, 0x6DD68, 0x6DD82, 0x6DDA0, 0x6DDBB, 0x6DDEF, 0x6DE29, 0x6DE85, 0x6DE99, 0x6DE9E, 0x6DED7, 0x6DF15,
		0x6DF22, 0x6DF2A, 0x6DF34, 0x6DF9F, 0x6DFAA, 0x6DFCD, 0x6DFFD, 0x6E018, 0x6E01E, 0x6E0ED, 0x6E0FC, 0x6E126,
		0x6E131, 0x6E137, 0x6E143, 0x6E14B, 0x6E154, 0x6E16D, 0x6E16E, 0x6E16F, 0x6E170, 0x6E171, 0x6E172, 0x6E19E,
		0x6E1A4, 0x6E1AA, 0x6E1AE, 0x6E20C, 0x6E216, 0x6E217, 0x6E228, 0x6E29E, 0x6E9B7, 0x6E9BA, 0x6EA10, 0x6EA63,
		0x6EAC4, 0x6EAE7, 0x6EAE8, 0x6EB42, 0x6EB6B, 0x6EB70, 0x6EB86, 0x6EBA9, 0x6EBCA, 0x6EBE3, 0x6EBFC, 0x6EC21,
		0x6EC34, 0x6EC71, 0x6EC73, 0x6EC7D, 0x6EC7F, 0x6EC9C, 0x6ECA5, 0x6ECA8, 0x6ECAF, 0x6ECC7, 0x6ECDA, 0x6ECDD,
		0x6ECEE, 0x6ED03, 0x6ED2F, 0x6ED3A, 0x6ED3E, 0x6EDAF, 0x6EDD1, 0x6EDD9, 0x6EE9E, 0x6EEA4, 0x6EEAA, 0x6EEB2,
		0x6EF26, 0x6EF81, 0x6EFE6, 0x6F0C7, 0x6F0D2, 0x6F0EF, 0x6F17A, 0x6F17D, 0x6F185, 0x6F18E, 0x6F1C2, 0x6F1ED,
		0x6F1FC, 0x6F267, 0x6F26A, 0x6F274, 0x6F27E, 0x6F28E, 0x6F2D4, 0x6F2FA, 0x6F300, 0x6F369, 0x6F370, 0x6F391,
		0x6F40A, 0x6F40E, 0x6F410, 0x6F411, 0x6F412, 0x6F41B, 0x6F42F, 0x6F432, 0x6F447, 0x6F44E, 0x6F46C, 0x6F475,
		0x6F47C, 0x6F482, 0x6F48F, 0x6F4AE, 0x6F4C9, 0x6F4CB, 0x6F4DE, 0x6F4E1, 0x6F52A, 0x6F5D9, 0x6F60B, 0x6F62F,
		0x6F638, 0x6F639, 0x6F70F, 0x6F712, 0x6F760, 0x6F792, 0x6F7C0, 0x6F7D2, 0x6F7DA, 0x6F881,
	};

	// Ablation switch, deliberately RUNTIME rather than compile-time so the gate can be shown to FAIL
	// without a rebuild. `XMEM_ABLATE_SPECULATION_FLAG=1 ./xmemProbe speculation_selftest` must
	// report FAIL on $50F14/$4FFD2; if it still reports PASS, the selftest is decorative.
	// Any report produced while this is set carries a loud banner -- an ablated instrument must never
	// be mistakable for a working one.
	inline bool speculationFlagAblated()
	{
		static const bool ablated = []
		{
			const char* e = std::getenv("XMEM_ABLATE_SPECULATION_FLAG");
			return e && *e && *e != '0';
		}();
		return ablated;
	}

	inline bool isCondBranchTarget(uint32_t _addr)
	{
		if (speculationFlagAblated())
			return false;
		return std::binary_search(std::begin(g_condBranchTargets), std::end(g_condBranchTargets), _addr);
	}

	// Appended to a BLOCK-START line. Empty for every other status: `covered-mid-block` and
	// `NOT REACHED` are range facts, not creation facts, and are not affected by speculation.
	inline const char* speculationNote(const bool _startsBlock, const uint32_t _addr)
	{
		if (!_startsBlock || !isCondBranchTarget(_addr))
			return "";
		return "  (SPECULATIVE-RISK: conditional-branch target)";
	}

	// Printed once per report that contains any block-start list, so a reader who never opens this
	// source still cannot mistake creation for execution.
	inline void writeSpeculationLegend(std::ostream& _out)
	{
		if (speculationFlagAblated())
		{
			_out << "\n!!!!!!!!!!!!!!!! SPECULATION FLAG ABLATED (XMEM_ABLATE_SPECULATION_FLAG) !!!!!!!!!!!!!!!!\n"
			        "This report's BLOCK-START lines carry NO speculative-risk annotation because the\n"
			        "flag was switched off. Do not use this report as evidence of anything.\n"
			        "!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!\n\n";
			return;
		}
		_out << "\n--- how to read BLOCK-START (2026-08-03) ---\n"
		        "  A BLOCK-START is JIT block CREATION, NOT execution. gearmulator compiles BOTH arms of\n"
		        "  a conditional branch when the parent block compiles (jitblock.cpp:414/425 ->\n"
		        "  jitblockchain.cpp:325 create(pc, _execute=false)), so a jXX/bXX target can appear here\n"
		        "  having never run. Lines marked (SPECULATIVE-RISK: conditional-branch target) are such\n"
		        "  targets. To tell the two apart, look for a DOWNSTREAM block start inside the same\n"
		        "  function, or a covered-mid-block past the branch.\n"
		        "  The absence of a mark is NOT a guarantee: speculation also cascades through\n"
		        "  UNCONDITIONAL branch targets, which this table deliberately does not model. Indirect\n"
		        "  `jmp (rn)` targets genuinely cannot be speculated. See tools/gen_speculative_targets.py.\n\n";
	}

	// -------------------------------------------------------------------------------------------
	// "speculation_selftest" mode -- the BOTH-DIRECTIONS gate for the flag above.
	//
	// Needs no ROM, no emulator and no container state: the flag is a pure table lookup, so the gate
	// is cheap enough that there is no excuse for not running it. Four controls, chosen so that a
	// wrong implementation fails at least one of them:
	//
	//   $50F14  MUST be flagged     -- `jlt func_050f14` at $050d3b. The address that produced the
	//                                  original misreading.
	//   $4FFD2  MUST be flagged     -- `jeq func_04ffd2` at $00093b. A second, independent site, so a
	//                                  hardcoded special case for $50F14 cannot pass.
	//   $51004  MUST NOT be flagged -- reached by an UNCONDITIONAL `bsr func_051004` at $050f50. This
	//                                  is the control that fails if the extractor stops distinguishing
	//                                  conditional from unconditional branches, i.e. the arm that
	//                                  catches "flag everything" -- which would pass the first two.
	//   $000A58 MUST NOT be flagged -- reached only via indirect `jmp (r2)`. Catches an extractor that
	//                                  resolves dynamic targets to a bogus constant.
	inline int runSpeculationSelftest()
	{
		struct Case { uint32_t addr; bool expectFlagged; const char* why; };
		static const Case cases[] = {
			{ 0x50F14, true,  "jlt target at $050d3b -- the 2026-08-03 misreading" },
			{ 0x4FFD2, true,  "jeq target at $00093b -- independent second site" },
			{ 0x51004, false, "UNCONDITIONAL bsr target from $050f50" },
			{ 0x00A58, false, "indirect `jmp (r2)` target only" },
		};

		const bool ablated = speculationFlagAblated();
		std::cout << "speculation_selftest: table holds "
		          << (sizeof(g_condBranchTargets) / sizeof(g_condBranchTargets[0]))
		          << " conditional-branch targets"
		          << (ablated ? "  [ABLATED: XMEM_ABLATE_SPECULATION_FLAG is set]" : "") << "\n";

		int failures = 0;
		for (const auto& c : cases)
		{
			const bool got = isCondBranchTarget(c.addr);
			const bool ok = got == c.expectFlagged;
			if (!ok)
				++failures;
			std::cout << "  " << (ok ? "PASS" : "FAIL") << "  $" << std::hex << std::uppercase
			          << c.addr << std::dec << "  expected " << (c.expectFlagged ? "FLAGGED" : "not flagged")
			          << ", got " << (got ? "FLAGGED" : "not flagged") << "   (" << c.why << ")\n";
		}

		// The table must also be non-degenerate. A table of every address would pass the two
		// must-flag arms; a table with the two must-not-flag arms carved out would pass all four
		// while flagging everything else. Assert a plausible band around the measured 4402 rather
		// than an exact figure, so a regenerated disassembly does not fail this spuriously.
		const size_t n = sizeof(g_condBranchTargets) / sizeof(g_condBranchTargets[0]);
		if (n < 1000 || n > 20000)
		{
			std::cout << "  FAIL  table size " << n << " is outside the sane band [1000, 20000] -- "
			             "a degenerate table can pass the four address controls while flagging "
			             "everything or nothing.\n";
			++failures;
		}
		else
		{
			std::cout << "  PASS  table size " << n << " inside sane band [1000, 20000]\n";
		}

		if (failures)
		{
			std::cout << "speculation_selftest: " << failures << " FAILURE(S)."
			          << (ablated ? "  This is the EXPECTED result under ablation -- it proves the gate "
			                        "can fail.\n" : "\n");
			return 1;
		}
		std::cout << "speculation_selftest: all checks passed.\n";
		if (ablated)
		{
			std::cout << "speculation_selftest: BUT the flag was ABLATED and everything still passed. "
			             "The gate is decorative. Treat this as a failure.\n";
			return 1;
		}
		return 0;
	}

	// "bootdump" mode (2026-07-22): settle the command-stream cmd=1 target-space question raised
	// by reading the boot ROM's dispatch table (work/dsp_commandstream_cmd_semantics_findings_
	// 2026-07-22.md): table at P:$12e = {$0c,$0f,$12,$15,$1f}, bsr r2 at $127 is PC-relative, so
	// cmd=0 -> 'move a,p:(r0)+', cmd=1 -> 'move a,x:(r0)+', cmd=2 -> Y write, cmd=3 -> packed
	// dual-Y, cmd=4 -> 'jmp (r0)' (execute at addr). If that is right, after boot X:$16-$4f must
	// hold the 58 words of the stream's cmd=1@$16 record while P:$16-$4f keeps the cmd=0 record's
	// own words; the prior "cmd=1 is P-memory" reading predicts the opposite. Boots, renders
	// briefly, dumps both spaces at every low-address cmd=1 record head plus the cmd=4 entry
	// point, twice (early + end of render) to expose any runtime rewriting.
	int runBootDump(const std::string& _outFile)
	{
		auto rom = ROMLoader::findROM(DeviceModel::TI2);
		if (!rom.isValid())
		{
			std::cout << "ROM not found/invalid. Place a valid TI2 firmware .bin next to this executable." << std::endl;
			return 1;
		}

		DspSingle* dsp1raw = nullptr;
		DspSingle* dsp2raw = nullptr;
		virusLib::Device::createDspInstances(dsp1raw, dsp2raw, rom, static_cast<float>(rom.getSamplerate()));
		std::unique_ptr<DspSingle> dsp1(dsp1raw);

		Microcontroller uc(*dsp1, rom, false);
		if (dsp2raw)
			uc.addDSP(*dsp2raw, false);

		dsp56k::SpscSemaphore sem(1);
		uint32_t callbackCount = 0;
		int32_t notifyTimeout = 0;
		constexpr uint32_t blockSize = 64;
		const uint32_t notifyThreshold = blockSize > 4 ? blockSize - 4 : 0;
		std::vector<SMidiEvent> midiEvents;

		auto& esai = dsp1->getAudio();
		esai.setCallback([&](dsp56k::Audio*)
		{
			const auto availableSize = esai.getAudioOutputs().size();
			const auto sizeReached = availableSize >= notifyThreshold;
			--notifyTimeout;
			if (notifyTimeout <= 0 && sizeReached)
			{
				notifyTimeout = static_cast<int>(notifyThreshold);
				sem.notify();
			}

			++callbackCount;
			if ((callbackCount & 0x3) != 0)
				return;

			uc.readMidiOut(midiEvents);
			uc.process();
			if ((callbackCount >> 2) == 1)
			{
				dsp1->drainESSI1();
				uc.sendInitControlCommands(127);
			}
		});

		virusLib::Device::bootDSPs(dsp1.get(), dsp2raw, rom, false);

		constexpr uint32_t kTotalSamples = 44100; // ~1s: boot completes early, runtime drift shows in the final dump
		std::cout << "Booted. Rendering " << kTotalSamples << " samples (~1s), dumping early + final." << std::endl;

		AudioProcessor proc(rom.getSamplerate(), "xmem_bootdump_throwaway.wav", false, kTotalSamples, dsp1.get(), dsp2raw);
		std::ofstream out(_outFile);
		out << "Mode: bootdump (cmd-target-space check, dsp1)\n";
		uint32_t rendered = 0;
		bool earlyDumped = false;
		const auto dumpAll = [&](const char* _tag)
		{
			const auto& mem = dsp1->getMemory();
			out << "\n=== dump " << _tag << " (after ~" << rendered << " samples) ===\n";
			dumpRange(mem, dsp56k::MemArea_P, "P", 0x000016, 58, out);
			dumpRange(mem, dsp56k::MemArea_X, "X", 0x000016, 58, out);
			dumpRange(mem, dsp56k::MemArea_P, "P", 0x000050, 8, out);
			dumpRange(mem, dsp56k::MemArea_X, "X", 0x000050, 8, out);
			dumpRange(mem, dsp56k::MemArea_Y, "Y", 0x000050, 8, out);
			// ADDED 2026-08-01: independent oracle for the cmd=3 unpacking fix.
			// gearmulator boots by feeding the raw command stream to the REAL boot
			// ROM, so its Y memory here is produced by Access's own unpacking code,
			// not by our reconstruction. Comparing this dump against
			// tools/reconstruct_dsp_memory.py's output tests the fix against an
			// implementation that shares none of our assumptions.
			dumpRange(mem, dsp56k::MemArea_Y, "Y", 0x040082, 160, out);
			dumpRange(mem, dsp56k::MemArea_Y, "Y", 0x0453b0, 16, out);
			// ADDED 2026-09-08 -- THE HOST-PROTOCOL STATE MACHINE (claim-ledger row 176).
			// The HDI08 receive ISR (P:$0060 -> func_05237D) files each host word into one of two
			// rings and dispatches every drained byte through `jsge (r2)` with r2 loaded from
			// X:$482C0. That pointer, its saved copies, the walker's cursor and the state TABLES
			// are all RUNTIME RAM: ti2.X.bin covers only X:$0-$1FB6 and ti2.Y.bin only
			// Y:$0-$453BD, so every one of these addresses is BEYOND the static images and the
			// reachable state set is provably unclosable without executing the firmware. That is
			// the ladder-rung-2 case CLAUDE.md describes; nothing here touches hardware.
			//
			// X:$482B8+16 spans $482BD/$482BE/$482BF (the flags the ring drains test), $482C0
			// (the live handler pointer), and $482C1/$482C2 (its saved copies).
			dumpRange(mem, dsp56k::MemArea_X, "X", 0x0482b8, 16, out);
			// Y:$482E0+24 spans the walker cursor $482E4 and the two roots $482EE/$482F0 that
			// func_05259A is entered with from $052569 and $052578.
			dumpRange(mem, dsp56k::MemArea_Y, "Y", 0x0482e0, 24, out);
			// The other two roots, from $054ED1 and $054EEA.
			dumpRange(mem, dsp56k::MemArea_Y, "Y", 0x054ed0, 16, out);
			dumpRange(mem, dsp56k::MemArea_Y, "Y", 0x054ef0, 16, out);
			// ROUND 2, 2026-09-08: the NODE REGION, so the graph can be WALKED rather than
			// sampled. The first dump showed the roots hold handler $0525AF with links to
			// Y:$482F2 and Y:$48307, the cursor y:$482E4 = $48327, and further node pointers
			// $48316 and $4834E -- all inside $48300-$4835F. 96 words covers the whole cluster
			// in one pass so a second rebuild is not needed to follow one more link.
			dumpRange(mem, dsp56k::MemArea_Y, "Y", 0x048300, 96, out);
			dumpRange(mem, dsp56k::MemArea_P, "P", 0x000b0e, 8, out);
			dumpRange(mem, dsp56k::MemArea_X, "X", 0x000b0e, 8, out);
			dumpRange(mem, dsp56k::MemArea_P, "P", 0x000c00, 8, out);
			dumpRange(mem, dsp56k::MemArea_X, "X", 0x000c00, 8, out);
			dumpRange(mem, dsp56k::MemArea_P, "P", 0x001e70, 16, out);
			dumpRange(mem, dsp56k::MemArea_X, "X", 0x001e70, 16, out);
			// X:$52058 -- THE SAMPLE-RATE SELECTOR, added 2026-08-12.
			// doc/port_algorithm_inventory.md gives it a section of its own: it has NO VISIBLE
			// WRITER in the static graph, and it decides three separate questions -- the 32 kHz
			// EQ-band candidate, the X:$484b7 enumeration, and which rate is actually live.
			// "fs = 44100 is in force" was REFUTED on 2026-08-12
			// (work/falsify/pitch-closed-form-fs-cancels.verdict.md C2), so every Hz figure in the
			// Vowel, Comb, Pitch and EQ/Phaser rows is either conditional on an unestablished rate
			// or has been rewritten to cite an algebraic cancellation instead.
			// No existing dump range came near it -- the X ranges stopped at $1e70 -- so the cell
			// has never been observed, only reasoned about. A window rather than a single word,
			// because a neighbour that moves with it is evidence and a lone value is not.
			dumpRange(mem, dsp56k::MemArea_X, "X", 0x052050, 24, out);
			// AND THE SAME WINDOW IN Y, added 2026-08-12 AFTER a cross-vendor pass REFUTED the
			// conclusion drawn from the X dump alone: the code writes `y:>$52058`, the first dump
			// read MemArea_X, and the X window returned P-image content for every unwritten word.
			// So "X:$52058 = $0 at boot" could not establish the live selector's value.
			// work/falsify/rate-table-six-rates.verdict.md C5 (REFUTED).
			dumpRange(mem, dsp56k::MemArea_Y, "Y", 0x052050, 24, out);
			// The rate table itself, so the selected row is visible beside the selector rather
			// than inferred from the static image. $484b8-$484d3 inclusive is 28 words = 7 rows
			// of 4; $484b4-$484b7 are the four cells func_053095 stores the selected row into.
			dumpRange(mem, dsp56k::MemArea_X, "X", 0x0484b4, 32, out);
			dumpRange(mem, dsp56k::MemArea_Y, "Y", 0x0484b4, 32, out);
			dumpRange(mem, dsp56k::MemArea_P, "P", 0x000d0c, 8, out);
		};
		while (!proc.finished())
		{
			sem.wait();
			proc.processBlock(blockSize);
			rendered += blockSize;
			if (!earlyDumped && rendered >= 8192)
			{
				earlyDumped = true;
				dumpAll("early");
			}
		}
		dumpAll("final");
		std::cout << "Wrote " << _outFile << std::endl;
		return 0;
	}

	// Bank/program parameterised 2026-08-03. It was hardcoded to 11/124 "VocoPad XM", a
	// VOCODER pad -- and the 2026-08-02 result that `func_051004` is NOT REACHED was
	// therefore a statement about one atypical preset, not about the firmware. Any
	// dormancy claim needs at least one ordinary subtractive patch before it means
	// anything (claim-ledger row 91).
	// _overrideOffset/_overrideValue (2026-08-03): bake one preset byte before load, so a
	// correlation observed across presets can be tested as an INTERVENTION on a single one.
	// Observationally, func_051004 is reached iff Filter1 Resonance (offset 42) is 0, 13/13
	// presets -- but presets with zero resonance may share other traits, and only forcing the
	// byte distinguishes the two.
	// SECOND override added 2026-08-03. Several open questions are UNTESTABLE with one override
	// because the parameter under test only reaches the DSP when a second parameter gates it:
	// Delay Mode (offset 112) selects a handler that never runs while Delay Send (offset 113) is
	// 0, so a Delay-Mode-only run measures the send gate, not the mode. Both overrides are baked
	// into the preset AND sent live at cb 400, exactly as the first one is -- a second-override
	// run with _override2Offset < 0 is bit-identical to the old single-override path.
	int runPcTrace(const std::string& _outFile, uint32_t _bank = 11, uint32_t _program = 124,
	               int _overrideOffset = -1, int _overrideValue = 0,
	               int _override2Offset = -1, int _override2Value = 0)
	{
		auto rom = ROMLoader::findROM(DeviceModel::TI2);
		if (!rom.isValid())
		{
			std::cout << "ROM not found/invalid. Place a valid TI2 firmware .bin next to this executable." << std::endl;
			return 1;
		}

		Microcontroller::TPreset preset{};
		rom.getSingle(_bank, _program, preset);
		if (_overrideOffset >= 0 && static_cast<size_t>(_overrideOffset) < preset.size())
		{
			std::cout << "OVERRIDE preset byte " << _overrideOffset << ": "
			          << static_cast<int>(preset[_overrideOffset]) << " -> " << _overrideValue << std::endl;
			preset[_overrideOffset] = static_cast<uint8_t>(_overrideValue);
		}
		if (_override2Offset >= 0 && static_cast<size_t>(_override2Offset) < preset.size())
		{
			std::cout << "OVERRIDE2 preset byte " << _override2Offset << ": "
			          << static_cast<int>(preset[_override2Offset]) << " -> " << _override2Value << std::endl;
			preset[_override2Offset] = static_cast<uint8_t>(_override2Value);
		}
		std::cout << "Using preset bank " << _bank << " program " << _program << " = \""
		          << ROMFile::getSingleName(preset) << "\" for pc_trace." << std::endl;

		DspSingle* dsp1raw = nullptr;
		DspSingle* dsp2raw = nullptr;
		virusLib::Device::createDspInstances(dsp1raw, dsp2raw, rom, static_cast<float>(rom.getSamplerate()));
		std::unique_ptr<DspSingle> dsp1(dsp1raw);

		Microcontroller uc(*dsp1, rom, false);
		if (dsp2raw)
			uc.addDSP(*dsp2raw, false);

		AddrTracker tracker1(dsp1->getDSP(), "dsp1");
		dsp1->getDSP().setDebugger(&tracker1);
		std::unique_ptr<AddrTracker> tracker2;
		if (dsp2raw)
		{
			tracker2 = std::make_unique<AddrTracker>(dsp2raw->getDSP(), "dsp2");
			dsp2raw->getDSP().setDebugger(tracker2.get());
		}

		dsp56k::SpscSemaphore sem(1);
		uint32_t callbackCount = 0;
		int32_t notifyTimeout = 0;
		constexpr uint32_t blockSize = 64;
		const uint32_t notifyThreshold = blockSize > 4 ? blockSize - 4 : 0;
		std::vector<SMidiEvent> midiEvents;

		bool presetSent = false, noteSent = false, secondNoteSent = false, arpToggled = false, ccSwept = false;
		bool overrideParamSent = false;
		bool landingSampled = false;
		dsp56k::TWord landingVoice = 0, landingR1 = 0, landingR4 = 0;
		dsp56k::TWord landingVals[9] = {};
		std::vector<dsp56k::TWord> landingHits;    // addresses holding (overrideValue << 16)
		std::vector<dsp56k::TWord> landingHits2;   // same, for the second override (2026-08-03)

		auto& esai = dsp1->getAudio();
		esai.setCallback([&](dsp56k::Audio*)
		{
			const auto availableSize = esai.getAudioOutputs().size();
			const auto sizeReached = availableSize >= notifyThreshold;
			--notifyTimeout;
			if (notifyTimeout <= 0 && sizeReached)
			{
				notifyTimeout = static_cast<int>(notifyThreshold);
				sem.notify();
			}

			++callbackCount;
			if ((callbackCount & 0x3) != 0)
				return;

			uc.readMidiOut(midiEvents);
			const auto audioCallbackCount = callbackCount >> 2;
			uc.process();

			if (audioCallbackCount == 1)
			{
				dsp1->drainESSI1();
				uc.sendInitControlCommands(127);
			}
			else if (audioCallbackCount == 256 && !presetSent)
			{
				dsp1->drainESSI1();
				dsp1->disableESSI1();
				std::cout << "[cb " << audioCallbackCount << "] Sending preset" << std::endl;
				uc.writeSingle(BankNumber::EditBuffer, virusLib::SINGLE, preset);
				presetSent = true;
			}
			// OVERRIDE GOES BEFORE THE FIRST NOTE, moved here 2026-08-03. It used to be sent
			// after the SECOND note (cb 900) and the positive control failed: forcing Filter1
			// Mode to HP/BP did not move the HP/BP kernels, though row 90 says mode selects a
			// different handler. Filter mode and resonance are latched per voice at note-on, so
			// a parameter arriving after the last note has no voice left to affect and nothing
			// new is ever JIT-compiled -- the override read as inert when it was merely LATE.
			// cb 400 sits after the preset write (256) and before the first note (512).
			else if (audioCallbackCount == 400 && (_overrideOffset >= 0 || _override2Offset >= 0) && !overrideParamSent)
			{
				overrideParamSent = true;
				// Page map matches "sweep" mode's: 0x70->0, 0x71->128, 0x6E->256, 0x6F->384.
				// Extended 2026-08-03 -- it covered only 0x70/0x71, so any offset >= 256 was
				// silently sent to the WRONG PAGE. Reverb Send is offset 258 = page 0x6E index 2.
				static const uint8_t kPages[4] = { 0x70, 0x71, 0x6E, 0x6F };
				// One lambda, used for BOTH overrides, so the second can never drift from the
				// first: the page map, the SysEx frame and the send path are literally the same
				// code, not a copy that a later edit could update in only one place.
				const auto sendOverride = [&](int _off, int _val, const char* _tag)
				{
					const uint8_t page  = kPages[(_off >> 7) & 3];
					const uint8_t index = static_cast<uint8_t>(_off & 0x7f);
					std::cout << "[cb " << audioCallbackCount << "] Sending live PARAM_CHANGE " << _tag
						<< " page $" << std::hex << static_cast<int>(page) << std::dec << " idx "
						<< static_cast<int>(index) << " = " << _val
						<< "  (BEFORE first note)" << std::endl;
					synthLib::SysexBuffer sysex{
						0xf0, 0x00, 0x20, 0x33, 0x01, 0x00,
						page, virusLib::SINGLE, index, static_cast<uint8_t>(_val),
						0xf7
					};
					std::vector<SMidiEvent> responses;
					uc.sendSysex(sysex, responses, MidiEventSource::Host);
				};
				if (_overrideOffset >= 0)
					sendOverride(_overrideOffset, _overrideValue, "[override1]");
				if (_override2Offset >= 0)
					sendOverride(_override2Offset, _override2Value, "[override2]");
			}
			// SAMPLE THE LANDING CHECK WHILE A VOICE IS SOUNDING, not after the render.
			// The end-of-run dump reads bases (x:$B52, x:$1, y:$1) that by then point at a
			// RELEASED voice: in baseline, voice+$1f read $4FFD2 (Analog) while preset 11/124's
			// Filter1 Mode byte is 0 (Low Pass) -- i.e. the cell did not even match the preset,
			// which is how I knew the object was wrong. cb 800 sits between the two note-ons.
			else if (audioCallbackCount == 800 && !landingSampled)
			{
				landingSampled = true;
				const auto& m = dsp1->getMemory();
				landingVoice = m.get(dsp56k::MemArea_X, 0xB52);
				landingR1    = m.get(dsp56k::MemArea_X, 0x1);
				landingR4    = m.get(dsp56k::MemArea_Y, 0x1);
				landingVals[0] = m.get(dsp56k::MemArea_X, landingVoice + 0x1f);
				landingVals[1] = m.get(dsp56k::MemArea_X, landingVoice + 0x21);
				landingVals[2] = m.get(dsp56k::MemArea_X, landingR1 + 0x70);
				landingVals[3] = m.get(dsp56k::MemArea_X, landingR1 + 0x72);
				landingVals[4] = m.get(dsp56k::MemArea_Y, landingR4 + 0x70);
				landingVals[5] = m.get(dsp56k::MemArea_Y, landingR4 + 0x71);
				// voice+$16 and +$14: Filter1 Resonance and Cutoff per doc/dsp56300_live_parameter_map.md,
				// which are VOICE-relative. My earlier "resonance (r1+$72)" label was an inference from
				// func_0510ea's store and is not what the map establishes -- so the resonance override's
				// landing was being judged on the wrong cell.
				landingVals[6] = m.get(dsp56k::MemArea_X, landingVoice + 0x16);
				landingVals[7] = m.get(dsp56k::MemArea_X, landingVoice + 0x14);
				// +$1B, DERIVED not guessed: the 2026-08-03 sweep put Filter1 Resonance at
				// X/Y:$49BB9 while the voice base read $49B9E, so the offset is $1B. The live
				// parameter map's +$16 is five words short, which is exactly why every earlier
				// probe read a constant and was misread as 'the override never arrived'.
				landingVals[8] = m.get(dsp56k::MemArea_X, landingVoice + 0x1b);
				// LOCATE THE CELL BY THE VALUE IT TAKES, NOT BY A FIXED OFFSET. Filter1
				// Resonance was measured 2026-08-03 at X/Y:$49BB9 holding `raw << 16` exactly
				// (5/5) -- but that address came from a DIFFERENT process, and the voice base
				// MOVES between runs. Hardcoding it would repeat the error that made three
				// days of probes read constants. A search for the expected value is
				// self-verifying: if nothing holds it, the override did not arrive, and that
				// conclusion does not depend on any offset being right.
				if (_overrideOffset >= 0)
				{
					const dsp56k::TWord want = static_cast<dsp56k::TWord>(_overrideValue) << 16;
					for (dsp56k::TWord a = 0x49000; a < 0x4A000 && landingHits.size() < 12; ++a)
						if (m.get(dsp56k::MemArea_X, a) == want)
							landingHits.push_back(a);
				}
				// The SECOND override gets its own search, not a shared one. With two overrides
				// a single hit list cannot say WHICH of the two arrived, and "one of them landed"
				// is exactly the ambiguity that makes a gated experiment uninterpretable.
				if (_override2Offset >= 0)
				{
					const dsp56k::TWord want2 = static_cast<dsp56k::TWord>(_override2Value) << 16;
					for (dsp56k::TWord a = 0x49000; a < 0x4A000 && landingHits2.size() < 12; ++a)
						if (m.get(dsp56k::MemArea_X, a) == want2)
							landingHits2.push_back(a);
				}
			}
			else if (audioCallbackCount == 512 && !noteSent)
			{
				std::cout << "[cb " << audioCallbackCount << "] Sending Note On" << std::endl;
				uc.sendMIDI(SMidiEvent(MidiEventSource::Host, 0x90, 60, 0x5f));
				uc.sendPendingMidiEvents(std::numeric_limits<uint32_t>::max());
				noteSent = true;
			}
			else if (audioCallbackCount == 900 && !secondNoteSent)
			{
				// A second, different-pitch Note On (chord, not retrigger) -- broadens coverage of
				// any per-voice-index-dependent path (recall func_04f946's confirmed {1,2,3} index
				// check) beyond a single voice's lifecycle.
				std::cout << "[cb " << audioCallbackCount << "] Sending second Note On (note 64)" << std::endl;
				uc.sendMIDI(SMidiEvent(MidiEventSource::Host, 0x90, 64, 0x5f));				uc.sendPendingMidiEvents(std::numeric_limits<uint32_t>::max());
				secondNoteSent = true;
			}
			else if (audioCallbackCount == 1200 && !arpToggled)
			{
				// Arpeggiator ON -- one of the still-untried func_05c9e8 VM candidates per plan.md,
				// and broadens per-tick coverage generally; free to include here since this mode is
				// about maximizing which P-memory addresses get JIT-compiled at all, not isolating
				// a single trigger's effect the way the "sweep"/"vocoder" experiments are.
				synthLib::SysexBuffer sysex{
					0xf0, 0x00, 0x20, 0x33, 0x01, 0x00,
					0x71, virusLib::SINGLE, 0x3b, 1, // page 113/PAGE_B, Arp Mode idx 0x3b, ON
					0xf7
				};
				std::vector<SMidiEvent> responses;
				uc.sendSysex(sysex, responses, MidiEventSource::Host);
				arpToggled = true;
			}
			else if (audioCallbackCount == 1500 && !ccSwept)
			{
				std::cout << "[cb " << audioCallbackCount << "] Sending all 128 MIDI CCs and perf controls" << std::endl;
				for (int i = 0; i < 128; ++i)
				{
					uc.sendMIDI(SMidiEvent(MidiEventSource::Host, 0xB0, i, 64));
				}
				uc.sendMIDI(SMidiEvent(MidiEventSource::Host, 0xE0, 0, 64)); // Pitch Bend
				uc.sendMIDI(SMidiEvent(MidiEventSource::Host, 0xD0, 64, 0)); // Channel Pressure
				uc.sendMIDI(SMidiEvent(MidiEventSource::Host, 0xA0, 60, 64)); // Poly Aftertouch
				uc.sendPendingMidiEvents(std::numeric_limits<uint32_t>::max());
				ccSwept = true;
			}
			// "Bulk SysEx patch dump/save" and "Multi-mode part-switching" (plan.md item 1's
			// remaining tail candidates) were both attempted here and reverted -- see
			// work/dsp_c9e8_pc_trace_crosscheck_findings.md for why: a REQUEST_BANK_SINGLE-style
			// bulk dump is host-only in Microcontroller (never touches the DSP, confirmed by
			// reading microcontroller.cpp), so a writeSingle burst was used as a proxy instead;
			// switching PLAY_MODE to Multi triggers a real internal writeMulti()+16x writeSingle()
			// replay, but repeatedly crashed gearmulator (SIGBUS) on specific bank-1 ROM presets
			// (the same class of landmine as the already-known "bank 0/program 0 crashes the
			// core" case elsewhere in this file) -- out of scope to chase further (gearmulator's
			// own internal stability, not this project's code).
		});

		virusLib::Device::bootDSPs(dsp1.get(), dsp2raw, rom, false);

		constexpr uint32_t kTotalSamples = 176400; // ~4s @ 44100Hz, matches vm_watch's proven duration
		std::cout << "Booted. Rendering " << kTotalSamples << " samples (~4s), tracking every "
			"JIT-compiled block's P-memory range on both DSPs..." << std::endl;

		AudioProcessor proc(rom.getSamplerate(), "xmem_pc_trace_throwaway.wav", false, kTotalSamples, dsp1.get(), dsp2raw);
		while (!proc.finished())
		{
			sem.wait();
			proc.processBlock(blockSize);
		}

		dsp1->getDSP().setDebugger(nullptr);
		if (dsp2raw)
			dsp2raw->getDSP().setDebugger(nullptr);

		// SETTLING MEASUREMENT 2026-08-01: is the alias target of the firmware's
		// out-of-range $8f0000 accesses live data or zeros? The JIT masks an OOR
		// offset with size(_area)-1, so $8f0000 -> $0f0000. If that region is all
		// zero, masking and the interpreter's return-0 are equivalent; if it is
		// nonzero, masking feeds live memory to the firmware.
		{
			auto dumpAlias = [](dsp56k::DSP& _dsp, const char* _label)
			{
				auto& m = _dsp.memory();
				for (auto area : { dsp56k::MemArea_X, dsp56k::MemArea_Y, dsp56k::MemArea_P })
				{
					uint32_t nonZero = 0, maxV = 0; uint32_t firstNZ = 0xffffffff;
					for (uint32_t i = 0; i <= 0x2c0; ++i)
					{
						const auto v = m.get(area, 0x0f0000 + i);
						if (v) { ++nonZero; if (firstNZ == 0xffffffff) firstNZ = i; if (v > maxV) maxV = v; }
					}
					std::cout << "ALIASPROBE " << _label << " area=" << (int)area
						<< " range=$0f0000-$0f02c0 nonzero=" << nonZero << "/" << 0x2c1
						<< " first=$" << std::hex << firstNZ << " max=$" << maxV << std::dec << std::endl;
				}
			};
			dumpAlias(dsp1->getDSP(), "dsp1");
			if (dsp2raw)
				dumpAlias(dsp2raw->getDSP(), "dsp2");
		}

		std::ofstream out(_outFile);
		out << "Mode: pc_trace (JIT-block coverage over ~4s: preset load, 2 notes, Arp ON)\n";
		out << "Preset: bank " << _bank << " program " << _program << " = \""
		    << ROMFile::getSingleName(preset) << "\"\n";
		// BOTH overrides are named in the header. A dump that reported only one would let a
		// reader attribute a two-override result to the single override they remembered asking
		// for -- the same misattribution the filename suffix exists to prevent.
		if (_overrideOffset >= 0)
			out << "OVERRIDE 1: preset byte " << _overrideOffset << " forced to " << _overrideValue << "\n";
		if (_override2Offset >= 0)
			out << "OVERRIDE 2: preset byte " << _override2Offset << " forced to " << _override2Value << "\n";
		if (_overrideOffset < 0 && _override2Offset < 0)
			out << "OVERRIDE: none -- unmodified factory preset\n";
		out << "NOT REACHED means not reached IN THIS SCENARIO -- a floor, never proof code is dead.\n\n";

		// work/dsp_osc_thread3_live_probe_and_correction.md's chain, plus the already-flagged
		// HDI08 drain-ISR reachability question from insights.md -- both were blocked on exactly
		// this kind of live coverage check.
		const std::vector<std::pair<dsp56k::TWord, const char*>> targets = {
			{ 0x053211, "Y:$53eb2 writer (func_053211)" },
			{ 0x053225, "12-slot smoothing case cluster start (func_053225)" },
			{ 0x000264, "func_000264 (chain step 0's callee, body is just 'rti')" },
			{ 0x055e0a, "chain step 1 (calls func_052bf4 x2 + func_051162... see work file)" },
			{ 0x055e25, "chain step 2 (calls func_051162)" },
			{ 0x055e46, "chain step 3 (calls func_050c90)" },
			{ 0x055e5d, "chain step 4 (calls func_050504)" },
			{ 0x055e74, "chain step 5 == Thread B setup (calls func_055e93 cluster)" },
			{ 0x055eb8, "chain step 6 -- contains the jsr to illegal-opcode $04f947" },
			{ 0x055d38, "func_055d38, the chain's own entry (template/reset init hypothesis)" },
			{ 0x052396, "HDI08 drain ISR: transmit (insights.md, 3rd unreachable-from-statics case)" },
			{ 0x05237d, "HDI08 drain ISR: receive entry" },
			{ 0x05238b, "HDI08 drain ISR: receive body (func_05238b)" },
			// Site 1 (work/dsp_modmatrix_site1_templatezone_attribution_findings.md's "Goal B") --
			// the abs()/store stub cluster and its two confirmed downstream clamp/limit consumer
			// bodies (see work/dsp_site1_live_trigger_findings.md). No static caller was found for
			// $04f0b7 itself in either the old test builds or here; func_04f077/func_04f0a5's own
			// table-select trampoline (statically reached via $0530b3<-func_053095<-$052061<-
			// func_05205b, itself only reached indirectly per static analysis) sits immediately
			// before it in P-memory but returns (rts at $04f0b6) without ever calling into $04f0b7 --
			// confirmed by direct disasm read this session, not assumed from proximity.
			{ 0x04f0b7, "Site1 stub 1 (abs, store Y:$46, new tfr a,b a0,y:$23 fix instruction)" },
			{ 0x04f0c5, "Site1 stub 2 (abs, store Y:$47)" },
			{ 0x04f0cc, "Site1 stub 3 (rnd, store Y:$48)" },
			{ 0x05b18c, "Site1 consumer chain: func_05b18c (clamp/limit body 1)" },
			{ 0x05b1b1, "Site1 consumer chain: func_05b1b1" },
			{ 0x05b1be, "Site1 consumer chain: func_05b1be (clamp/limit body 2)" },
			{ 0x05b1c9, "Site1 consumer chain: func_05b1c9" },
			{ 0x05b199, "Site1 consumer chain: bsmi indirect dispatch table itself" },
			// Filter thread, added 2026-08-02 (claim-ledger rows 90/91). The block-START list
			// alone cannot answer these -- an address can execute inside a block that starts
			// earlier -- so they go through `covers()` here rather than being grepped out of the
			// dump. The open question this decides: does func_051004 execute at all in this
			// preset? Its parameter setters demonstrably do.
			{ 0x051004, "func_051004 -- the 32-sample block routine, IDENTITY REOPENED (row 91)" },
			{ 0x050f7e, "func_050f7e -- its caller-side neighbour" },
			{ 0x050f50, "the bsr site that calls func_051004" },
			{ 0x0510fe, "func_0510fe -- mode selector into the $46dd5 table (row 91)" },
			{ 0x0510dc, "func_0510dc -- cutoff setter" },
			{ 0x0510ea, "func_0510ea -- resonance setter" },
			{ 0x04ff1c, "filter 1 mode-table selector, base $46adc (row 90)" },
			{ 0x04ff32, "filter 2 mode-table selector, base $46aec (row 90)" },
			{ 0x04ffd2, "the Analog 1-4 Pole handler (row 90)" },
			{ 0x000a58, "LP kernel (row 90)" },
			{ 0x000a6b, "HP kernel (row 90)" },
			{ 0x000a7f, "BP kernel (row 90)" },
			{ 0x050238, "BS kernel (row 90)" },
		};

		// Refuse to emit a report that cannot distinguish "not reached" from "not measured".
		if (const auto fatal = coverageInstrumentFatal(tracker1.m_blockStarts.size()); !fatal.empty())
		{
			writeInstrumentFatal(out, fatal);
			out.close();
			return 2;                  // non-zero, so a scripted caller cannot mistake it for a run
		}

		// DID THE OVERRIDE LAND? Added 2026-08-03 after two rounds of chasing a control that
		// could not work. Coverage alone cannot tell "the parameter did not change execution"
		// from "the parameter never arrived", and I spent two re-runs on the latter hypothesis
		// while my control's PREMISE was false: Filter1 Mode genuinely varies (0/4/5) across the
		// seven surveyed presets and the kernel coverage never varied with it, so "forcing mode
		// must move the HP kernel" was already contradicted by data in hand.
		//
		// These cells have INDEPENDENT provenance, which is what makes them usable as a control:
		// $49BBD/$49BBF are Filter1/Filter2 Mode, established by a live sweep at 8/8 (row 90);
		// $49C29/$49C2B are the r1-side cutoff/resonance the setters write; Y:$49D92/$49D93 are
		// func_0510fe's own outputs (row 91). If an override moves none of these, it did not
		// arrive, and every coverage number in this report is uninformative about it.
		{
			// dsp1->getMemory(), NOT dsp1->getDSP().memory(): the latter compiles and returns $5
			// for every address, i.e. a plausible number rather than an error. Caught only because
			// $49BBD was independently known to be $A58 -- a landing check with no known-answer
			// cell would have reported "override did not land" from a broken accessor.
			const auto& m1 = dsp1->getMemory();
			auto cell = [&](dsp56k::EMemArea a, dsp56k::TWord addr) { return m1.get(a, addr); };
			out << "--- override landing check (sampled at cb 800, DURING the note) ---\n";
			if (!landingSampled)
			{
				out << "  NOT SAMPLED -- the run never reached cb 800. Treat every value as absent.\n\n";
			}
			else
			{
				out << "  bases at sample time: voice(x:$B52)=$" << std::hex << std::uppercase
				    << landingVoice << "  r1(x:$1)=$" << landingR1 << "  r4(y:$1)=$" << landingR4
				    << std::dec << "\n";
				static const char* kLabels[9] = {
					"Filter1 Mode handler (voice+$1f)", "Filter2 Mode handler (voice+$21)",
					"cutoff               (r1+$70)",    "resonance            (r1+$72)",
					"curve ptr            (r4+$70)",    "tap ptr              (r4+$71)",
					"F1 res  (voice+$16, map -- WRONG)", "F1 cutoff    (voice+$14, per map)",
					"F1 RESONANCE (voice+$1b, DERIVED)" };
				for (int i = 0; i < 9; ++i)
					out << "  " << kLabels[i] << " = $" << std::hex << std::uppercase
					    << landingVals[i] << std::dec << "\n";
				if (_overrideOffset >= 0)
				{
					out << "  override1 (byte " << _overrideOffset << "=" << _overrideValue
					    << ") cells holding (value<<16) in X:$49000-$49FFF: ";
					if (landingHits.empty()) out << "NONE -- override1 did not arrive";
					else for (auto a : landingHits) out << "$" << std::hex << std::uppercase << a << std::dec << " ";
					out << "\n";
				}
				if (_override2Offset >= 0)
				{
					out << "  override2 (byte " << _override2Offset << "=" << _override2Value
					    << ") cells holding (value<<16) in X:$49000-$49FFF: ";
					if (landingHits2.empty()) out << "NONE -- override2 did not arrive";
					else for (auto a : landingHits2) out << "$" << std::hex << std::uppercase << a << std::dec << " ";
					out << "\n";
				}
				out << "\n";
			}
		}

		writeSpeculationLegend(out);

		for (auto* tracker : { &tracker1, tracker2.get() })
		{
			if (!tracker)
				continue;
			out << "--- " << tracker->m_label << ": " << tracker->m_blockStarts.size()
				<< " distinct JIT blocks compiled ---\n";
			for (const auto& [addr, desc] : targets)
			{
				const bool startsBlock = tracker->m_blockStarts.count(addr) != 0;
				const bool covered = tracker->covers(addr);
				out << "  $" << std::hex << std::uppercase << addr << std::dec
					<< (startsBlock ? "  BLOCK-START" : (covered ? "  covered-mid-block" : "  NOT REACHED"))
					<< "  -- " << desc << speculationNote(startsBlock, addr) << "\n";
			}
			size_t nSpeculative = 0;
			for (const auto addr : tracker->m_blockStarts)
				if (isCondBranchTarget(addr))
					++nSpeculative;
			out << "\n  " << nSpeculative << " of " << tracker->m_blockStarts.size()
				<< " block starts are conditional-branch targets (creation may be speculative).\n";
			out << "\n  Full block-start list:\n";
			for (const auto addr : tracker->m_blockStarts)
				out << "    $" << std::hex << std::uppercase << addr << std::dec
					<< speculationNote(true, addr) << "\n";
			out << "\n";
		}

		out.close();
		std::cout << "Wrote " << _outFile << std::endl;
		return 0;
	}

	// ---------------------------------------------------------------------------------------------
	// "pc_coverage" mode (2026-07-31): whole-image DSP execution coverage, as a LOWER BOUND on how
	// much of the P image is code.
	//
	// WHY THIS IS NOT pc_trace. pc_trace answers "was address X reached" for a hand-written target
	// list, using onJitBlockCreated. That hook is the wrong instrument for a whole-image number, for
	// two separate reasons found by reading the JIT:
	//
	//   1. JitBlockChain::getChildBlock() calls create(_pc, false) -- the JIT SPECULATIVELY compiles
	//      the children of a block so it can chain them, before and possibly without ever executing
	//      them. A block that ends in a conditional branch gets BOTH its taken- and not-taken child
	//      compiled. So "a block was created" is a strict superset of "a block ran", and counting
	//      created blocks would inflate the lower bound in exactly the direction that makes it a
	//      false claim.
	//   2. A block's [getPCFirst(), getPCNext()) span comes from JitBlockInfo's forward static scan,
	//      not from observed execution. Treating every word in the span as executed imports a static
	//      analysis into what is supposed to be a measurement.
	//
	// So this mode uses DebuggerInterface::onExec, which fires with the exact PC of every single
	// instruction the DSP retires -- but ONLY on DSP::execInterpreter(), never under the JIT
	// (dsp.h). It therefore requires a build with DSP56K_FORCE_INTERPRETER=1, which flips
	// dsp.h's g_useJIT constexpr to false.
	//
	// THE REFUSAL IS REAL AS OF 2026-08-02 (T19) AND WAS NOT BEFORE. This comment used to end "The
	// mode refuses to report a coverage number from a JIT build; see the g_useJIT check below." No
	// such check existed. The only thing below was an advisory std::cout, the function returned 0
	// unconditionally, and the claim was repeated in downstream briefs by people who read the
	// comment instead of the code. A comment describing a guard that is not there is worse than no
	// comment. The refusal now lives in the fail-closed block at the end of runPcCoverage, is
	// opt-out only via --jit-control, and exits nonzero.
	//
	// Note the JIT build does NOT report zero, which is why "retired == 0" could never have stood in
	// for the JIT check: DSP::execInterrupt calls onExec too, so a JIT run reports 13 executed words
	// on dsp1 and 9 on dsp2. Small, nonzero, and entirely a dispatched-interrupt-vector set.
	//
	// The JIT build is still useful and this same mode still runs in it, because the created-block
	// set is a legitimate CONTROL: every executed address must also have been compiled, so
	// (interpreter executed set) must be a subset of (JIT created-block span set). A violation means
	// one of the two instruments is lying.
	//
	// WHAT THE OUTPUT MEANS, and this is the trap that has already cost this project a session:
	// an executed address is definitively code. An UNEXECUTED address is "NOT OBSERVED EXECUTING"
	// and nothing more. It is not data. gearmulator drives a scenario, and a scenario reaches what
	// it reaches -- this project already has a worked example of a byte-identical A/B render that
	// meant nothing because gearmulator never executes the Rotary handler at all. Coverage is a
	// lower bound on code and never an upper bound.
	class ExecTracker final : public dsp56k::DebuggerInterface
	{
	public:
		// The DSP's P space for a TI-family ROM is 0x100000 words (virusLib::Device::createDspInstances
		// passes that as the memory size), even though the boot command stream's own writes top out
		// at $06f1fe (tools/dsp_pmem_extent.py). Cover the whole address space: an earlier 0x80000
		// limit here silently bucketed 1,357,962 real executions at $08001c-$080046 as
		// "out-of-range" instead of recording where they were.
		static constexpr dsp56k::TWord kPMemWords = 0x100000;

		ExecTracker(dsp56k::DSP& _dsp, std::string _label)
			: DebuggerInterface(_dsp), m_label(std::move(_label)), m_executed(kPMemWords, 0) {}

		void onExec(const dsp56k::TWord _pc) override
		{
			++m_execCount;

			// INTERRUPT ENTRIES (2026-08-01, control C4). Under the JIT there is exactly ONE call
			// site for DebuggerInterface::onExec in the whole emulator -- DSP::execInterrupt
			// (dsp.cpp:200), because DSP::execJit (dsp.h:207) does not call it at all. So in a
			// g_useJIT build every address that reaches this function is, by construction, an
			// interrupt vector entry that was actually dispatched via m_jitEntries[vba].
			//
			// That matters because those entries are entered through the m_jitEntries function
			// pointer, NOT through a chained created block, so they can be absent from the
			// created-block span even though they demonstrably executed. C4 compares the
			// interpreter's executed set against the JIT build's span, and would report such an
			// address as "executed but never compiled" -- a disagreement about vectors, not a
			// disagreement about the instrument. Emitting the dispatched-vector set lets C4 test
			// (span UNION interrupt entries) instead, which is the set the control actually meant.
			if (dsp56k::g_useJIT && _pc < kPMemWords)
				m_irqEntries.insert(_pc);

			if (_pc < kPMemWords)
			{
				m_executed[_pc] = 1;
				// Diagnostic (2026-08-01): per-PC hit counts + a ring of the most recent PCs, so a
				// watchdog thread can name the exact P address the core is spinning on when a run
				// stops making progress. Cost is one increment per instruction; the run is already
				// ~1000x slower than the JIT, so this is not what makes it slow.
				++m_hits[_pc];
				m_ring[m_ringPos & (kRing - 1)] = _pc;
				++m_ringPos;
			}
			else
			{
				++m_outOfRange;
				m_outOfRangeMin = std::min(m_outOfRangeMin, _pc);
				m_outOfRangeMax = std::max(m_outOfRangeMax, _pc);
			}
		}

		// Kept so the identical source is usable as the JIT-build control described above.
		void onJitBlockCreated(const dsp56k::JitDspMode&, const dsp56k::JitBlockRuntimeData* _block) override
		{
			if (!_block)
				return;
			m_blockStarts.insert(_block->getPCFirst());
			for (auto a = _block->getPCFirst(); a < _block->getPCNext() && a < kPMemWords; ++a)
				m_blockSpan.insert(a);
		}

		size_t distinctExecuted() const
		{
			size_t n = 0;
			for (const auto b : m_executed)
				n += b;
			return n;
		}

		// Top _n hottest PCs, and the recent-PC ring in execution order. Read from the watchdog
		// thread without a lock -- racy by construction and that is fine: this is a diagnostic of a
		// loop that is executing millions of times per second, not a measurement.
		std::string hotspot(size_t _n) const
		{
			std::vector<std::pair<uint64_t, dsp56k::TWord>> v;
			for (dsp56k::TWord a = 0; a < kPMemWords; ++a)
				if (m_hits[a])
					v.emplace_back(m_hits[a], a);
			std::sort(v.begin(), v.end(), std::greater<>());
			std::ostringstream ss;
			for (size_t i = 0; i < _n && i < v.size(); ++i)
				ss << " $" << std::hex << v[i].second << "x" << std::dec << v[i].first;
			return ss.str();
		}

		std::string recentLoop(size_t _n) const
		{
			std::ostringstream ss;
			const uint64_t pos = m_ringPos;
			const size_t n = std::min<uint64_t>(_n, std::min<uint64_t>(pos, kRing));
			for (size_t i = 0; i < n; ++i)
				ss << " $" << std::hex << m_ring[(pos - n + i) & (kRing - 1)];
			return ss.str();
		}

		static constexpr size_t kRing = 64;

		const std::string m_label;
		std::vector<uint8_t> m_executed;
		std::vector<uint32_t> m_hits = std::vector<uint32_t>(kPMemWords, 0);
		std::array<dsp56k::TWord, kRing> m_ring{};
		uint64_t m_ringPos = 0;
		uint64_t m_execCount = 0;
		uint64_t m_outOfRange = 0;
		dsp56k::TWord m_outOfRangeMin = 0xffffffff;
		dsp56k::TWord m_outOfRangeMax = 0;
		std::set<dsp56k::TWord> m_blockStarts;
		std::set<dsp56k::TWord> m_blockSpan;
		std::set<dsp56k::TWord> m_irqEntries;
	};

	// One scenario = an ordered list of (bank, program) presets. Each gets a slot in which it is
	// written to the edit buffer, played, and modulated. Widening the envelope is a matter of
	// passing more presets, not of writing more code -- which matters, because the honest headline
	// number here is "coverage under THIS envelope", and the envelope must be reportable.
	int runPcCoverage(const std::string& _outPrefix,
		const std::vector<std::pair<int, int>>& _presets,
		uint32_t _slotCallbacks,
		bool _sweepControls,
		uint32_t _maxSamples,
		uint32_t _firstSlot,
		int _watchdogSecs,
		// T12 2026-08-02, ADDITIVE. Live PARAM_CHANGE sends, {page, index, value}, fired once per
		// slot at off == 5/8 of the slot -- i.e. AFTER the CC sweep (off == 1/2) so the sweep
		// cannot clobber the value under test, and BEFORE the note-offs (off == 7/8) so the
		// parameter is in force while voices are still sounding. Empty by default, so a run
		// without --param is bit-identical to every pre-T12 run of this mode.
		const std::vector<std::array<uint8_t, 3>>& _liveParams = {},
		// T19 2026-08-02. Acknowledges that this is a JIT-build CONTROL run (created-block span),
		// not a coverage measurement, and downgrades the g_useJIT refusal from exit 3 to exit 0.
		// It does NOT suppress the sentinel file or set measurement=1 in the .meta -- the run still
		// is not a measurement and the artifacts still say so. All it changes is the exit code.
		bool _jitControl = false,
		// 2026-08-02, ADDITIVE, controls task for P4/P5. Inclusive [lo,hi] P-address ranges to dump
		// from RUNTIME memory at the end of the render, one file per DSP. Empty by default, so a run
		// without --pdump is bit-identical to every earlier run of this mode.
		//
		// WHY THIS EXISTS. Two separate open controls need the same observable and neither could be
		// run without it:
		//   P4 -- work/diffexec_T20 §3 established that the 323 out-of-extent executed addresses
		//         unrelocate into the loaded extent under a SIMULATED relocation. codex's falsify
		//         pass named the missing control: the simulation and the coverage tracker share an
		//         emulator, so a common-mode defect is not excluded. Byte-comparing the RUNTIME
		//         arena against the simulation removes the tracker from the loop entirely.
		//   P5 -- Arm B's null is on an executed-ADDRESS-SET statistic, which cannot distinguish
		//         "no routing change" from "a routing change this statistic cannot see" (e.g. the
		//         built VM program's CONTENT changing at fixed addresses). Dumping P content gives
		//         a second, independent observable over the same arms.
		const std::vector<std::pair<uint32_t, uint32_t>>& _pdumpRanges = {},
		// 2026-08-07, ADDITIVE. --icache-model <base>: enable the DSP56300 instruction-cache model
		// on both DSPs for this run, with <base> as the first CACHEABLE program address. 0 = off,
		// so a run without the flag is bit-identical to every earlier run of this mode.
		//
		// The base is REQUIRED and has no default here for the same reason it has none in
		// DSP::setInstructionCacheModel: it is a per-part, per-OMR/SR property (DSP56367 with the
		// TI2's OMR=$204080/SR=$880000 -> $001c00), and a wrong base silently makes internal
		// program RAM cacheable, which FM Rev. 5 chapter 8 says never happens.
		//
		// The model is INTERPRETER-ONLY and setInstructionCacheModel THROWS in a JIT build, so this
		// flag cannot be used to produce the false-negative reading it exists to avoid: under the
		// JIT no sector is ever allocated (Memory::getOpcode bypasses the cache) and dmaWritesStale
		// would read 0 by construction. The throw is caught below and reported as a refusal.
		dsp56k::TWord _icacheBase = 0)
	{
		auto rom = ROMLoader::findROM(DeviceModel::TI2);
		if (!rom.isValid())
		{
			std::cout << "ROM not found/invalid. Place a valid TI2 firmware .bin next to this executable." << std::endl;
			return 1;
		}

		// The JIT arm of this line was WRONG until 2026-08-02 (T19). It said "onExec does not fire,
		// the coverage number will be ZERO and that is correct". onExec DOES fire under the JIT --
		// DSP::execInterrupt calls it -- and a measured JIT run reports 62,352 retired and 13
		// distinct words on dsp1, 9 on dsp2. Small and nonzero, not zero. That mattered: it is why a
		// "refuse if the number is zero" guard structurally cannot catch a JIT build, and why the
		// g_useJIT refusal at the end of this function needs its own arm.
		std::cout << "pc_coverage: g_useJIT = " << (dsp56k::g_useJIT ? "TRUE (JIT build -- CONTROL ONLY. "
			"onExec fires only from DSP::execInterrupt, so the 'distinct P words' number below is a "
			"dispatched-interrupt-vector count, NOT coverage. This run will be REFUSED unless "
			"--jit-control is given.)"
			: "false (interpreter build -- onExec fires per instruction, this run MEASURES coverage)")
			<< std::endl;

		std::vector<Microcontroller::TPreset> presets;
		std::vector<std::string> presetNames;
		for (const auto& [bank, program] : _presets)
		{
			Microcontroller::TPreset p{};
			if (!rom.getSingle(bank, program, p))
			{
				std::cout << "  preset " << bank << ":" << program << " could not be read, skipping" << std::endl;
				continue;
			}
			presetNames.push_back(ROMFile::getSingleName(p));
			presets.push_back(p);
		}
		if (presets.empty())
		{
			std::cout << "pc_coverage: no usable presets." << std::endl;
			return 1;
		}
		std::cout << "pc_coverage: " << presets.size() << " presets x " << _slotCallbacks
			<< " audio callbacks each" << std::endl;

		// The envelope must be reportable (see this function's header comment), and a live
		// PARAM_CHANGE is part of the envelope. Print it unconditionally, including the empty case,
		// so a log can never be mistaken for the other configuration.
		std::cout << "pc_coverage: liveParams = " << _liveParams.size();
		for (const auto& p : _liveParams)
			std::cout << " [page " << static_cast<int>(p[0]) << " idx " << static_cast<int>(p[1])
				<< " = " << static_cast<int>(p[2]) << "]";
		std::cout << std::endl;

		DspSingle* dsp1raw = nullptr;
		DspSingle* dsp2raw = nullptr;
		virusLib::Device::createDspInstances(dsp1raw, dsp2raw, rom, static_cast<float>(rom.getSamplerate()));
		std::unique_ptr<DspSingle> dsp1(dsp1raw);

		Microcontroller uc(*dsp1, rom, false);
		if (dsp2raw)
			uc.addDSP(*dsp2raw, false);

		// TEMPORARY INSTRUMENTATION 2026-08-01 -- settling the row-81 $8f0000 alias question.
		// Which out-of-range path is actually live depends entirely on Memory::hasMmuSupport():
		//   false -> jitmem.cpp:318 masks offset &= size-1, so $8f0000 aliases Y:$0f0000 (the
		//            "injects live synth memory" story), and Memory::get/dspWrite (interpreter)
		//            return 0 / discard.
		//   true  -> jitmem.cpp:315 skips BOTH the mask and the bounds check; memorybuffer.cpp
		//            has mapped every DSP address above usedAreaSize onto one shared scratch
		//            block, so $8f0000 lands in scratch, NOT in Y:$0f0000. The interpreter still
		//            returns 0 / discards, because Memory::get's bounds check is MMU-blind.
		// Nothing downstream is interpretable until this bit is known, so print it unconditionally.
		for (auto* d : { dsp1.get(), dsp2raw })
		{
			if (!d)
				continue;
			auto& mem = d->getMemory();
			std::cout << "OORPATH " << (d == dsp1.get() ? "dsp1" : "dsp2")
				<< ": hasMmuSupport=" << (mem.hasMmuSupport() ? "TRUE (scratch-alias path)" : "false (mask path)")
				<< " sizeP=$" << std::hex << mem.sizeP()
				<< " sizeXY=$" << mem.sizeXY()
				<< " bridged=$" << mem.getBridgedMemoryAddress()
				<< std::dec << std::endl;
		}

		ExecTracker tracker1(dsp1->getDSP(), "dsp1");
		dsp1->getDSP().setDebugger(&tracker1);
		std::unique_ptr<ExecTracker> tracker2;
		if (dsp2raw)
		{
			tracker2 = std::make_unique<ExecTracker>(dsp2raw->getDSP(), "dsp2");
			dsp2raw->getDSP().setDebugger(tracker2.get());
		}

		// --icache-model. Enabled at exactly the point the debugger is attached -- after
		// createDspInstances and before the DSP threads are driven -- which is the lifetime point
		// this mode has always used and is therefore already known to be race-free here.
		//
		// Printed unconditionally, including the OFF case, so that no log can be mistaken for the
		// other configuration. This is the same rule the liveParams line above follows, and it
		// exists because the counters below are meaningless without knowing whether the model ran.
		if (_icacheBase)
		{
			try
			{
				dsp1->getDSP().setInstructionCacheModel(true, _icacheBase);
				if (dsp2raw)
					dsp2raw->getDSP().setInstructionCacheModel(true, _icacheBase);
			}
			catch (const std::exception& e)
			{
				std::cout << "pc_coverage: --icache-model REFUSED: " << e.what() << std::endl;
				std::cout << "pc_coverage: exiting 4 rather than running with the model off and "
					"reporting counters that would read 0 by construction." << std::endl;
				return 4;
			}
			std::cout << "pc_coverage: icacheModel = ON, first cacheable program address $"
				<< std::hex << _icacheBase << std::dec << std::endl;
		}
		else
		{
			std::cout << "pc_coverage: icacheModel = OFF (ideal always-coherent machine; the "
				"instruction-cache counters printed at the end are NOT a measurement)" << std::endl;
		}

		dsp56k::SpscSemaphore sem(1);
		uint32_t callbackCount = 0;
		int32_t notifyTimeout = 0;
		constexpr uint32_t blockSize = 64;
		const uint32_t notifyThreshold = blockSize > 4 ? blockSize - 4 : 0;
		std::vector<SMidiEvent> midiEvents;
		bool essiDrained = false;
		std::atomic<bool> scenarioDone{false};
		uint32_t lastReportedCb = 0;

		auto& esai = dsp1->getAudio();
		esai.setCallback([&](dsp56k::Audio*)
		{
			const auto availableSize = esai.getAudioOutputs().size();
			const auto sizeReached = availableSize >= notifyThreshold;
			--notifyTimeout;
			if (notifyTimeout <= 0 && sizeReached)
			{
				notifyTimeout = static_cast<int>(notifyThreshold);
				sem.notify();
			}

			++callbackCount;
			if ((callbackCount & 0x3) != 0)
				return;

			uc.readMidiOut(midiEvents);
			const auto cb = callbackCount >> 2;
			uc.process();

			if (cb == 1)
			{
				dsp1->drainESSI1();
				uc.sendInitControlCommands(127);
				return;
			}

			// Slot 0 starts at _firstSlot (default 256, matching pc_trace's proven settle time
			// before the first preset write).
			const uint32_t kFirstSlot = _firstSlot;
			if (cb - lastReportedCb >= 100)
			{
				lastReportedCb = cb;
				std::cout << "  [cb " << cb << "] "
					<< (cb < kFirstSlot ? "settling" : "running") << std::endl;
			}
			if (cb < kFirstSlot)
				return;
			const uint32_t slot = (cb - kFirstSlot) / _slotCallbacks;
			const uint32_t off = (cb - kFirstSlot) % _slotCallbacks;
			if (slot >= presets.size())
			{
				scenarioDone = true;
				return;
			}

			if (off == 0)
			{
				if (!essiDrained)
				{
					dsp1->drainESSI1();
					dsp1->disableESSI1();
					essiDrained = true;
				}
				std::cout << "[cb " << cb << "] slot " << slot << ": preset \"" << presetNames[slot]
					<< "\"" << std::endl;
				uc.writeSingle(BankNumber::EditBuffer, virusLib::SINGLE, presets[slot]);
			}
			else if (off == _slotCallbacks / 8)
			{
				uc.sendMIDI(SMidiEvent(MidiEventSource::Host, 0x90, 60, 0x5f));
				uc.sendPendingMidiEvents(std::numeric_limits<uint32_t>::max());
			}
			else if (off == _slotCallbacks / 4)
			{
				// A second, different-pitch Note On (a chord, not a retrigger) reaches
				// per-voice-index-dependent paths a single voice's lifecycle cannot.
				uc.sendMIDI(SMidiEvent(MidiEventSource::Host, 0x90, 64, 0x5f));
				uc.sendMIDI(SMidiEvent(MidiEventSource::Host, 0x90, 67, 0x40));
				uc.sendPendingMidiEvents(std::numeric_limits<uint32_t>::max());
			}
			else if (_sweepControls && off == _slotCallbacks / 2)
			{
				for (int i = 0; i < 128; ++i)
					uc.sendMIDI(SMidiEvent(MidiEventSource::Host, 0xB0, i, 64));
				uc.sendMIDI(SMidiEvent(MidiEventSource::Host, 0xE0, 0, 64));   // Pitch Bend
				uc.sendMIDI(SMidiEvent(MidiEventSource::Host, 0xD0, 64, 0));   // Channel Pressure
				uc.sendMIDI(SMidiEvent(MidiEventSource::Host, 0xA0, 60, 64));  // Poly Aftertouch
				uc.sendPendingMidiEvents(std::numeric_limits<uint32_t>::max());
			}
			else if (!_liveParams.empty() && off == (_slotCallbacks * 5) / 8)
			{
				// T12 2026-08-02. Live PARAM_CHANGE, same wire shape as runChorusPcTrace's
				// sendLiveParam (xmemProbe.cpp, the cb1200 branch) and as tools/sweep_params.py:
				//   F0 00 20 33 01 00 <page> <SINGLE=0x40> <index> <value> F7
				// A bulk edit-buffer write does NOT reconfigure every subsystem
				// (work/dsp_chorus_live_program_matrix_findings.md), so baking the byte into the
				// TPreset is not equivalent to this and must not be substituted for it.
				for (const auto& p : _liveParams)
				{
					std::cout << "[cb " << cb << "] slot " << slot << ": live PARAM_CHANGE page "
						<< static_cast<int>(p[0]) << " idx " << static_cast<int>(p[1])
						<< " = " << static_cast<int>(p[2]) << std::endl;
					synthLib::SysexBuffer sysex{
						0xf0, 0x00, 0x20, 0x33, 0x01, 0x00,
						p[0], virusLib::SINGLE, p[1], p[2],
						0xf7
					};
					std::vector<SMidiEvent> responses;
					uc.sendSysex(sysex, responses, MidiEventSource::Host);
				}
			}
			else if (off == (_slotCallbacks * 7) / 8)
			{
				// Release the voices so the release/voice-steal paths run before the next preset.
				uc.sendMIDI(SMidiEvent(MidiEventSource::Host, 0x80, 60, 0));
				uc.sendMIDI(SMidiEvent(MidiEventSource::Host, 0x80, 64, 0));
				uc.sendMIDI(SMidiEvent(MidiEventSource::Host, 0x80, 67, 0));
				uc.sendPendingMidiEvents(std::numeric_limits<uint32_t>::max());
			}
		});

		virusLib::Device::bootDSPs(dsp1.get(), dsp2raw, rom, false);

		// The render ends when the SCHEDULE completes, not at a precomputed sample count. The
		// ESAI-callback-to-sample ratio is not 1:1 and is not worth deriving: an earlier version of
		// this mode computed the sample count from the schedule, came up ~4x short, and rendered a
		// whole run in which the first preset was never sent. _maxSamples is only a backstop against
		// a DSP that stops producing audio, and it is deliberately generous.
		const uint32_t maxSamples = _maxSamples ? _maxSamples
			: (_firstSlot + _slotCallbacks * static_cast<uint32_t>(presets.size()) + 128) * blockSize * 8;
		std::cout << "Booted. Driving the schedule to completion (backstop " << maxSamples
			<< " samples = " << (static_cast<double>(maxSamples) / rom.getSamplerate())
			<< " s of DSP time)..." << std::endl;

		// The rendered audio is written out so a JIT-vs-interpreter bit-comparison can be run as a
		// fidelity control: if the two builds do not produce identical audio for an identical
		// scenario, they are not the same machine and the interpreter's coverage is about a
		// different program.
		// Watchdog (2026-08-01). The interpreter build boots and then stops making progress; "it
		// hangs" is not a diagnosis, so this thread reports, every _watchdogSecs, whether the DSP
		// cores are retiring instructions at all, which P address they are retiring them AT, and
		// the exact recent instruction sequence. A spinning-but-retiring core is a firmware poll
		// loop; a non-retiring core is a host-side block.
		std::atomic<bool> watchdogRun{true};
		std::thread watchdog;
		if (_watchdogSecs)
		{
			watchdog = std::thread([&]
			{
				uint64_t prev1 = 0, prev2 = 0;
				while (watchdogRun)
				{
					for (int i = 0; i < _watchdogSecs * 10 && watchdogRun; ++i)
						std::this_thread::sleep_for(std::chrono::milliseconds(100));
					if (!watchdogRun)
						break;
					const uint64_t e1 = tracker1.m_execCount;
					const uint64_t e2 = tracker2 ? tracker2->m_execCount : 0;
					std::cout << "[watchdog] cb=" << callbackCount
						<< " dsp1 +" << (e1 - prev1) << " (pc $" << std::hex
						<< dsp1->getDSP().getPC().toWord() << std::dec << ")"
						<< " dsp2 +" << (e2 - prev2);
					if (dsp2raw)
						std::cout << " (pc $" << std::hex << dsp2raw->getDSP().getPC().toWord() << std::dec << ")";
					// ESAI state, because the interpreter hang is a firmware spin on the ESAI
					// transmit-frame-sync bit: knowing whether TFS is toggling at all separates
					// "the peripheral is not being clocked" from "it is clocked and the firmware
					// is waiting for something else".
					{
						auto& p1 = dsp1->getPeriphX();
						std::cout << "\n  esai1 TFS=" << p1.getEsai().getTransmitFrameSync()
							<< " tem=" << std::hex << p1.getEsai().hasEnabledTransmitters() << std::dec
							<< " outQ=" << p1.getEsai().getAudioOutputs().size()
							<< " inQ=" << p1.getEsai().getAudioInputs().size()
							<< " ictr=" << dsp1->getDSP().getInstructionCounter()
							<< " remFS=" << p1.getEsaiClock().getRemainingInstructionsForFrameSync()
							<< " txFrames=" << p1.getEsai().getTxFrameCounter()
							<< " txWordCount=" << p1.getEsai().getTxWordCount();
					}
					std::cout << "\n  dsp1 hot:" << tracker1.hotspot(6)
						<< "\n  dsp1 recent:" << tracker1.recentLoop(24);
					if (tracker2)
						std::cout << "\n  dsp2 hot:" << tracker2->hotspot(6)
							<< "\n  dsp2 recent:" << tracker2->recentLoop(24);
					std::cout << std::dec << std::endl;
					prev1 = e1;
					prev2 = e2;
				}
			});
		}

		AudioProcessor proc(rom.getSamplerate(), _outPrefix + ".wav", false, maxSamples, dsp1.get(), dsp2raw);
		while (!proc.finished() && !scenarioDone)
		{
			sem.wait();
			proc.processBlock(blockSize);
		}
		watchdogRun = false;
		if (watchdog.joinable())
			watchdog.join();
		if (!scenarioDone)
			std::cout << "WARNING: the sample backstop fired before the schedule completed. This run's "
				"envelope is NOT the one requested -- do not report its coverage as such." << std::endl;

		dsp1->getDSP().setDebugger(nullptr);
		if (dsp2raw)
			dsp2raw->getDSP().setDebugger(nullptr);

		// --- instruction-cache counters, 2026-08-07 ------------------------------------------
		//
		// dmaWritesToP answers the question left open on 2026-08-03 (work/icache_selfmod_coherency
		// section "Next step"): does any DMA channel in the TI2 firmware EVER target program space?
		// It is counted with the model off and outside the CE/base gate (dsp.cpp), so a 0 here is
		// unambiguous -- it does not mean "below the cacheable base" or "with CE clear".
		//
		// dmaWritesStale is the only counter that requires the model, and it requires a FETCH to
		// have allocated the sector first, so `fetches` is printed next to it as the anti-vacuity
		// number. fetches == 0 with the model on means the run never fetched a cacheable address
		// and the staleness figure says nothing at all. That combination is what a JIT build would
		// have produced silently before setInstructionCacheModel started refusing one.
		for (auto* d : { dsp1.get(), dsp2raw })
		{
			if (!d)
				continue;
			const auto& s = d->getDSP().getInstructionCacheStats();
			const bool on = d->getDSP().getInstructionCacheModel();
			std::cout << "ICACHE " << (d == dsp1.get() ? "dsp1" : "dsp2")
				<< ": model=" << (on ? "ON" : "off")
				<< " fetches=" << s.fetches
				<< " fetchHits=" << s.fetchHits
				<< " pmovewHits=" << s.pmovewHits
				<< " pmovewMisses=" << s.pmovewMisses
				<< " dmaWritesToP=" << s.dmaWritesToP
				<< " dmaWritesToPCacheable=" << s.dmaWritesToPCacheable
				<< " dmaWritesToPResident=" << s.dmaWritesToPResident
				<< " dmaWritesStale=" << s.dmaWritesStale
				<< std::hex << " dmaWriteToPRange=$" << s.dmaWriteToPMin << "-$" << s.dmaWriteToPMax << std::dec
				<< " pflush=" << s.pflush
				<< " pflushun=" << s.pflushun
				<< " pfree=" << s.pfree
				<< " plock=" << s.plock
				<< " punlock=" << s.punlock
				<< std::endl;

			if (on && s.fetches == 0)
				std::cout << "ICACHE " << (d == dsp1.get() ? "dsp1" : "dsp2")
					<< ": VACUOUS -- the model was on but no cacheable address was ever fetched, so "
					"dmaWritesStale=" << s.dmaWritesStale << " is a fact about this run's reach, "
					"not about the firmware." << std::endl;
		}

		// TEMPORARY INSTRUMENTATION 2026-08-01 -- the measurement the claim ledger names as the
		// one that settles row 81: is the alias target nonzero at the end of a render?
		// Dumps BOTH candidate targets so the answer does not depend on which path this build took:
		//   $0f0000+ (in-range, the mask path's target) and, only when the MMU mapping exists,
		//   $8f0000+ (the scratch block the JIT would actually touch). 705 words = $8f0000-$8f02c0.
		// Written to a file so two runs can be byte-compared as an A/A determinism control -- the
		// render was shown nondeterministic on 2026-08-01, which invalidated four earlier
		// conclusions drawn from A/B comparisons that never established reproducibility first.
		{
			const char* aliasOut = std::getenv("OOR_ALIAS_DUMP");
			if (aliasOut && *aliasOut)
			{
				std::ofstream dump(aliasOut);
				dump << std::hex << std::setfill('0');
				for (auto* d : { dsp1.get(), dsp2raw })
				{
					if (!d)
						continue;
					const std::string label = (d == dsp1.get()) ? "dsp1" : "dsp2";
					auto& mem = d->getMemory();
					struct Target { const char* name; dsp56k::TWord base; bool needsMmu; };
					const Target targets[] = {
						{ "Y:$0f0000", 0x0f0000, false },
						{ "X:$0f0000", 0x0f0000, false },
						{ "Y:$8f0000", 0x8f0000, true  },
						{ "X:$8f0000", 0x8f0000, true  },
					};
					for (size_t ti = 0; ti < 4; ++ti)
					{
						const auto& t = targets[ti];
						if (t.needsMmu && !mem.hasMmuSupport())
						{
							dump << label << " " << t.name << " SKIPPED (no MMU mapping; "
								"this address is outside the allocated buffer)\n";
							continue;
						}
						const auto area = (ti & 1) ? dsp56k::MemArea_X : dsp56k::MemArea_Y;
						const dsp56k::TWord* base = mem.getMemAreaPtr(area) + t.base;
						size_t nonZero = 0;
						for (dsp56k::TWord i = 0; i < 705; ++i)
							if (base[i])
								++nonZero;
						dump << label << " " << t.name << "-+$2c0  nonzero=" << std::dec << nonZero
							<< "/705  words:" << std::hex;
						for (dsp56k::TWord i = 0; i < 705; ++i)
							dump << " " << std::setw(6) << base[i];
						dump << "\n";
						std::cout << "ALIASDUMP " << label << " " << t.name << " nonzero="
							<< std::dec << nonZero << "/705" << std::endl;
					}
				}
			}
		}

		// -----------------------------------------------------------------------------------------
		// RUNTIME P-MEMORY DUMP (--pdump), 2026-08-02. See the _pdumpRanges parameter comment for
		// why. Written as raw 24-bit big-endian words, ranges concatenated in the order given, so a
		// consumer can byte-compare two runs with cmp(1) and index a word by ordinal without a
		// parser. A sidecar .meta records the ranges and the nonzero count.
		//
		// FAIL-LOUD, per doc/instrument_defects.md class 23: a dump that is entirely zero is the
		// exact shape of "the instrument ran and measured nothing", and for the arena range it is
		// also the shape of "the boot relocator never ran". It cannot be a hard refusal because a
		// caller may legitimately request a range that IS zero -- so it writes a sentinel file and
		// prints a PDUMP-ALL-ZERO line, and the downstream comparator is required to treat that as
		// INCONCLUSIVE rather than as agreement.
		if (!_pdumpRanges.empty())
		{
			for (auto* d : { dsp1.get(), dsp2raw })
			{
				if (!d)
					continue;
				const std::string label = (d == dsp1.get()) ? "dsp1" : "dsp2";
				auto& mem = d->getMemory();
				const dsp56k::TWord* p = mem.getMemAreaPtr(dsp56k::MemArea_P);
				const std::string binPath = _outPrefix + "." + label + ".pdump";
				std::ofstream bin(binPath, std::ios::binary);
				size_t nWords = 0, nNonZero = 0, nOutOfRange = 0;
				for (const auto& r : _pdumpRanges)
				{
					for (uint32_t a = r.first; a <= r.second; ++a)
					{
						dsp56k::TWord w = 0;
						if (a < mem.sizeP())
							w = p[a];
						else
							++nOutOfRange;
						const char b3[3] = {
							static_cast<char>((w >> 16) & 0xff),
							static_cast<char>((w >> 8) & 0xff),
							static_cast<char>(w & 0xff) };
						bin.write(b3, 3);
						++nWords;
						if (w)
							++nNonZero;
					}
				}
				bin.close();

				{
					std::ofstream meta(_outPrefix + "." + label + ".pdump.meta");
					meta << "tool=xmemProbe/pc_coverage/pdump\n"
						<< "label=" << label << "\n"
						<< "sizeP=" << std::dec << mem.sizeP() << "\n"
						<< "words=" << nWords << "\n"
						<< "nonzero=" << nNonZero << "\n"
						<< "outofrange=" << nOutOfRange << "\n";
					for (const auto& r : _pdumpRanges)
						meta << "range=" << std::hex << r.first << ":" << r.second << std::dec << "\n";
				}

				const std::string zeroSentinel = _outPrefix + "." + label + ".PDUMP-ALL-ZERO";
				std::remove(zeroSentinel.c_str());
				if (nWords && !nNonZero)
				{
					std::ofstream sen(zeroSentinel);
					sen << "every one of " << std::dec << nWords << " dumped P words is zero.\n"
						<< "Do not read " << binPath << " as agreement with anything.\n";
					sen.close();
					std::cout << "PDUMP-ALL-ZERO " << label << ": " << std::dec << nWords
						<< " words, all zero -- this dump measures nothing" << std::endl;
				}
				std::cout << "PDUMP " << label << ": " << std::dec << nWords << " words, "
					<< nNonZero << " nonzero, " << nOutOfRange << " out of P range -> "
					<< binPath << std::endl;
			}
		}

		// -----------------------------------------------------------------------------------------
		// FAIL CLOSED (T19, 2026-08-02). Everything above this point ran happily earlier the same day
		// on a build whose DebuggerInterface call sites had been compiled out. It printed
		// "g_useJIT = false ... this run MEASURES coverage", rendered a real 25,004-byte wav, wrote
		// all six output files, reported "retired 0 instructions" with an all-zero 1 MiB bitmap on
		// BOTH DSPs -- and exited 0. That is doc/instrument_defects.md class 23 occurring inside the
		// very tool the class was written about, and it silently invalidated a cited 12,766-word
		// result from 2026-08-01.
		//
		// Three conditions, each meaning "this run is not a coverage measurement", each of which
		// previously exited 0 and printed a number a downstream reader would have used:
		//
		//   1. retired == 0            -- onExec never fired. The hooks are compiled out, or the
		//                                 scenario never advanced the DSP. Either way there is
		//                                 nothing here.
		//   2. distinct == 0           -- the bitmap is entirely zero.
		//   3. g_useJIT                -- the refusal this function's header comment claimed since
		//                                 2026-07-31 and did not have. It needs its OWN arm because
		//                                 a JIT run does not report zero (13 / 9 words, via
		//                                 execInterrupt), so arms 1 and 2 structurally cannot catch
		//                                 it. Opt out with --jit-control when a JIT run is a
		//                                 deliberate created-block-span control -- the opt-out must
		//                                 be typed on the command line so that a control run is a
		//                                 decision visible in the log, not a default.
		//
		// TWO THINGS TRAVEL WITH THE ARTIFACT, not just with stdout, because this mode's stdout is
		// ~106k lines of interleaved "DSP 56300 ERROR: Memory Read" and the summary line is not
		// reliably parseable out of it (work/diffexec_T1_instrument_readiness_2026-08-02.md S5):
		//   - "<prefix>.<label>.meta", key=value, machine-readable, always written;
		//   - "<prefix>.<label>.NOT-A-COVERAGE-MEASUREMENT", written ONLY when the run is not one.
		// A consumer that reads neither stdout nor the exit code still trips over the sentinel.
		// tools/pc_coverage_gate.py enforces all of it from outside, so artifacts produced by an
		// older binary can be checked too.
		std::vector<std::string> refusals;
		for (auto* t : { &tracker1, tracker2.get() })
		{
			if (!t)
				continue;
			const uint64_t retired = t->m_execCount;
			const size_t distinct = t->distinctExecuted();
			const bool isMeasurement = !dsp56k::g_useJIT && retired > 0 && distinct > 0;

			const std::string binPath = _outPrefix + "." + t->m_label + ".cov";
			std::ofstream bin(binPath, std::ios::binary);
			bin.write(reinterpret_cast<const char*>(t->m_executed.data()),
				static_cast<std::streamsize>(t->m_executed.size()));
			bin.close();

			const std::string spanPath = _outPrefix + "." + t->m_label + ".jitspan";
			std::ofstream span(spanPath);
			for (const auto a : t->m_blockSpan)
				span << std::hex << a << "\n";
			span.close();

			const std::string irqPath = _outPrefix + "." + t->m_label + ".irqentry";
			std::ofstream irq(irqPath);
			for (const auto a : t->m_irqEntries)
				irq << std::hex << a << "\n";
			irq.close();

			const std::string metaPath = _outPrefix + "." + t->m_label + ".meta";
			{
				std::ofstream meta(metaPath);
				meta << "tool=xmemProbe/pc_coverage\n"
					<< "label=" << t->m_label << "\n"
					<< "g_useJIT=" << (dsp56k::g_useJIT ? 1 : 0) << "\n"
					<< "retired=" << std::dec << retired << "\n"
					<< "distinct=" << distinct << "\n"
					<< "covbytes=" << t->m_executed.size() << "\n"
					<< "outofrange=" << t->m_outOfRange << "\n"
					<< "jitblocks=" << t->m_blockStarts.size() << "\n"
					<< "jitspanwords=" << t->m_blockSpan.size() << "\n"
					<< "irqentries=" << t->m_irqEntries.size() << "\n"
					<< "measurement=" << (isMeasurement ? 1 : 0) << "\n";
			}

			const std::string sentinelPath = _outPrefix + "." + t->m_label + ".NOT-A-COVERAGE-MEASUREMENT";
			std::remove(sentinelPath.c_str());   // a rerun into the same prefix must not inherit one

			std::cout << t->m_label
				<< ": retired " << std::dec << retired << " instructions, "
				<< distinct << " distinct P words executed, "
				<< t->m_outOfRange << " out-of-range PCs (min $" << std::hex << t->m_outOfRangeMin
				<< " max $" << t->m_outOfRangeMax << std::dec << "), "
				<< t->m_blockStarts.size() << " JIT blocks created, "
				<< t->m_blockSpan.size() << " words in created-block spans, "
				<< t->m_irqEntries.size() << " dispatched interrupt entries" << std::endl;
			std::cout << "  wrote " << binPath << ", " << spanPath << ", " << irqPath
				<< " and " << metaPath << std::endl;

			if (!isMeasurement)
			{
				std::string why;
				if (dsp56k::g_useJIT)
					why = "JIT build -- onExec fires only from DSP::execInterrupt, so this bitmap is a "
						"dispatched-interrupt-vector set and NOT execution coverage";
				else if (retired == 0)
					why = "retired 0 instructions -- DebuggerInterface::onExec never fired. Almost "
						"certainly a build with DSP56K_DEBUGGER_HOOKS off, which is silent at "
						"runtime: the render still happens and every output file is still written";
				else
					why = "coverage bitmap is entirely zero";

				std::ofstream sen(sentinelPath);
				sen << why << "\n"
					<< "retired=" << std::dec << retired << " distinct=" << distinct
					<< " g_useJIT=" << (dsp56k::g_useJIT ? 1 : 0) << "\n"
					<< "Do not read " << binPath << " as a coverage measurement.\n";
				sen.close();

				refusals.push_back(t->m_label + ": " + why);
			}
		}

		if (!refusals.empty())
		{
			const bool jitOnly = dsp56k::g_useJIT;
			for (const auto& r : refusals)
				std::cout << "pc_coverage: REFUSED -- " << r << std::endl;
			if (jitOnly && _jitControl)
			{
				std::cout << "pc_coverage: --jit-control given; treating this as a deliberate "
					"created-block-span control run, NOT a coverage measurement. Exit 0." << std::endl;
				return 0;
			}
			std::cout << "pc_coverage: this run is NOT a coverage measurement. Exiting 3. "
				"Any number printed above is void." << std::endl;
			return 3;
		}
		return 0;
	}
	// "chorus_pc_trace" mode: plan.md's addendum-diffing item #2 -- xmemProbe's pc_trace capability
	// (proven in work/dsp_pc_trace_findings.md) run differentially across Chorus Type values, to
	// find which DSP2 P-memory blocks get JIT-compiled for Hyper Chorus (type 3) or Air Chorus
	// (type 4) but NOT for Classic (type 1), directly settling per-feature identity for the
	// addendum's OS 4.5 diff zone (work/addendum_version_diff_findings.md's medium-confidence
	// func_05c9e8-neighborhood correlation) without the static cross-version address translation
	// that finding's caveat flagged as unattempted. work/chorus_type_findings.md already found
	// Classic/Vintage/Vibrato/Rotary share one DSP2_X:$1F41 dispatch-pointer value ($25C3FD) while
	// Hyper ($25C3FB) and Air ($25C5A6) get distinct ones from a live memory diff -- this mode
	// answers the separate question of which *code* actually executes, independent of how that
	// stored value should be interpreted (not itself verified as a literal P-address here). Chorus
	// type is a CLI argument so the caller runs type=1 (baseline) then type=3/4 (test) as separate
	// invocations and diffs the resulting block-start dumps externally.
	// _distortionType/_characterType: addendum-diffing follow-up (plan.md's "byte-level reading of
	// the OS 4.0 boundary" item) -- same reuse pattern as _filterBankType, testing whether the OS
	// 4.0/3.3 Distortion "Types" (Mint..Chili Overdrive idx 20-25, Wide..Bit Reducer idx 12-19) or
	// the Speaker Cabinet Character Type (idx 8) get their own dedicated P-memory code, or reuse
	// pre-existing generic engine code the way Chorus/Filter Bank types already were shown to.
	int runChorusPcTrace(int _chorusType, const std::string& _outFile, bool _sendNotes = true, int _filterBankType = -1,
		int _distortionType = -1, int _characterType = -1, int _modMatrixSource = -1, bool _dumpBuildArea = false,
		const std::vector<std::array<uint8_t, 3>>& _liveParams = {}, int _arpMode = -1)
	{
		auto rom = ROMLoader::findROM(DeviceModel::TI2);
		if (!rom.isValid())
		{
			std::cout << "ROM not found/invalid. Place a valid TI2 firmware .bin next to this executable." << std::endl;
			return 1;
		}

		Microcontroller::TPreset preset{};
		// bank 11/124 "VocoPad XM" -- same base preset work/chorus_type_findings.md's own sweep
		// used, proven to actually engage the DSP2_X:$1F41 dispatch pointer (an earlier attempt
		// with bank 1/0 "64Degee MS" left X:$1F41 at $0 the whole render -- Chorus never actually
		// engaged, silently making that run's "identical block sets" result meaningless).
		rom.getSingle(11, 124, preset);
		std::cout << "Using preset \"" << ROMFile::getSingleName(preset) << "\" as chorus_pc_trace base, "
			"Chorus Type=" << _chorusType << std::endl;
		if (preset.size() > 276)
			std::cout << "  (factory Filter Bank Type=" << static_cast<int>(preset[275])
				<< " Mix=" << static_cast<int>(preset[276]) << ")" << std::endl;
		if (_filterBankType >= 0 && preset.size() > 276)
		{
			preset[275] = static_cast<uint8_t>(_filterBankType); // Filter Bank/Type
			preset[276] = 127;                                   // Filter Bank/Mix -- full on
			std::cout << "  Overriding Filter Bank Type=" << _filterBankType << " Mix=127" << std::endl;
		}

		// Reusing "sweep" mode's exact FX-defaults block verbatim (not just the Chorus fields) --
		// a first attempt at just the 4 Chorus fields left DSP2_X:$1F41 at $0 for the *entire*
		// render even with Type=1/preset bank 11/124, contradicting work/chorus_type_findings.md's
		// own report of real nonzero per-type values there. Since that finding was produced via
		// tools/sweep_params.py -> xmemProbe "sweep" mode, which bakes in this exact multi-effect
		// defaults block (Reverb/Distortion/Delay/Phaser all forced on, not just Chorus) before
		// overwriting the swept parameter, matching it exactly first is the safest way to reproduce
		// the known-good result before narrowing down which piece was actually necessary.
		if (preset.size() >= 305)
		{
			preset[257] = 1;  // Reverb Mode = 1 (on)
			preset[258] = 64; // Reverb Send
			preset[259] = 0;  // Reverb Type
			preset[260] = 64; // Reverb Time
			preset[261] = 10; // Reverb Damping
			preset[262] = 64; // Reverb Color
			preset[265] = 10; // Reverb Predelay

			preset[103] = static_cast<uint8_t>(_chorusType); // Chorus/Type
			preset[105] = 64; // Chorus Mix
			preset[106] = 43; // Chorus Rate
			preset[107] = 64; // Chorus Depth
			preset[108] = 32; // Chorus Delay

			preset[228] = 1;   // Distortion Curve
			preset[229] = 64;  // Distortion Intensity
			preset[328] = 127; // Distortion Mix

			preset[112] = 1;  // Delay Mode
			preset[113] = 64; // Delay Send
			preset[114] = 64; // Delay Time
			preset[116] = 64; // Delay Feedback

			preset[212] = 3;   // Phaser Mode
			preset[213] = 64;  // Phaser Mix
			preset[214] = 36;  // Phaser Rate
			preset[215] = 112; // Phaser Depth
			preset[216] = 64;  // Phaser Frequency
		}

		// Page_B (0x71) offset base 128 + param -- confirmed via virusLib's own
		// Microcontroller::applyToSingleEditBuffer formula (offset = pageOffset*128 + param,
		// PAGE_B -> pageOffset 1), matching the existing preset[228]="Distortion Curve" (page
		// 113/0x71 idx 100) constant above.
		if (_distortionType >= 0 && preset.size() > 328)
		{
			preset[228] = static_cast<uint8_t>(_distortionType); // Distortion Curve
			preset[229] = 64;                                    // Distortion Intensity
			preset[328] = 127;                                   // Distortion Mix
			std::cout << "  Overriding Distortion Curve=" << _distortionType << std::endl;
		}

		// Page_6E (0x6E/110) offset base 256 + param, same formula -- Character Type is page
		// 110 idx 26, same page as Filter Bank/Type (idx 19 -> preset[275]) above, so
		// preset[256+26]=preset[282].
		if (_characterType >= 0 && preset.size() > 282)
		{
			preset[282] = static_cast<uint8_t>(_characterType); // Character Type
			std::cout << "  Overriding Character Type=" << _characterType << std::endl;
		}

		// Mod Matrix Slot 1: Assign1 Source (page 113/0x71 idx 64 -> preset[192]) / Destination
		// (idx 65 -> preset[193]) / Amount (idx 66 -> preset[194]). Tests OS 4.5's 9 new sources
		// (LFO 1/2/3 unipolar=29-31, 1%/10% constant=32-33, AnaKey1/2 Fine/Coarse=34-37) against an
		// always-live destination (Filter 1 Cutoff=24, independently confirmed reachable via
		// tools/sweep_params.py's X:$49BB2 mapping) with a real nonzero Amount.
		if (_modMatrixSource >= 0 && preset.size() > 194)
		{
			preset[192] = static_cast<uint8_t>(_modMatrixSource); // Assign1 Source
			preset[193] = 24;                                     // Assign1 Destination = Filter 1 Cutoff
			preset[194] = 127;                                    // Assign1 Amount
			std::cout << "  Overriding Mod Matrix Slot 1 Source=" << _modMatrixSource << " Dest=24 Amount=127" << std::endl;
		}

		// Site 1 part-2 probe (work/dsp_site1_live_trigger_part2_findings.md): Arp Mode baked into
		// the BULK preset write (before either Note On), same "rule out a read-only-at-note-on/
		// arp-state-latched-before-my-live-SysEx-arrived timing confound" rationale the predecessor
		// session already applied to the Mod Matrix "Random" source above via modsource_pc_trace.
		// Page 113/0x71 idx 15 = Arp Mode -> PAGE_B offset 128+15 = preset[143]; value 5 = "Random"
		// in the arpModes enum (Off/Up/Down/Up&Down/AsPlayed/Random/Chord/Arp>Matrix).
		if (_arpMode >= 0 && preset.size() > 143)
		{
			preset[143] = static_cast<uint8_t>(_arpMode); // Arp Mode
			std::cout << "  Overriding Arp Mode (baked into bulk preset)=" << _arpMode << std::endl;
		}

		DspSingle* dsp1raw = nullptr;
		DspSingle* dsp2raw = nullptr;
		virusLib::Device::createDspInstances(dsp1raw, dsp2raw, rom, static_cast<float>(rom.getSamplerate()));
		std::unique_ptr<DspSingle> dsp1(dsp1raw);

		Microcontroller uc(*dsp1, rom, false);
		if (dsp2raw)
			uc.addDSP(*dsp2raw, false);

		AddrTracker tracker1(dsp1->getDSP(), "dsp1");
		dsp1->getDSP().setDebugger(&tracker1);
		std::unique_ptr<AddrTracker> tracker2;
		if (dsp2raw)
		{
			tracker2 = std::make_unique<AddrTracker>(dsp2raw->getDSP(), "dsp2");
			dsp2raw->getDSP().setDebugger(tracker2.get());
		}

		dsp56k::SpscSemaphore sem(1);
		uint32_t callbackCount = 0;
		int32_t notifyTimeout = 0;
		constexpr uint32_t blockSize = 64;
		const uint32_t notifyThreshold = blockSize > 4 ? blockSize - 4 : 0;
		std::vector<SMidiEvent> midiEvents;

		bool presetSent = false, noteSent = false, secondNoteSent = false, liveChorusTypeSent = false;

		auto& esai = dsp1->getAudio();
		esai.setCallback([&](dsp56k::Audio*)
		{
			const auto availableSize = esai.getAudioOutputs().size();
			const auto sizeReached = availableSize >= notifyThreshold;
			--notifyTimeout;
			if (notifyTimeout <= 0 && sizeReached)
			{
				notifyTimeout = static_cast<int>(notifyThreshold);
				sem.notify();
			}

			++callbackCount;
			if ((callbackCount & 0x3) != 0)
				return;

			uc.readMidiOut(midiEvents);
			const auto audioCallbackCount = callbackCount >> 2;
			uc.process();

			if (audioCallbackCount == 1)
			{
				dsp1->drainESSI1();
				uc.sendInitControlCommands(127);
			}
			else if (audioCallbackCount == 256 && !presetSent)
			{
				dsp1->drainESSI1();
				dsp1->disableESSI1();
				std::cout << "[cb " << audioCallbackCount << "] Sending preset" << std::endl;
				uc.writeSingle(BankNumber::EditBuffer, virusLib::SINGLE, preset);
				presetSent = true;
			}
			else if (audioCallbackCount == 512 && !noteSent && _sendNotes)
			{
				std::cout << "[cb " << audioCallbackCount << "] Sending Note On" << std::endl;
				uc.sendMIDI(SMidiEvent(MidiEventSource::Host, 0x90, 60, 0x5f));
				uc.sendPendingMidiEvents(std::numeric_limits<uint32_t>::max());
				noteSent = true;
			}
			else if (audioCallbackCount == 900 && !secondNoteSent && _sendNotes)
			{
				std::cout << "[cb " << audioCallbackCount << "] Sending second Note On (note 64)" << std::endl;
				uc.sendMIDI(SMidiEvent(MidiEventSource::Host, 0x90, 64, 0x5f));
				uc.sendPendingMidiEvents(std::numeric_limits<uint32_t>::max());
				secondNoteSent = true;
			}
			else if (audioCallbackCount == 1200 && !_liveParams.empty() && !liveChorusTypeSent)
			{
				// The bulk edit-buffer preset write above demonstrably does NOT reconfigure the
				// chorus (full DSP2 X+Y state identical between Hyper/Air runs except the 1-word
				// type cell X/Y:$4C4F6, work/dsp_chorus_live_program_matrix_findings.md) -- send
				// the parameters as live PARAM_CHANGEs (same SysEx shape as vm_watch's
				// sendLiveParam), the path real editors and tools/sweep_params.py use, which
				// actually triggers the effect-rebuild.
				for (const auto& p : _liveParams)
				{
					std::cout << "[cb " << audioCallbackCount << "] Sending live PARAM_CHANGE page $"
						<< std::hex << static_cast<int>(p[0]) << std::dec << " idx " << static_cast<int>(p[1])
						<< " = " << static_cast<int>(p[2]) << std::endl;
					synthLib::SysexBuffer sysex{
						0xf0, 0x00, 0x20, 0x33, 0x01, 0x00,
						p[0], virusLib::SINGLE, p[1], p[2],
						0xf7
					};
					std::vector<SMidiEvent> responses;
					uc.sendSysex(sysex, responses, MidiEventSource::Host);
				}
				liveChorusTypeSent = true;
			}
		});

		virusLib::Device::bootDSPs(dsp1.get(), dsp2raw, rom, false);

		// Register the DSP memory buffers so the SIGBUS/SIGSEGV handler can map a
		// firmware-computed out-of-range access back to a DSP (area, offset). X/Y/P share
		// one buffer per DSP; registering the X base + the P area's end covers the whole span.
		installFaultHandler();
		g_faultDsp1 = &dsp1->getDSP();
		if (dsp2raw) g_faultDsp2 = &dsp2raw->getDSP();
		registerMemRange("dsp1_X", dsp1->getMemory().getMemAreaPtr(dsp56k::MemArea_X), 0x100000);
		registerMemRange("dsp1_Y", dsp1->getMemory().getMemAreaPtr(dsp56k::MemArea_Y), 0x100000);
		registerMemRange("dsp1_P", dsp1->getMemory().getMemAreaPtr(dsp56k::MemArea_P), 0x100000);
		if (dsp2raw)
		{
			registerMemRange("dsp2_X", dsp2raw->getMemory().getMemAreaPtr(dsp56k::MemArea_X), 0x100000);
			registerMemRange("dsp2_Y", dsp2raw->getMemory().getMemAreaPtr(dsp56k::MemArea_Y), 0x100000);
			registerMemRange("dsp2_P", dsp2raw->getMemory().getMemAreaPtr(dsp56k::MemArea_P), 0x100000);
		}

		constexpr uint32_t kTotalSamples = 8 * 44100; // matches "sweep" mode's proven render duration
		std::cout << "Booted. Rendering " << kTotalSamples << " samples (~8s), Chorus Type=" << _chorusType
			<< ", sendNotes=" << _sendNotes
			<< ", tracking every JIT-compiled block's P-memory range on both DSPs..." << std::endl;

		AudioProcessor proc(rom.getSamplerate(), "xmem_chorus_pc_trace_throwaway.wav", false, kTotalSamples, dsp1.get(), dsp2raw);
		while (!proc.finished())
		{
			sem.wait();
			proc.processBlock(blockSize);
		}

		dsp1->getDSP().setDebugger(nullptr);
		if (dsp2raw)
			dsp2raw->getDSP().setDebugger(nullptr);

		std::ofstream out(_outFile);
		out << "Mode: chorus_pc_trace, Chorus Type=" << _chorusType
			<< " (JIT-block coverage over ~4s: preset load, 2 notes)\n";
		if (_filterBankType >= 0)
			out << "  Filter Bank Type override=" << _filterBankType << "\n";
		if (_distortionType >= 0)
			out << "  Distortion Curve override=" << _distortionType << "\n";
		if (_characterType >= 0)
			out << "  Character Type override=" << _characterType << "\n";
		if (_modMatrixSource >= 0)
			out << "  Mod Matrix Slot 1 Source override=" << _modMatrixSource << " (Dest=24 Filter 1 Cutoff, Amount=127)\n";
		if (_arpMode >= 0)
			out << "  Arp Mode override=" << _arpMode << " (baked into bulk preset, preset[143])\n";
		out << "\n";

		// NOT A SANITY CHECK. The label that stood here until 2026-08-12 printed a VALIDITY
		// VERDICT this cell cannot support, and the value it printed was correct the whole time --
		// the number was right and the sentence a reader acts on was false.
		//
		// The retired comment read: "DSP2_X:$1F41 should hold a distinct value per chorus type
		// ($25C3FD classic/vintage/vibrato/rotary, $25C3FB hyper, $25C5A6 air) -- confirms the
		// preset[103] write above actually took effect before trusting a 'block sets are
		// identical' result as meaningful rather than a silently-inert sweep." Every clause of
		// that is superseded, and the correction is already in THIS FILE twelve lines below, in
		// the chorus_buildarea block, where it has sat since 2026-07-17 without reaching here:
		//
		//   * X:$1F41 is a ROTATING CURRENT-SLOT POINTER into a shared 1022-record tap pool at
		//     X:$BF003-$BFFFA that is byte-identical across chorus types. It is not a per-type
		//     dispatch pointer, and the $25Cxxx per-type table was single-snapshot readings of a
		//     rotating value -- a sampling artefact.
		//     work/dsp_chorus_live_program_matrix_findings.md sections 1 and 5 (2026-07-17).
		//   * It varies BETWEEN RUNS AT CONSTANT CONFIGURATION, $0 included. Two runs of one
		//     identical arm: v12 run1 $3BCD74 / run2 $0, and v1 run1 $0 / run2 $3BCD76
		//     (work/os40_falsify_2026-08-12.md:180). A single snapshot of a value that moves on
		//     its own cannot validate anything.
		//     Also work/diffexec_T15_farside_paramcheck_2026-08-02.md lesson 5 ("unstable in this
		//     harness -- do not inherit that check as validation") and
		//     work/diffexec_T16_filterbank_rerun_spec_2026-08-02.md section 3.
		//
		// So $0 here does NOT mean the run is void, and non-zero does NOT mean it is valid. It is
		// dumped because the value is real and diffable, not because it certifies anything.
		// Engagement has to be established some other way -- for the live-PARAM_CHANGE path that
		// means the block-set evidence itself, not this cell.
		if (dsp2raw)
		{
			const auto tapSlotPtr = dsp2raw->getMemory().get(dsp56k::MemArea_X, 0x1F41);
			out << "X:$1F41 rotating tap-slot pointer = $"
				<< std::hex << std::uppercase << tapSlotPtr << std::dec
				<< "  -- NOT an engagement or validity check: this cell varies run-to-run at"
				   " constant configuration, $0 included. Do not read $0 as a void run.\n\n";
		}

		// chorus_buildarea mode (work/dsp_vm_program_catalog_findings.md item 6.1): the live
		// dispatch-pointer values ($25C3FB Hyper / $25C5A6 Air / $25C3FD classic-family / $25C542
		// Off) mask to X:$5C3FB etc. -- inside the X/P-shared external-memory range where the
		// static image holds the VM descriptor cluster + template region 2. Dump the whole
		// neighborhood live so the runtime state at those targets (possibly builder-written, i.e.
		// differing from the static image) can be compared per chorus type and matched against the
		// two new-in-OS-4.5 program templates.
		if (_dumpBuildArea)
		{
			// Iteration 3 of this mode: X:$1F41's value turned out to be a slot pointer into a
			// shared 1022-record tap pool (X:$BF003-$BFFFA), not a program entry -- the built
			// programs live somewhere else in the heap. So dump DSP2's ENTIRE X memory; run the
			// mode twice for one type to get a runtime-noise baseline, then diff across types.
			const auto& mem1 = dsp1->getMemory();
			dumpRange(mem1, dsp56k::MemArea_X, "dsp1_x", 0x1F40, 8, out);
			// 12-slot smoothing subsystem targeted probe (verification_pass_shortlist item 5):
			// fixed globals X:$485a6 (12-bit mask), X:$49b50/$49b32 (12-slot arrays) -- dump on
			// BOTH DSPs explicitly since the full dump below only covers DSP2.
			out << "--- dsp1 12-slot smoothing subsystem probe ---\n";
			dumpRange(mem1, dsp56k::MemArea_X, "dsp1_x", 0x485a6, 1, out);
			dumpRange(mem1, dsp56k::MemArea_X, "dsp1_x", 0x49b50, 12, out);
			dumpRange(mem1, dsp56k::MemArea_X, "dsp1_x", 0x49b32, 12, out);
			// "13 master parameter cells" probe (work/dsp_vm_interpreter_and_hypersaw_decode_
			// findings.md's open item 1): Osc1's HyperSaw call site's actual-argument cells
			// $566b2-$566b7 plus the $05668x family, plus margin either side -- DSP1 never gets
			// a full-X dump below (unlike DSP2), so this is the only way to see these live on
			// DSP1, where per-voice oscillator building actually happens.
			out << "--- dsp1 master-parameter-cell family probe ---\n";
			dumpRange(mem1, dsp56k::MemArea_X, "dsp1_x", 0x56680, 0x60, out);
			// Region-2 dispatch-site "value_cell"/"flag_cell" operand band (plan.md item 9's
			// region-2 open item / work/dsp_region2_characterization_attempt_findings.md's
			// concrete lead): all 12 dispatch sites at/past 0x05ea85 read value_cell operands
			// packed into 0x055c63-0x055cc3 -- watch this band live while sweeping candidate
			// parameters, instead of only diffing JIT-block sets, since a parameter that writes
			// a nonzero/changing value here is direct, unambiguous evidence of the binding even
			// before any resulting dispatch is understood.
			out << "--- dsp1 region-2 value_cell/flag_cell band probe ---\n";
			dumpRange(mem1, dsp56k::MemArea_X, "dsp1_x", 0x55c60, 0x70, out);
			// Three per-voice build-stream root pointers (work/dsp_vm_interpreter_and_hypersaw_
			// decode_findings.md sec.6 / work/dsp_master_patchsetup_program_parse_findings.md
			// sec.0/2): X:$1f63/$1f66/$1f69 hold the P-memory root-template address for streams
			// 1/2/3 respectively (area->+1, length->+2), written per-voice/per-build by
			// func_05513d/func_055177 before func_054c07 (the ONLY interpreter, confirmed exactly
			// 3 static call sites total in the whole image) walks each. Root A (P:056527, the
			// insert-FX skeleton) and the oscillator-model program (starts ~P:0565a7) are both
			// statically confirmed to correspond to two of these three streams, but which cell
			// holds which was never pinned live, and the third stream's root content is entirely
			// unknown -- boot defaults ($055fbb/$056052/$055fbd, read directly from the static
			// image's func_055d38 bootstrap loop) are placeholder/idle code, not real per-voice
			// state. This probe reads the real, live values for an actually-loaded, playing voice
			// -- the last open static gap in region-2's trigger-condition investigation
			// (work/dsp_region2_trigger_investigation_findings.md): if the third pointer lands
			// inside template region 2 (0x05d05b-0x05ee50), region 2 IS a per-voice stream built
			// every voice; if all three land outside it, region 2 is confirmed unreached by any
			// of the three streams under this preset/mode.
			out << "--- dsp1 per-voice build-stream root-pointer probe (X:$1f60-$1f70) ---\n";
			dumpRange(mem1, dsp56k::MemArea_X, "dsp1_x", 0x1f60, 0x11, out);
			// Bonus check: 05dcee/05dd40 (table 05dca5) and 05e79b (table 05ea65) are the two
			// region-2 tables that do NOT use the fixed-constant "value_cell+1" convention -- they
			// share flag cell 0x001f04 with Root A's own module-enable flag instead, and their
			// value cells (X:$5dcb0, X:$47b55) read as literal $0 in the static image (unlike the
			// 12 fixed-constant sites' nonzero baked-in values) -- consistent with genuine,
			// currently-unwritten live RAM cells rather than deliberate constants. Watch them live
			// to see if this specific pair is actually parameter-driven, unlike the rest of
			// region 2.
			out << "--- dsp1 region-2 subset (05dca5/05ea65) value-cell probe ---\n";
			dumpRange(mem1, dsp56k::MemArea_X, "dsp1_x", 0x5dcb0, 1, out);
			dumpRange(mem1, dsp56k::MemArea_X, "dsp1_x", 0x47b55, 1, out);
			// Site 1 (OS 4.5.1->4.5.2 firmware fix, work/dsp_modmatrix_site1_templatezone_
			// attribution_findings.md's "Goal B") live-trigger probe: the 3-stub abs()/store cluster
			// at P:$04f0b7-$04f0d2 (current 5.1.7.00 firmware address, confirmed via static disasm to
			// be the same cluster identified in the old v45104/v45107 test builds -- the fix's own
			// inserted instruction `tfr a,b a0,y:$23` at $04f0bd survives verbatim) stores into
			// Y:$46/$47/$48 -- STILL the old pre-fix numbering here, not the v45107 "fixed" $43/$44/
			// $45 (that renumbering was already confirmed mechanical/unrelated, and in THIS firmware
			// Y:$43-$45 turned out to be reused by a completely different, unrelated table-cache
			// routine at P:$04f083/P:$053095 -- confirmed via static disasm this session, not
			// assumed). Downstream clamp/limit consumers (func_05b18c family) read Y:$47 against a
			// Y:$16-derived limit. Y:$23 is the fix's own new write target. Dumped on BOTH DSPs since
			// which one actually executes this cluster is one of this probe's open questions (Site 1
			// sits in low P-memory near oscillator/global-synthesis code, unlike the confirmed-
			// DSP2-only chorus/rotary family) -- see work/dsp_site1_live_trigger_findings.md.
			out << "--- dsp1 Site1 stub-cluster probe (Y:$16/$23/$40-$4F) ---\n";
			dumpRange(mem1, dsp56k::MemArea_Y, "dsp1_y", 0x16, 1, out);
			dumpRange(mem1, dsp56k::MemArea_Y, "dsp1_y", 0x23, 1, out);
			dumpRange(mem1, dsp56k::MemArea_Y, "dsp1_y", 0x40, 0x10, out);
			if (dsp2raw)
			{
				const auto& mem2 = dsp2raw->getMemory();
				dumpRange(mem2, dsp56k::MemArea_X, "dsp2_x", 0x1F40, 8, out);
				out << "--- dsp2 12-slot smoothing subsystem probe ---\n";
				dumpRange(mem2, dsp56k::MemArea_X, "dsp2_x", 0x485a6, 1, out);
				dumpRange(mem2, dsp56k::MemArea_X, "dsp2_x", 0x49b50, 12, out);
				dumpRange(mem2, dsp56k::MemArea_X, "dsp2_x", 0x49b32, 12, out);
				out << "--- dsp2 master-parameter-cell family probe ---\n";
				dumpRange(mem2, dsp56k::MemArea_X, "dsp2_x", 0x56680, 0x60, out);
				out << "--- dsp2 region-2 value_cell/flag_cell band probe ---\n";
				dumpRange(mem2, dsp56k::MemArea_X, "dsp2_x", 0x55c60, 0x70, out);
				out << "--- dsp2 Site1 stub-cluster probe (Y:$16/$23/$40-$4F) ---\n";
				dumpRange(mem2, dsp56k::MemArea_Y, "dsp2_y", 0x16, 1, out);
				dumpRange(mem2, dsp56k::MemArea_Y, "dsp2_y", 0x23, 1, out);
				dumpRange(mem2, dsp56k::MemArea_Y, "dsp2_y", 0x40, 0x10, out);
				out << "--- full DSP2 X dump ---\n";
				dumpRange(mem2, dsp56k::MemArea_X, "dsp2_x", 0x0, 0x100000, out);
				out << "--- full DSP2 Y dump ---\n";
				dumpRange(mem2, dsp56k::MemArea_Y, "dsp2_y", 0x0, 0x100000, out);
			}
			out << "\n";
		}

		for (auto* tracker : { &tracker1, tracker2.get() })
		{
			if (!tracker)
				continue;
			out << "--- " << tracker->m_label << ": " << tracker->m_blockStarts.size()
				<< " distinct JIT blocks compiled ---\n";
			for (const auto addr : tracker->m_blockStarts)
				out << "    $" << std::hex << std::uppercase << addr << std::dec << "\n";
			out << "\n";
		}

		out.close();
		std::cout << "Wrote " << _outFile << std::endl;
		return 0;
	}

	// "site1_cold_build_pc_trace <arm>" -- Site 1 live-trigger probe, part 2
	// (work/dsp_site1_live_trigger_findings.md section 7 item 2 / work/dsp_site1_live_trigger_
	// part2_findings.md). The predecessor session's whole harness pattern was "writeSingle a preset
	// once at cb256, then 2 Note Ons ~400cb (~0.56s) apart" -- every prior test therefore already
	// included a "first voice built right after a fresh patch load" moment (the cb512 Note On on a
	// freshly-booted DSP), so that specific condition was never actually left untested. What WAS
	// never tested: (a) a patch loaded via a REAL MIDI Bank Select + Program Change (0xC0), which in
	// the real firmware goes through Microcontroller::partBankSelect/partProgramChange -- confirmed
	// by reading microcontroller.cpp this session that this bottoms out in the exact same
	// writeSingle(BankNumber::EditBuffer, SINGLE, preset) call uc.writeSingle() already makes
	// directly elsewhere in this file, so no NEW DSP-facing code path is expected a priori, but this
	// tests it live rather than trusting the static read alone; (b) several voices being built in a
	// near-simultaneous burst (a 4-note chord within 3 audio-callback ticks of each other, ~4.4ms)
	// immediately after that load, rather than 2 notes spread ~0.56s apart with time to settle
	// between them -- a per-instance stub like Site 1's (its shared prologue caches "current voice/
	// instance pointer r4" and reads x:(r4)+n4-indexed operands) could plausibly only be reached
	// under voice-slot-allocation pressure a single sequential note never creates.
	//
	// Bank-select arithmetic (derived from microcontroller.cpp, not guessed): g_singleRamBankCount=2
	// RAM-bank slots occupy m_singles[0]/[1], so m_singles[b] for b>=2 maps to ROMFile bank (b-2);
	// to reach ROM bank 11 (bank 11/124 "VocoPad XM", the base preset every other probe this
	// session/predecessor's session used) needs m_singles[13]. Microcontroller::partBankSelect sets
	// m_currentBank = toArrayIndex(fromMidiByte(ccValue)) = ccValue-1 (BankNumber is 1-based) -- so
	// ccValue=14 lands on m_singles[13]. Sent live via real MIDI CC32 (Bank Select LSB) + 0xC0
	// (Program Change, value 124), NOT uc.writeSingle -- this is the whole point of this probe.
	//
	// _armParams: zero or more live PARAM_CHANGE overrides (page/idx/val triples, same SysEx shape
	// as runChorusPcTrace's own _liveParams) sent right after the cold load settles, at cb300 --
	// same slot part 2's single hardcoded Arp Mode=Random write used. Empty = matched control,
	// identical cold-PC + chord-burst pattern, nothing overridden (byte-for-byte the old _arm=false
	// path). Part 2 (work/dsp_site1_live_trigger_part2_findings.md sec.3.3) only ever armed this
	// probe with ONE candidate (Arp Mode=Random, page113/idx15/val5) as a deliberate scoping choice,
	// not an exhaustive cross-product of every candidate under this trigger condition -- part 3
	// (work/dsp_site1_live_trigger_part3_findings.md) extends the *candidate* axis (LFO2/LFO3 S&H,
	// Unison LFO Phase, Arp Pattern Selct) while reusing this exact harness/timing unchanged.
	// _armLabel: human-readable description of what _armParams represents, printed to stdout/output
	// file only (no behavioral effect) -- mirrors runChorusPcTrace's per-override cout lines.
	// _candidateTag: short filename-safe tag (e.g. "control"/"arpmode"/"lfo2sh") used for the
	// throwaway .wav name -- kept separate from _armLabel since the latter has spaces unsuitable
	// for a filename.
	int runSite1ColdBuildProbe(const std::vector<std::array<uint8_t, 3>>& _armParams, const std::string& _armLabel,
		const std::string& _candidateTag, const std::string& _outFile)
	{
		auto rom = ROMLoader::findROM(DeviceModel::TI2);
		if (!rom.isValid())
		{
			std::cout << "ROM not found/invalid. Place a valid TI2 firmware .bin next to this executable." << std::endl;
			return 1;
		}

		DspSingle* dsp1raw = nullptr;
		DspSingle* dsp2raw = nullptr;
		virusLib::Device::createDspInstances(dsp1raw, dsp2raw, rom, static_cast<float>(rom.getSamplerate()));
		std::unique_ptr<DspSingle> dsp1(dsp1raw);

		Microcontroller uc(*dsp1, rom, false);
		if (dsp2raw)
			uc.addDSP(*dsp2raw, false);

		AddrTracker tracker1(dsp1->getDSP(), "dsp1");
		dsp1->getDSP().setDebugger(&tracker1);
		std::unique_ptr<AddrTracker> tracker2;
		if (dsp2raw)
		{
			tracker2 = std::make_unique<AddrTracker>(dsp2raw->getDSP(), "dsp2");
			dsp2raw->getDSP().setDebugger(tracker2.get());
		}

		dsp56k::SpscSemaphore sem(1);
		uint32_t callbackCount = 0;
		int32_t notifyTimeout = 0;
		constexpr uint32_t blockSize = 64;
		const uint32_t notifyThreshold = blockSize > 4 ? blockSize - 4 : 0;
		std::vector<SMidiEvent> midiEvents;

		bool bankSelectSent = false, programChangeSent = false, armSent = false;
		bool note1Sent = false, note2Sent = false, note3Sent = false, note4Sent = false;

		auto& esai = dsp1->getAudio();
		esai.setCallback([&](dsp56k::Audio*)
		{
			const auto availableSize = esai.getAudioOutputs().size();
			const auto sizeReached = availableSize >= notifyThreshold;
			--notifyTimeout;
			if (notifyTimeout <= 0 && sizeReached)
			{
				notifyTimeout = static_cast<int>(notifyThreshold);
				sem.notify();
			}

			++callbackCount;
			if ((callbackCount & 0x3) != 0)
				return;

			uc.readMidiOut(midiEvents);
			const auto audioCallbackCount = callbackCount >> 2;
			uc.process();

			if (audioCallbackCount == 1)
			{
				dsp1->drainESSI1();
				uc.sendInitControlCommands(127);
			}
			else if (audioCallbackCount == 256 && !bankSelectSent)
			{
				dsp1->drainESSI1();
				dsp1->disableESSI1();
				std::cout << "[cb " << audioCallbackCount << "] Sending real MIDI Bank Select (CC32=14, "
					"-> m_singles[13] -> ROM bank 11)" << std::endl;
				uc.sendMIDI(SMidiEvent(MidiEventSource::Host, 0xB0, 32, 14));
				uc.sendPendingMidiEvents(std::numeric_limits<uint32_t>::max());
				bankSelectSent = true;
			}
			else if (audioCallbackCount == 260 && !programChangeSent)
			{
				std::cout << "[cb " << audioCallbackCount << "] Sending real MIDI Program Change "
					"(program 124, cold ROM load via Microcontroller::partProgramChange, NOT uc.writeSingle)" << std::endl;
				uc.sendMIDI(SMidiEvent(MidiEventSource::Host, 0xC0, 124, 0));
				uc.sendPendingMidiEvents(std::numeric_limits<uint32_t>::max());
				programChangeSent = true;
			}
			else if (audioCallbackCount == 300 && !armSent)
			{
				if (!_armParams.empty())
				{
					std::cout << "[cb " << audioCallbackCount << "] Sending live PARAM_CHANGE(s): " << _armLabel << std::endl;
					for (const auto& p : _armParams)
					{
						std::cout << "  page $" << std::hex << static_cast<int>(p[0]) << std::dec
							<< " idx " << static_cast<int>(p[1]) << " = " << static_cast<int>(p[2]) << std::endl;
						synthLib::SysexBuffer sysex{
							0xf0, 0x00, 0x20, 0x33, 0x01, 0x00,
							p[0], virusLib::SINGLE, p[1], p[2],
							0xf7
						};
						std::vector<SMidiEvent> responses;
						uc.sendSysex(sysex, responses, MidiEventSource::Host);
					}
				}
				else
				{
					std::cout << "[cb " << audioCallbackCount << "] Control run: no live PARAM_CHANGE sent (all candidates at patch default)" << std::endl;
				}
				armSent = true;
			}
			// Chord burst: 4 notes within 3 audio-callback ticks of each other (~4.4ms total at
			// 44100Hz/64-sample blocks) right after the cold load+arm settles -- as close to
			// "several voices built simultaneously" as this harness's discrete-callback scheduling
			// allows, versus the established pattern's single notes ~400cb (~0.56s) apart.
			else if (audioCallbackCount == 340 && !note1Sent)
			{
				std::cout << "[cb " << audioCallbackCount << "] Chord burst note 1 (60)" << std::endl;
				uc.sendMIDI(SMidiEvent(MidiEventSource::Host, 0x90, 60, 0x5f));
				uc.sendPendingMidiEvents(std::numeric_limits<uint32_t>::max());
				note1Sent = true;
			}
			else if (audioCallbackCount == 341 && !note2Sent)
			{
				std::cout << "[cb " << audioCallbackCount << "] Chord burst note 2 (64)" << std::endl;
				uc.sendMIDI(SMidiEvent(MidiEventSource::Host, 0x90, 64, 0x5f));
				uc.sendPendingMidiEvents(std::numeric_limits<uint32_t>::max());
				note2Sent = true;
			}
			else if (audioCallbackCount == 342 && !note3Sent)
			{
				std::cout << "[cb " << audioCallbackCount << "] Chord burst note 3 (67)" << std::endl;
				uc.sendMIDI(SMidiEvent(MidiEventSource::Host, 0x90, 67, 0x5f));
				uc.sendPendingMidiEvents(std::numeric_limits<uint32_t>::max());
				note3Sent = true;
			}
			else if (audioCallbackCount == 343 && !note4Sent)
			{
				std::cout << "[cb " << audioCallbackCount << "] Chord burst note 4 (70)" << std::endl;
				uc.sendMIDI(SMidiEvent(MidiEventSource::Host, 0x90, 70, 0x5f));
				uc.sendPendingMidiEvents(std::numeric_limits<uint32_t>::max());
				note4Sent = true;
			}
		});

		virusLib::Device::bootDSPs(dsp1.get(), dsp2raw, rom, false);

		installFaultHandler();
		g_faultDsp1 = &dsp1->getDSP();
		if (dsp2raw) g_faultDsp2 = &dsp2raw->getDSP();
		registerMemRange("dsp1_X", dsp1->getMemory().getMemAreaPtr(dsp56k::MemArea_X), 0x100000);
		registerMemRange("dsp1_Y", dsp1->getMemory().getMemAreaPtr(dsp56k::MemArea_Y), 0x100000);
		registerMemRange("dsp1_P", dsp1->getMemory().getMemAreaPtr(dsp56k::MemArea_P), 0x100000);
		if (dsp2raw)
		{
			registerMemRange("dsp2_X", dsp2raw->getMemory().getMemAreaPtr(dsp56k::MemArea_X), 0x100000);
			registerMemRange("dsp2_Y", dsp2raw->getMemory().getMemAreaPtr(dsp56k::MemArea_Y), 0x100000);
			registerMemRange("dsp2_P", dsp2raw->getMemory().getMemAreaPtr(dsp56k::MemArea_P), 0x100000);
		}

		constexpr uint32_t kTotalSamples = 8 * 44100; // matches the rest of this file's proven render duration
		std::cout << "Booted. Rendering " << kTotalSamples << " samples (~8s), cold Bank-Select+Program-Change "
			<< "+ chord-burst pattern, candidate=" << _candidateTag << " (" << _armLabel << ")"
			<< ", tracking every JIT-compiled block's P-memory range on both DSPs..." << std::endl;

		AudioProcessor proc(rom.getSamplerate(),
			"xmem_site1_cold_build_throwaway_" + _candidateTag + ".wav",
			false, kTotalSamples, dsp1.get(), dsp2raw);
		while (!proc.finished())
		{
			sem.wait();
			proc.processBlock(blockSize);
		}

		dsp1->getDSP().setDebugger(nullptr);
		if (dsp2raw)
			dsp2raw->getDSP().setDebugger(nullptr);

		std::ofstream out(_outFile);
		out << "Mode: site1_cold_build_pc_trace, candidate=" << _candidateTag << " (" << _armLabel << ")"
			   " (real MIDI Bank Select CC32=14 + "
			   "Program Change 124 cold load [NOT uc.writeSingle], then a 4-note chord burst within 3 "
			   "callback ticks of each other at cb340-343, JIT-block coverage over ~8s)\n\n";

		// Same probe set as chorus_pc_trace's fulldump block's Site1-specific portion, kept in the
		// same dumpRange call shape/order so existing grep-based reachability checks against other
		// dumps in work/gearmulator-run/ keep working unmodified.
		auto& mem1 = dsp1->getMemory();
		out << "--- dsp1 Site1 stub-cluster probe (Y:$16/$23/$40-$4F) ---\n";
		dumpRange(mem1, dsp56k::MemArea_Y, "dsp1_y", 0x16, 1, out);
		dumpRange(mem1, dsp56k::MemArea_Y, "dsp1_y", 0x23, 1, out);
		dumpRange(mem1, dsp56k::MemArea_Y, "dsp1_y", 0x40, 0x10, out);
		if (dsp2raw)
		{
			auto& mem2 = dsp2raw->getMemory();
			// NOT A SANITY CHECK -- the same false label retired at the runChorusPcTrace site
			// on 2026-08-12, and this copy inherited it verbatim. The retired claim was that "any
			// nonzero/known dispatch value here proves SOME real single loaded, not a blank/failed
			// program-change no-op". X:$1F41 is a rotating tap-slot pointer that moves run-to-run
			// at constant configuration and reads $0 on runs that are fine, so it proves neither
			// direction. See the long note at the runChorusPcTrace site for the evidence.
			const auto tapSlotPtr = mem2.get(dsp56k::MemArea_X, 0x1F41);
			out << "X:$1F41 rotating tap-slot pointer = $"
				<< std::hex << std::uppercase << tapSlotPtr << std::dec
				<< "  -- NOT an engagement or validity check; $0 does not mean the load failed\n";
			out << "--- dsp2 Site1 stub-cluster probe (Y:$16/$23/$40-$4F) ---\n";
			dumpRange(mem2, dsp56k::MemArea_Y, "dsp2_y", 0x16, 1, out);
			dumpRange(mem2, dsp56k::MemArea_Y, "dsp2_y", 0x23, 1, out);
			dumpRange(mem2, dsp56k::MemArea_Y, "dsp2_y", 0x40, 0x10, out);
		}
		out << "\n";

		for (auto* tracker : { &tracker1, tracker2.get() })
		{
			if (!tracker)
				continue;
			out << "--- " << tracker->m_label << ": " << tracker->m_blockStarts.size()
				<< " distinct JIT blocks compiled ---\n";
			for (const auto addr : tracker->m_blockStarts)
				out << "    $" << std::hex << std::uppercase << addr << std::dec << "\n";
			out << "\n";
		}

		out.close();
		std::cout << "Wrote " << _outFile << std::endl;
		return 0;
	}

	// "site1_multimode_pc_trace <candidate>" -- Site 1 live-trigger probe, Multi-mode extension
	// (work/trace_site1_goala_foundations_findings.md section 4): all 19+ prior Site 1 live-trigger
	// runs (parts 1-3 of this investigation) routed every single test through Single-mode
	// writeSingle(EditBuffer, SINGLE, ...) -- confirmed a real Multi/Arrangement-mode transition was
	// never exercised by any of them, even though Microcontroller::writeMulti()/a real PLAY_MODE
	// SysEx switch exist in gearmulator's own API and were already flagged elsewhere in this project
	// (work/dsp_region2_trigger_investigation_findings.md, this file's own comment near line 397-406)
	// as the one genuinely untested trigger axis.
	//
	// A prior session (work/dsp_c9e8_pc_trace_crosscheck_findings.md, 2026-07-15) DID attempt exactly
	// this transition, for an unrelated question, and hit a real gearmulator SIGBUS crash -- but
	// traced here (read microcontroller.cpp fresh this session) to a specific, avoidable cause: the
	// PLAY_MODE=Multi SysEx handler (Microcontroller::sendSysex's PAGE_D/PLAY_MODE branch, ~line 782)
	// replays `writeSingle(EditBuffer, i, m_singleEditBuffers[i])` for all 16 parts using WHATEVER is
	// currently cached in `m_singleEditBuffers[]` -- which defaults, until explicitly written, to RAM
	// bank 0's blank/uninitialized template preset (the exact same landmine this file already avoids
	// elsewhere via its "bank 0/program 0 crashes the core" comment, ~line 3489). The crash is not
	// inherent to Multi mode itself, it's inherent to replaying uninitialized/degenerate preset data
	// through writeSingle -- so this probe explicitly prepopulates all 16 parts with the two presets
	// already proven crash-free across every other test in this file (bank 1/program 0, "known-safe
	// fallback"; bank 11/program 124, "VocoPad XM") BEFORE triggering the real PLAY_MODE transition,
	// sidestepping the landmine while still exercising the identical DSP-facing code path a real
	// Multi-mode UI switch takes.
	//
	// Sequence: prepopulate parts 0-15 (parts 0/1 get VocoPad XM so they're audible; parts 2-15 get
	// the safe filler) via direct writeSingle calls -> writeMulti() with the ROM's own real factory
	// multi (rom.getMulti(0,...), the same call Microcontroller's own constructor uses) so the DSP
	// gets a real per-part MIDI-channel table -> a real live PLAY_MODE SysEx (page=PAGE_D/0x73,
	// idx=PLAY_MODE/122, val=PlayModeMulti/2), confirmed via console log to replay all 16 parts
	// without crashing -> Note On events on parts 0 and 1's actual assigned MIDI channels (read live
	// via getPartMidiChannel(), not assumed), two notes each, deliberately overlapping across the two
	// parts (both a "several voices/instances active simultaneously" condition and a genuine
	// "different Multi part" condition neither Single mode nor the prior cold-build chord-burst test
	// could construct, since a chord burst is still all one part) -> the candidate live PARAM_CHANGE(s),
	// this time addressed to a SPECIFIC MULTI PART (part=1, not the SINGLE sentinel every one of the
	// 19+ prior runs used) -- confirmed by reading Microcontroller::send() (~line 403) that `_part` is
	// transmitted as a literal byte in the raw HDI08 command word (`buf[1] = (_part<<16)|...`), i.e.
	// this is a genuinely different value on the wire than any prior single-mode run ever sent,
	// directly relevant to Site 1's own "per-instance selector" code shape (work/dsp_modmatrix_site1_
	// templatezone_attribution_findings.md's Goal B section). _liveParams/_label/_candidateTag/
	// _outFile follow this file's established runSite1ColdBuildProbe convention.
	// _sendPlayModeSysex (2026-07-21, shm-exhaustion re-test): if true, cb2100 sends the REAL
	// PLAY_MODE=Multi SysEx (page $73, idx 122, val 2) -- the exact path that deterministically
	// SIGBUS-crashed on 2026-07-20 ("bug #1", work/site1_multimode_test_findings.md section 3) --
	// instead of skipping it in favor of the writeMulti() workaround. Purpose: A/B the crash
	// against the /dev/shm root cause found for the FM-Noise SIGBUS
	// (work/dsp_fm_noise_sigbus_mmu_trace_findings.md) using shm_open- vs memfd-backed builds.
	// _testPartA/_testPartB (2026-07-21): which two Multi parts get the active preset + note-ons.
	// Default {1,2} preserves the 2026-07-20 part-0-avoidance workaround; passing {0,1} re-tests
	// the original "note-on to part 0 crashes" characterization against the shm root cause.
	int runSite1MultiModeProbe(const std::vector<std::array<uint8_t, 3>>& _liveParams, const std::string& _label,
		const std::string& _candidateTag, const std::string& _outFile, const bool _sendPlayModeSysex = false,
		const uint8_t _testPartA = 1, const uint8_t _testPartB = 2)
	{
		auto rom = ROMLoader::findROM(DeviceModel::TI2);
		if (!rom.isValid())
		{
			std::cout << "ROM not found/invalid. Place a valid TI2 firmware .bin next to this executable." << std::endl;
			return 1;
		}

		Microcontroller::TPreset safePreset{}, vocoPreset{}, multiPreset{};
		rom.getSingle(1, 0, safePreset);              // "known-safe fallback" (bank 0/program 0 crashes the core)
		rom.getSingle(11, 124, vocoPreset);           // "VocoPad XM" -- proven base preset throughout this file
		const bool haveMulti = rom.getMulti(0, multiPreset); // ROM's own real factory multi (same call Microcontroller's ctor uses)
		std::cout << "Multi-mode probe: parts 0/1 = \"" << ROMFile::getSingleName(vocoPreset)
			<< "\", parts 2-15 = \"" << ROMFile::getSingleName(safePreset) << "\", multi = "
			<< (haveMulti ? ROMFile::getMultiName(multiPreset) : std::string("<unavailable, using default>")) << std::endl;

		DspSingle* dsp1raw = nullptr;
		DspSingle* dsp2raw = nullptr;
		virusLib::Device::createDspInstances(dsp1raw, dsp2raw, rom, static_cast<float>(rom.getSamplerate()));
		std::unique_ptr<DspSingle> dsp1(dsp1raw);

		Microcontroller uc(*dsp1, rom, false);
		if (dsp2raw)
			uc.addDSP(*dsp2raw, false);

		AddrTracker tracker1(dsp1->getDSP(), "dsp1");
		dsp1->getDSP().setDebugger(&tracker1);
		std::unique_ptr<AddrTracker> tracker2;
		if (dsp2raw)
		{
			tracker2 = std::make_unique<AddrTracker>(dsp2raw->getDSP(), "dsp2");
			dsp2raw->getDSP().setDebugger(tracker2.get());
		}

		dsp56k::SpscSemaphore sem(1);
		uint32_t callbackCount = 0;
		int32_t notifyTimeout = 0;
		constexpr uint32_t blockSize = 64;
		const uint32_t notifyThreshold = blockSize > 4 ? blockSize - 4 : 0;
		std::vector<SMidiEvent> midiEvents;

		bool partsPrepopulated = false, multiWritten = false, playModeSent = false, liveParamSent = false;
		bool note1Sent = false, note2Sent = false, note3Sent = false, note4Sent = false;
		// Active/tested parts are 1 and 2, deliberately NOT part 0 -- a diagnostic run this session
		// (see the header comment's "crash #2" discussion) found a note-on to part 0 specifically
		// SIGBUS-crashes gearmulator once genuinely in Multi mode, while the identical note-on
		// sequence to part 1 (and, confirmed here, part 2) does not -- isolated by sending 2 notes to
		// part 1 first (no crash) then a note to part 0 (crashed at the same P:$050bf1 DSP1 PC both
		// times it was tried). Root cause not chased further (deep in DSP-side per-instance/voice
		// table addressing, `X:>$1f00` + r5/n5-indexed access -- see disasm around P:$050be1-$050bff
		// -- looks like the same class of signed/unsigned out-of-bounds host-memory-access bug
		// already found and partly addressed for the unrelated "FM Mode Noise" SIGBUS elsewhere in
		// this project, not something a test harness can route around). Avoiding part 0 as an active
		// part sidesteps it entirely while still giving 2 real, simultaneously-active Multi parts.
		const uint8_t kTestPartA = _testPartA, kTestPartB = _testPartB;
		uint8_t partAChannel = kTestPartA, partBChannel = kTestPartB; // overwritten once read live below

		auto& esai = dsp1->getAudio();
		esai.setCallback([&](dsp56k::Audio*)
		{
			const auto availableSize = esai.getAudioOutputs().size();
			const auto sizeReached = availableSize >= notifyThreshold;
			--notifyTimeout;
			if (notifyTimeout <= 0 && sizeReached)
			{
				notifyTimeout = static_cast<int>(notifyThreshold);
				sem.notify();
			}

			++callbackCount;
			if ((callbackCount & 0x3) != 0)
				return;

			uc.readMidiOut(midiEvents);
			const auto audioCallbackCount = callbackCount >> 2;
			uc.process();

			if (audioCallbackCount == 1)
			{
				dsp1->drainESSI1();
				uc.sendInitControlCommands(127);
			}
			else if (audioCallbackCount == 50 && !partsPrepopulated)
			{
				std::cout << "[cb " << audioCallbackCount << "] Prepopulating all 16 parts (direct writeSingle, "
					"avoids replaying blank RAM-bank-0 data through the PLAY_MODE=Multi transition below); "
					"parts " << static_cast<int>(kTestPartA) << "/" << static_cast<int>(kTestPartB) << " get "
					"VocoPad XM (active/tested), all others (including part 0) get the safe filler only" << std::endl;
				for (uint8_t p = 0; p < 16; ++p)
					uc.writeSingle(BankNumber::EditBuffer, p, (p == kTestPartA || p == kTestPartB) ? vocoPreset : safePreset);
				partsPrepopulated = true;
			}
			else if (audioCallbackCount == 2000 && !multiWritten)
			{
				std::cout << "[cb " << audioCallbackCount << "] Writing real factory multi (direct writeMulti)" << std::endl;
				uc.writeMulti(BankNumber::EditBuffer, 0, multiPreset);
				multiWritten = true;
			}
			else if (audioCallbackCount == 2100 && !playModeSent)
			{
				// NOTE (found this session, see the function's header comment): the literal real
				// PLAY_MODE=Multi SysEx (page $73, idx 122, val 2) reproducibly SIGBUS-crashes
				// gearmulator here, confirmed independently of preset content/queue-backlog timing
				// (tried with generous cb2000/2100 spacing after the prepopulation queue had fully
				// drained -- crashed immediately anyway, inside Microcontroller::sendSysex's own
				// PLAY_MODE branch, which fires 16 writeSingle calls in one tight, unpaced C++ loop
				// with zero opportunity for gearmulator's async preset-upgrade queue to keep up). This
				// is a genuine bug in gearmulator's own bulk-multi-part-load code, not something a
				// test harness can route around by pacing/timing/preset choice -- confirms and
				// finalizes work/dsp_c9e8_pc_trace_crosscheck_findings.md's 2026-07-15 finding.
				//
				// Workaround used instead: reach the identical FUNCTIONAL state (host-side
				// m_globalSettings[PLAY_MODE]==PlayModeMulti, DSP already holding real per-part
				// preset data for all 16 parts from the cb50 prepopulation above, which used the
				// exact same writeSingle() calls every other Site1 test in this file already proved
				// crash-free) via a direct writeMulti() call alone (cb2000 above) -- sendPreset()'s
				// own code (microcontroller.cpp ~line 269) sets PLAY_MODE=Multi as a side effect of
				// ANY writeMulti call, with no dependency on the buggy SysEx handler's bulk-replay
				// loop. This sidesteps only the one buggy code path (the unpaced 16x replay), not
				// "Multi mode" itself -- every other Multi-mode-gated branch this investigation cares
				// about (applyToSingleEditBuffer's per-part routing, sendMIDI's per-part Program
				// Change/Bank routing, the PAGE_B/PAGE_6E per-part PARAM_CHANGE routing used below)
				// reads the exact same m_globalSettings[PLAY_MODE] flag this sets.
				if (_sendPlayModeSysex)
				{
					std::cout << "[cb " << audioCallbackCount << "] Sending the REAL PLAY_MODE=Multi SysEx "
						"(page $73 idx 122 val 2) -- the 2026-07-20 'bug #1' crash path, re-tested for the "
						"shm-exhaustion A/B" << std::endl;
					synthLib::SysexBuffer sysex{
						0xf0, 0x00, 0x20, 0x33, 0x01, 0x00,
						0x73, 0x00, 122, 2,
						0xf7
					};
					std::vector<SMidiEvent> responses;
					uc.sendSysex(sysex, responses, MidiEventSource::Host);
				}
				else
					std::cout << "[cb " << audioCallbackCount << "] Skipping the crash-prone PLAY_MODE SysEx -- "
						"multi mode already engaged via cb2000's direct writeMulti() (see comment above)" << std::endl;
				partAChannel = uc.getPartMidiChannel(kTestPartA);
				partBChannel = uc.getPartMidiChannel(kTestPartB);
				std::cout << "[cb " << audioCallbackCount << "] Part " << static_cast<int>(kTestPartA) << " MIDI channel="
					<< static_cast<int>(partAChannel) << ", Part " << static_cast<int>(kTestPartB) << " MIDI channel="
					<< static_cast<int>(partBChannel) << std::endl;
				playModeSent = true;
			}
			// Generous gaps below (cb2000/2100/2800/2810/3200/3210/3600) are deliberate, not
			// arbitrary: a first attempt at this probe used the original harness's tight cb50/120/256
			// spacing and hit a real SIGBUS, traced (see this function's own header comment) to
			// gearmulator's async preset-upgrade queue (`m_pendingPresetWrites`) still draining the
			// 16-part prepopulation batch (observed drain rate ~46 audio-callback-ticks/item from a
			// console-log timestamp cross-check) when the PLAY_MODE SysEx's OWN internal 16x
			// writeSingle replay piled a second batch on top of it. These gaps (each comfortably >
			// 16*46=736 ticks) let each batch fully drain before the next step fires, confirmed
			// crash-free empirically (see work/site1_multimode_test_findings.md) -- not fundamental
			// to Multi mode itself, just to how fast this harness may queue transfers.
			else if (audioCallbackCount == 2800 && !note1Sent)
			{
				std::cout << "[cb " << audioCallbackCount << "] Note On part " << static_cast<int>(kTestPartA)
					<< " (channel " << static_cast<int>(partAChannel) << ", note 60)" << std::endl;
				uc.sendMIDI(SMidiEvent(MidiEventSource::Host, static_cast<uint8_t>(0x90 | (partAChannel & 0x0f)), 60, 0x5f));
				uc.sendPendingMidiEvents(std::numeric_limits<uint32_t>::max());
				note1Sent = true;
			}
			else if (audioCallbackCount == 2810 && !note2Sent)
			{
				std::cout << "[cb " << audioCallbackCount << "] Note On part " << static_cast<int>(kTestPartB)
					<< " (channel " << static_cast<int>(partBChannel) << ", note 64) -- overlaps part "
					<< static_cast<int>(kTestPartA) << "'s still-held note 60" << std::endl;
				uc.sendMIDI(SMidiEvent(MidiEventSource::Host, static_cast<uint8_t>(0x90 | (partBChannel & 0x0f)), 64, 0x5f));
				uc.sendPendingMidiEvents(std::numeric_limits<uint32_t>::max());
				note2Sent = true;
			}
			else if (audioCallbackCount == 3200 && !note3Sent)
			{
				std::cout << "[cb " << audioCallbackCount << "] Note On part " << static_cast<int>(kTestPartA)
					<< " (channel " << static_cast<int>(partAChannel) << ", note 67)" << std::endl;
				uc.sendMIDI(SMidiEvent(MidiEventSource::Host, static_cast<uint8_t>(0x90 | (partAChannel & 0x0f)), 67, 0x5f));
				uc.sendPendingMidiEvents(std::numeric_limits<uint32_t>::max());
				note3Sent = true;
			}
			else if (audioCallbackCount == 3210 && !note4Sent)
			{
				std::cout << "[cb " << audioCallbackCount << "] Note On part " << static_cast<int>(kTestPartB)
					<< " (channel " << static_cast<int>(partBChannel) << ", note 70)" << std::endl;
				uc.sendMIDI(SMidiEvent(MidiEventSource::Host, static_cast<uint8_t>(0x90 | (partBChannel & 0x0f)), 70, 0x5f));
				uc.sendPendingMidiEvents(std::numeric_limits<uint32_t>::max());
				note4Sent = true;
			}
			else if (audioCallbackCount == 3600 && !liveParamSent)
			{
				if (!_liveParams.empty())
				{
					std::cout << "[cb " << audioCallbackCount << "] Sending live PARAM_CHANGE(s) targeted at "
						"MULTI PART " << static_cast<int>(kTestPartA) << " (not SINGLE): " << _label << std::endl;
					for (const auto& p : _liveParams)
					{
						std::cout << "  page $" << std::hex << static_cast<int>(p[0]) << std::dec
							<< " idx " << static_cast<int>(p[1]) << " = " << static_cast<int>(p[2])
							<< " (part=" << static_cast<int>(kTestPartA) << ")" << std::endl;
						synthLib::SysexBuffer sysex{
							0xf0, 0x00, 0x20, 0x33, 0x01, 0x00,
							p[0], kTestPartA, p[1], p[2],
							0xf7
						};
						std::vector<SMidiEvent> responses;
						uc.sendSysex(sysex, responses, MidiEventSource::Host);
					}
				}
				else
				{
					std::cout << "[cb " << audioCallbackCount << "] Control run: no live PARAM_CHANGE sent" << std::endl;
				}
				liveParamSent = true;
			}
		});

		virusLib::Device::bootDSPs(dsp1.get(), dsp2raw, rom, false);

		installFaultHandler();
		g_faultDsp1 = &dsp1->getDSP();
		if (dsp2raw) g_faultDsp2 = &dsp2raw->getDSP();
		registerMemRange("dsp1_X", dsp1->getMemory().getMemAreaPtr(dsp56k::MemArea_X), 0x100000);
		registerMemRange("dsp1_Y", dsp1->getMemory().getMemAreaPtr(dsp56k::MemArea_Y), 0x100000);
		registerMemRange("dsp1_P", dsp1->getMemory().getMemAreaPtr(dsp56k::MemArea_P), 0x100000);
		if (dsp2raw)
		{
			registerMemRange("dsp2_X", dsp2raw->getMemory().getMemAreaPtr(dsp56k::MemArea_X), 0x100000);
			registerMemRange("dsp2_Y", dsp2raw->getMemory().getMemAreaPtr(dsp56k::MemArea_Y), 0x100000);
			registerMemRange("dsp2_P", dsp2raw->getMemory().getMemAreaPtr(dsp56k::MemArea_P), 0x100000);
		}

		// Longer than this file's usual 8s render -- needed to give the async preset-upgrade queue
		// (see the comment above the note-on block) time to fully drain both the 16-part
		// prepopulation batch and the PLAY_MODE replay's own 16-part batch before the render ends.
		constexpr uint32_t kTotalSamples = 32 * 44100; // ~32s
		std::cout << "Booted. Rendering " << kTotalSamples << " samples (~32s), real Multi-mode transition "
			<< "(2 active parts, overlapping notes), candidate=" << _candidateTag << " (" << _label << ")"
			<< ", tracking every JIT-compiled block's P-memory range on both DSPs..." << std::endl;

		AudioProcessor proc(rom.getSamplerate(),
			"xmem_site1_multimode_throwaway_" + _candidateTag + ".wav",
			false, kTotalSamples, dsp1.get(), dsp2raw);
		while (!proc.finished())
		{
			sem.wait();
			proc.processBlock(blockSize);
		}

		dsp1->getDSP().setDebugger(nullptr);
		if (dsp2raw)
			dsp2raw->getDSP().setDebugger(nullptr);

		std::ofstream out(_outFile);
		out << "Mode: site1_multimode_pc_trace, candidate=" << _candidateTag << " (" << _label << ")"
			   " (real PLAY_MODE=Multi SysEx transition with 16 prepopulated parts, 2 active parts with "
			   "overlapping notes on their real assigned MIDI channels, candidate PARAM_CHANGE targeted "
			   "at part=1, JIT-block coverage over ~8s)\n\n";

		auto& mem1 = dsp1->getMemory();
		out << "--- dsp1 Site1 stub-cluster probe (Y:$16/$23/$40-$4F) ---\n";
		dumpRange(mem1, dsp56k::MemArea_Y, "dsp1_y", 0x16, 1, out);
		dumpRange(mem1, dsp56k::MemArea_Y, "dsp1_y", 0x23, 1, out);
		dumpRange(mem1, dsp56k::MemArea_Y, "dsp1_y", 0x40, 0x10, out);
		if (dsp2raw)
		{
			auto& mem2 = dsp2raw->getMemory();
			// Label retired 2026-08-12 along with the other two sites: X:$1F41 is a rotating
			// tap-slot pointer, not a dispatch pointer, and not a validity verdict of any kind.
			const auto tapSlotPtr = mem2.get(dsp56k::MemArea_X, 0x1F41);
			out << "X:$1F41 rotating tap-slot pointer = $"
				<< std::hex << std::uppercase << tapSlotPtr << std::dec
				<< "  -- NOT an engagement or validity check\n";
			out << "--- dsp2 Site1 stub-cluster probe (Y:$16/$23/$40-$4F) ---\n";
			dumpRange(mem2, dsp56k::MemArea_Y, "dsp2_y", 0x16, 1, out);
			dumpRange(mem2, dsp56k::MemArea_Y, "dsp2_y", 0x23, 1, out);
			dumpRange(mem2, dsp56k::MemArea_Y, "dsp2_y", 0x40, 0x10, out);
		}
		out << "\n";

		for (auto* tracker : { &tracker1, tracker2.get() })
		{
			if (!tracker)
				continue;
			out << "--- " << tracker->m_label << ": " << tracker->m_blockStarts.size()
				<< " distinct JIT blocks compiled ---\n";
			for (const auto addr : tracker->m_blockStarts)
				out << "    $" << std::hex << std::uppercase << addr << std::dec << "\n";
			out << "\n";
		}

		out.close();
		std::cout << "Wrote " << _outFile << std::endl;
		return 0;
	}

	// "hardsync_pc_trace <mode>" -- verification-pass shortlist item #2
	// (work/verification_pass_shortlist_2026-07-16.md): doc/dsp56300_synth_engine.md's confirmed
	// self-modifying-code hard-sync mechanism (func_04fab5/func_04faba patch P:$4fa2b/$4fa50 with a
	// real jses call to func_04fa79) is hedged on WHICH UI parameter arms it -- Osc3 Mode=Slave
	// (page 113/0x71 idx 41, value 1) or the plain boolean Osc2 Sync (page 112/0x70 idx 28)? Since
	// the patched slots sit inside an always-executed per-sample loop (reached as a JIT block
	// regardless of whether they're currently a no-op data word or the live jses call), checking
	// their own reachability is uninformative. Instead this checks reachability of the *patcher*
	// functions themselves (func_04fab5/func_04faba, only called from func_04f969's conditional
	// pitch-clamp branch) and the *consumer* func_04fa79 (only entered via the conditionally-armed
	// jses, not part of the loop's unconditional path) -- both are clean, unambiguous reachability
	// signals, reusing the same target-list-report style as the original pc_trace mode.
	// mode: 0 = baseline (Osc3 Off, Osc2 Sync off), 1 = Osc3 Mode=Slave, 2 = Osc2 Sync=1.
	int runHardSyncPcTrace(int _mode, const std::string& _outFile)
	{
		auto rom = ROMLoader::findROM(DeviceModel::TI2);
		if (!rom.isValid())
		{
			std::cout << "ROM not found/invalid." << std::endl;
			return 1;
		}

		Microcontroller::TPreset preset{};
		rom.getSingle(11, 124, preset); // "VocoPad XM" -- same proven base as chorus_pc_trace
		std::cout << "Using preset \"" << ROMFile::getSingleName(preset) << "\" as hardsync_pc_trace "
			"base, mode=" << _mode << std::endl;

		if (preset.size() >= 305)
		{
			preset[257] = 1;  preset[258] = 64; preset[259] = 0; preset[260] = 64;
			preset[261] = 10; preset[262] = 64; preset[265] = 10; // Reverb
			preset[103] = 1;  preset[105] = 64; preset[106] = 43;
			preset[107] = 64; preset[108] = 32;                   // Chorus
			preset[228] = 1;  preset[229] = 64; preset[328] = 127; // Distortion
			preset[112] = 1;  preset[113] = 64; preset[114] = 64; preset[116] = 64; // Delay
			preset[212] = 3;  preset[213] = 64; preset[214] = 36;
			preset[215] = 112; preset[216] = 64;                   // Phaser
		}
		if (preset.size() > 169)
		{
			preset[169] = (_mode == 1) ? 1 : 0; // Osc3 Mode: 1=Slave, 0=Off otherwise
			preset[28] = (_mode == 2) ? 1 : 0;  // Osc2 Sync: boolean
			std::cout << "  Osc3 Mode=" << static_cast<int>(preset[169])
				<< " Osc2 Sync=" << static_cast<int>(preset[28]) << std::endl;
		}

		DspSingle* dsp1raw = nullptr;
		DspSingle* dsp2raw = nullptr;
		virusLib::Device::createDspInstances(dsp1raw, dsp2raw, rom, static_cast<float>(rom.getSamplerate()));
		std::unique_ptr<DspSingle> dsp1(dsp1raw);

		Microcontroller uc(*dsp1, rom, false);
		if (dsp2raw)
			uc.addDSP(*dsp2raw, false);

		AddrTracker tracker1(dsp1->getDSP(), "dsp1");
		dsp1->getDSP().setDebugger(&tracker1);
		std::unique_ptr<AddrTracker> tracker2;
		if (dsp2raw)
		{
			tracker2 = std::make_unique<AddrTracker>(dsp2raw->getDSP(), "dsp2");
			dsp2raw->getDSP().setDebugger(tracker2.get());
		}

		dsp56k::SpscSemaphore sem(1);
		uint32_t callbackCount = 0;
		int32_t notifyTimeout = 0;
		constexpr uint32_t blockSize = 64;
		const uint32_t notifyThreshold = blockSize > 4 ? blockSize - 4 : 0;
		std::vector<SMidiEvent> midiEvents;

		bool presetSent = false, noteSent = false, secondNoteSent = false, thirdNoteSent = false;
		bool pitchBendSent = false, pitchBendDownSent = false;

		auto& esai = dsp1->getAudio();
		esai.setCallback([&](dsp56k::Audio*)
		{
			const auto availableSize = esai.getAudioOutputs().size();
			const auto sizeReached = availableSize >= notifyThreshold;
			--notifyTimeout;
			if (notifyTimeout <= 0 && sizeReached)
			{
				notifyTimeout = static_cast<int>(notifyThreshold);
				sem.notify();
			}

			++callbackCount;
			if ((callbackCount & 0x3) != 0)
				return;

			uc.readMidiOut(midiEvents);
			const auto audioCallbackCount = callbackCount >> 2;
			uc.process();

			if (audioCallbackCount == 1)
			{
				dsp1->drainESSI1();
				uc.sendInitControlCommands(127);
			}
			else if (audioCallbackCount == 256 && !presetSent)
			{
				dsp1->drainESSI1();
				dsp1->disableESSI1();
				std::cout << "[cb " << audioCallbackCount << "] Sending preset" << std::endl;
				uc.writeSingle(BankNumber::EditBuffer, virusLib::SINGLE, preset);
				presetSent = true;
			}
			else if (audioCallbackCount == 512 && !noteSent)
			{
				std::cout << "[cb " << audioCallbackCount << "] Sending Note On" << std::endl;
				uc.sendMIDI(SMidiEvent(MidiEventSource::Host, 0x90, 60, 0x5f));
				uc.sendPendingMidiEvents(std::numeric_limits<uint32_t>::max());
				noteSent = true;
			}
			else if (audioCallbackCount == 900 && !secondNoteSent && _mode != 3)
			{
				// A pitch-bend-shaped follow-up: a second, higher note, likely to cross whatever
				// pitch-clamp threshold func_04f969's branch tests, since the hard-sync arm
				// condition is gated on a pitch-clamp outcome per the doc's own description.
				std::cout << "[cb " << audioCallbackCount << "] Sending second Note On (note 84)" << std::endl;
				uc.sendMIDI(SMidiEvent(MidiEventSource::Host, 0x90, 84, 0x7f));
				uc.sendPendingMidiEvents(std::numeric_limits<uint32_t>::max());
				secondNoteSent = true;
			}
			else if (audioCallbackCount == 1300 && !thirdNoteSent && _mode != 3)
			{
				std::cout << "[cb " << audioCallbackCount << "] Sending third Note On (note 36, low)" << std::endl;
				uc.sendMIDI(SMidiEvent(MidiEventSource::Host, 0x90, 36, 0x7f));
				uc.sendPendingMidiEvents(std::numeric_limits<uint32_t>::max());
				thirdNoteSent = true;
			}
			else if (audioCallbackCount == 700 && _mode == 3 && !pitchBendSent)
			{
				// mode 3: the doc's own language ("func_04f969's own pitch-clamp branch outcome")
				// suggests the trigger might be a pitch value hitting a clamp boundary, not a UI
				// sync mode at all -- test a real full-range Pitch Bend event while a note sounds.
				std::cout << "[cb " << audioCallbackCount << "] Sending max Pitch Bend Up" << std::endl;
				uc.sendMIDI(SMidiEvent(MidiEventSource::Host, 0xE0, 0x7F, 0x7F));
				uc.sendPendingMidiEvents(std::numeric_limits<uint32_t>::max());
				pitchBendSent = true;
			}
			else if (audioCallbackCount == 1100 && _mode == 3 && pitchBendSent && !pitchBendDownSent)
			{
				std::cout << "[cb " << audioCallbackCount << "] Sending max Pitch Bend Down" << std::endl;
				uc.sendMIDI(SMidiEvent(MidiEventSource::Host, 0xE0, 0x00, 0x00));
				uc.sendPendingMidiEvents(std::numeric_limits<uint32_t>::max());
				pitchBendDownSent = true;
			}
		});

		virusLib::Device::bootDSPs(dsp1.get(), dsp2raw, rom, false);

		constexpr uint32_t kTotalSamples = 8 * 44100;
		std::cout << "Booted. Rendering " << kTotalSamples << " samples (~8s), mode=" << _mode
			<< "..." << std::endl;

		AudioProcessor proc(rom.getSamplerate(), "xmem_hardsync_pc_trace_throwaway.wav", false, kTotalSamples, dsp1.get(), dsp2raw);
		while (!proc.finished())
		{
			sem.wait();
			proc.processBlock(blockSize);
		}

		dsp1->getDSP().setDebugger(nullptr);
		if (dsp2raw)
			dsp2raw->getDSP().setDebugger(nullptr);

		std::ofstream out(_outFile);
		out << "Mode: hardsync_pc_trace, mode=" << _mode << " (0=baseline 1=Osc3Slave 2=Osc2Sync)\n\n";

		const std::vector<std::pair<dsp56k::TWord, const char*>> targets = {
			{ 0x04fab5, "func_04fab5 (hard-sync patcher A)" },
			{ 0x04faba, "func_04faba (hard-sync patcher B)" },
			{ 0x04fa79, "func_04fa79 (hard-sync consumer, only entered via armed jses)" },
			{ 0x04f969, "func_04f969 (pitch-clamp branch that selects the patcher)" },
		};

		writeSpeculationLegend(out);

		for (auto* tracker : { &tracker1, tracker2.get() })
		{
			if (!tracker)
				continue;
			out << "--- " << tracker->m_label << ": " << tracker->m_blockStarts.size()
				<< " distinct JIT blocks compiled ---\n";
			for (const auto& [addr, desc] : targets)
			{
				const bool startsBlock = tracker->m_blockStarts.count(addr) != 0;
				const bool covered = tracker->covers(addr);
				out << "  $" << std::hex << std::uppercase << addr << std::dec
					<< (startsBlock ? "  BLOCK-START" : (covered ? "  covered-mid-block" : "  NOT REACHED"))
					<< "  -- " << desc << speculationNote(startsBlock, addr) << "\n";
			}
			out << "\n";
		}

		out.close();
		std::cout << "Wrote " << _outFile << std::endl;
		return 0;
	}

	// "oscwave_probe <value>" -- verification-pass shortlist item #3
	// (work/verification_pass_shortlist_2026-07-16.md): doc/dsp56300_synth_engine.md:845-849 flags
	// a per-oscillator "type code" field (y:(r0+$2c)) compared against -3/2 right before the
	// per-sample waveform-generator call, hedged as "which concrete waveforms -3/2/other map to
	// wasn't identified." Sweeps Oscillator 1 Wave Select (page 112/0x70 idx 19, 0-63) live and
	// reads the field via the confirmed active-voice linked-list walk.
	int runOscWaveProbe(int _waveSelect, const std::string& _outFile)
	{
		auto rom = ROMLoader::findROM(DeviceModel::TI2);
		if (!rom.isValid())
		{
			std::cout << "ROM not found/invalid." << std::endl;
			return 1;
		}

		Microcontroller::TPreset preset{};
		rom.getSingle(1, 0, preset); // plain base preset, no FX needed for this read
		std::cout << "Using preset \"" << ROMFile::getSingleName(preset) << "\" as oscwave_probe "
			"base, Osc1 Wave Select=" << _waveSelect << std::endl;
		if (preset.size() > 19)
			preset[19] = static_cast<uint8_t>(_waveSelect); // Osc1 Wave Select

		DspSingle* dsp1raw = nullptr;
		DspSingle* dsp2raw = nullptr;
		virusLib::Device::createDspInstances(dsp1raw, dsp2raw, rom, static_cast<float>(rom.getSamplerate()));
		std::unique_ptr<DspSingle> dsp1(dsp1raw);

		Microcontroller uc(*dsp1, rom, false);
		if (dsp2raw)
			uc.addDSP(*dsp2raw, false);

		dsp56k::SpscSemaphore sem(1);
		uint32_t callbackCount = 0;
		int32_t notifyTimeout = 0;
		constexpr uint32_t blockSize = 64;
		const uint32_t notifyThreshold = blockSize > 4 ? blockSize - 4 : 0;
		std::vector<SMidiEvent> midiEvents;

		bool presetSent = false, noteSent = false;
		std::ofstream out(_outFile);

		auto& esai = dsp1->getAudio();
		esai.setCallback([&](dsp56k::Audio*)
		{
			const auto availableSize = esai.getAudioOutputs().size();
			const auto sizeReached = availableSize >= notifyThreshold;
			--notifyTimeout;
			if (notifyTimeout <= 0 && sizeReached)
			{
				notifyTimeout = static_cast<int>(notifyThreshold);
				sem.notify();
			}

			++callbackCount;
			if ((callbackCount & 0x3) != 0)
				return;

			uc.readMidiOut(midiEvents);
			const auto audioCallbackCount = callbackCount >> 2;
			uc.process();

			if (audioCallbackCount == 1)
			{
				dsp1->drainESSI1();
				uc.sendInitControlCommands(127);
			}
			else if (audioCallbackCount == 256 && !presetSent)
			{
				dsp1->drainESSI1();
				dsp1->disableESSI1();
				uc.writeSingle(BankNumber::EditBuffer, virusLib::SINGLE, preset);
				presetSent = true;
			}
			else if (audioCallbackCount == 512 && !noteSent)
			{
				uc.sendMIDI(SMidiEvent(MidiEventSource::Host, 0x90, 60, 0x5f));
				uc.sendPendingMidiEvents(std::numeric_limits<uint32_t>::max());
				noteSent = true;
			}
			else if (audioCallbackCount == 700)
			{
				out << "=== cb700 (post-note-settle) ===\n";
				dumpVoiceLinkedList(dsp1->getMemory(), out);
			}
			else if (audioCallbackCount == 1500)
			{
				out << "=== cb1500 (later) ===\n";
				dumpVoiceLinkedList(dsp1->getMemory(), out);
			}
		});

		virusLib::Device::bootDSPs(dsp1.get(), dsp2raw, rom, false);

		constexpr uint32_t kTotalSamples = 6 * 44100;
		AudioProcessor proc(rom.getSamplerate(), "xmem_oscwave_probe_throwaway.wav", false, kTotalSamples, dsp1.get(), dsp2raw);
		while (!proc.finished())
		{
			sem.wait();
			proc.processBlock(blockSize);
		}

		out.close();
		std::cout << "Wrote " << _outFile << std::endl;
		return 0;
	}

	// "ji_pitch_probe <note> <pureTuning> <outWav>" -- work/dsp_vm_interpreter_and_hypersaw_decode_
	// findings.md's open question #2 / doc/dsp56300_synth_engine.md: the shared pitch-mapper op
	// 5929a maps semitone class through a P:059280 table holding exact log2 of just-intonation
	// ratios (17/16, 9/8, 6/5, 5/4, 4/3, 7/5, 3/2, 8/5, 5/3, 7/4, 15/8) instead of the identity/ET
	// mapping. resources/Virus TI Reference.pdf's Global Tuning page documents a "Pure Tuning"
	// parameter (Tempered/default .. Natural .. Pure, "slight pitch adjustment... to minimize
	// dissonance"), gearmulator's own ControlCommand enum has this as unattributed "UNK76" but its
	// sendInitControlCommands array already comments page-0x40/param-0x4C as "Pure Tuning = 0" --
	// matching this table's own live control-command slot exactly. Renders one held HyperSaw note
	// per invocation (Osc1 only, HyperSaw, flat ADSR, FX off) with Pure Tuning set live via
	// PARAM_CHANGE_D (cmd 0x73) BEFORE Note On, to a real WAV file a Python driver can measure the
	// fundamental frequency of -- the live chromatic-sweep check this open question has been
	// waiting on. Not a JIT-trace/memory-dump probe like its siblings: X:$1f31/$1f32 are shared
	// per-tick scratch cells reused by whichever oscillator/voice runs last, so reading them
	// directly is ambiguous the moment Osc2 or a second voice is in play; measuring the actual
	// rendered audio sidesteps that ambiguity entirely and is a more direct answer to "does this
	// audibly warp pitch" anyway.
	int runJiPitchProbe(int _note, int _pureTuning, const std::string& _wavOutFile)
	{
		auto rom = ROMLoader::findROM(DeviceModel::TI2);
		if (!rom.isValid())
		{
			std::cout << "ROM not found/invalid." << std::endl;
			return 1;
		}

		Microcontroller::TPreset preset{};
		rom.getSingle(1, 0, preset); // plain base preset, same fallback the other probes use

		// Osc1 Mode = Classic (page 110/PAGE_6E idx 30 -> offset 2*128+30 = 286) -- op 5929a (the
		// pitch mapper under test) is part of the "oscillator core" shared by all 8 osc models
		// (doc/dsp56300_synth_engine.md), and Classic's single band-limited sawtooth (no per-saw
		// detune ladder/beating) gives a far cleaner single-fundamental waveform for autocorrelation
		// pitch measurement than HyperSaw's multi-saw texture, which an initial pass showed
		// confuses simple F0 estimators (see work/dsp_ji_pitch_live_check_findings.md). Balance
		// fully Osc1 (page 112 idx 33 -> offset 33, 0 = "-64" = Osc1 only per the manual), flat
		// ADSR (Attack 0, Decay/Sustain full so the note holds at a constant level, no note-off
		// needed), FX sends zeroed so nothing else colors the fundamental.
		if (preset.size() > 504)
		{
			preset[286] = 0;   // Osc1 Mode = Classic
			preset[17] = 64;   // Osc1 Shape = center (index 17 is Classic's "Shape" field)
			preset[20] = 64;   // Osc1 Semitone = 0
			preset[21] = 96;   // Osc1 Keyfollow = Norm
			preset[33] = 0;    // Osc Balance = Osc1 only
			preset[59] = 0;    // Amp Env Attack
			preset[60] = 127;  // Amp Env Decay
			preset[61] = 127;  // Amp Env Sustain
			preset[105] = 0;   // Chorus Mix
			preset[113] = 0;   // Delay Send
			preset[258] = 0;   // Reverb Send
			preset[213] = 0;   // Phaser Mix
			preset[328] = 0;   // Distortion Mix

			// The factory base preset ("64Degee MS") is an arbitrary sound-design patch, not a
			// clean reference tone -- a first pass (see work/dsp_ji_pitch_live_check_findings.md)
			// found a badly non-monotonic, octave-confused chromatic sweep, traced to leftover
			// modulation sources this preset carries that the overrides above don't touch.
			// Neutralize every pitch-affecting source found in parameterDescriptions_TI.json:
			preset[5] = 0;     // Portamento Time -- a glide would smear pitch over the analysis window
			preset[34] = 0;    // Suboscillator Volume -- an octave-below sub-osc would dominate the FFT
			preset[37] = 0;    // Noise Volume
			preset[74] = 64;   // Osc1 Lfo1 Amount (bipolar, 64 = center = off) -- vibrato
			preset[75] = 64;   // Osc2 Lfo1 Amount
			preset[143] = 0;   // Arp Mode = Off (page 113 idx 15 -> offset 128+15)
			preset[192] = 0;   // Assign1 Source = Off (page 113 idx 64 -> offset 128+64)
			preset[195] = 0;   // Assign2 Source = Off (page 113 idx 67 -> offset 128+67)
			preset[200] = 0;   // Assign3 Source = Off (page 113 idx 72 -> offset 128+72)
			preset[504] = 0;   // Unison Mode = Off (page 111 idx 120 -> offset 384+120)

			// A second pass (still work/dsp_ji_pitch_live_check_findings.md) found the residual
			// non-monotonic sweep traced to the filter: with Resonance/Env Amount left at whatever
			// the factory patch had, a modulated/resonant filter's own emphasis peak slides over
			// time and can dominate naive peak-picking pitch estimators even though the true
			// oscillator fundamental is stable underneath -- fully open, unresonant, unmodulated
			// filters remove that confound.
			preset[40] = 127; // Filter 1 Cutoff = fully open
			preset[41] = 127; // Filter 2 Cutoff = fully open
			preset[42] = 0;   // Filter 1 Resonance
			preset[43] = 0;   // Filter 2 Resonance
			preset[44] = 0;   // Filter 1 Env Amount
			preset[45] = 0;   // Filter 2 Env Amount
			preset[76] = 64;  // PW Lfo1 Amount (bipolar, off)
			preset[77] = 64;  // Reso Lfo1 Amount
			preset[78] = 64;  // FiltGain Lfo1 Amount
			preset[86] = 64;  // Shape Lfo2 Amount
			preset[87] = 64;  // FM Lfo2 Amount
			preset[88] = 64;  // Cutoff1 Lfo2 Amount
			preset[89] = 64;  // Cutoff2 Lfo2 Amount
			preset[90] = 64;  // Pan Lfo2 Amount
			preset[140] = 0;  // Osc Lfo3 Amount (page 113 idx 12 -> offset 128+12)

			// Osc Balance=0 above should already fully silence Osc2 in the mix, but a lingering
			// slow beat pattern in an earlier pass survived every modulation-source fix above --
			// force Osc2 to unison-with-Osc1 pitch too, defensively, in case Balance's crossfade
			// doesn't reach an exact zero and a detuned Osc2 is leaking through underneath.
			preset[25] = 64;  // Osc2 Semitone = 0
			preset[26] = 0;   // Osc2 Detune = 0 (factory default is 32, a deliberate small detune)
		}
		std::cout << "ji_pitch_probe: note=" << _note << " Pure Tuning=" << _pureTuning
			<< " -> " << _wavOutFile << std::endl;

		DspSingle* dsp1raw = nullptr;
		DspSingle* dsp2raw = nullptr;
		virusLib::Device::createDspInstances(dsp1raw, dsp2raw, rom, static_cast<float>(rom.getSamplerate()));
		std::unique_ptr<DspSingle> dsp1(dsp1raw);

		Microcontroller uc(*dsp1, rom, false);
		if (dsp2raw)
			uc.addDSP(*dsp2raw, false);

		dsp56k::SpscSemaphore sem(1);
		uint32_t callbackCount = 0;
		int32_t notifyTimeout = 0;
		constexpr uint32_t blockSize = 64;
		const uint32_t notifyThreshold = blockSize > 4 ? blockSize - 4 : 0;
		std::vector<SMidiEvent> midiEvents;

		bool presetSent = false, tuningSent = false, noteSent = false;

		auto& esai = dsp1->getAudio();
		esai.setCallback([&](dsp56k::Audio*)
		{
			const auto availableSize = esai.getAudioOutputs().size();
			const auto sizeReached = availableSize >= notifyThreshold;
			--notifyTimeout;
			if (notifyTimeout <= 0 && sizeReached)
			{
				notifyTimeout = static_cast<int>(notifyThreshold);
				sem.notify();
			}

			++callbackCount;
			if ((callbackCount & 0x3) != 0)
				return;

			uc.readMidiOut(midiEvents);
			const auto audioCallbackCount = callbackCount >> 2;
			uc.process();

			if (audioCallbackCount == 1)
			{
				dsp1->drainESSI1();
				uc.sendInitControlCommands(127);
			}
			else if (audioCallbackCount == 256 && !presetSent)
			{
				dsp1->drainESSI1();
				dsp1->disableESSI1();
				uc.writeSingle(BankNumber::EditBuffer, virusLib::SINGLE, preset);
				presetSent = true;
			}
			else if (audioCallbackCount == 300 && !tuningSent)
			{
				// Live PARAM_CHANGE_D (cmd 0x73 = globalSettingsPage() on TI ROMs), part=SINGLE
				// (ignored for global-page writes per Microcontroller::send), param=76 (Pure
				// Tuning / "UNK76"), sent BEFORE Note On so the voice allocator's initial pitch
				// computation sees the new value, not a live re-evaluation of an already-sounding
				// voice.
				std::cout << "[cb " << audioCallbackCount << "] Sending live PARAM_CHANGE_D Pure Tuning = "
					<< _pureTuning << std::endl;
				synthLib::SysexBuffer sysex{
					0xf0, 0x00, 0x20, 0x33, 0x01, 0x00,
					0x73, virusLib::SINGLE, 76, static_cast<uint8_t>(_pureTuning),
					0xf7
				};
				std::vector<SMidiEvent> responses;
				uc.sendSysex(sysex, responses, MidiEventSource::Host);
				tuningSent = true;
			}
			else if (audioCallbackCount == 512 && !noteSent)
			{
				std::cout << "[cb " << audioCallbackCount << "] Sending Note On " << _note << std::endl;
				uc.sendMIDI(SMidiEvent(MidiEventSource::Host, 0x90, static_cast<uint8_t>(_note), 100));
				uc.sendPendingMidiEvents(std::numeric_limits<uint32_t>::max());
				noteSent = true;
			}
		});

		virusLib::Device::bootDSPs(dsp1.get(), dsp2raw, rom, false);

		constexpr uint32_t kTotalSamples = 6 * 44100;
		AudioProcessor proc(rom.getSamplerate(), _wavOutFile, false, kTotalSamples, dsp1.get(), dsp2raw);
		while (!proc.finished())
		{
			sem.wait();
			proc.processBlock(blockSize);
		}

		std::cout << "Wrote " << _wavOutFile << std::endl;
		return 0;
	}

	// "hdr4_pitch_probe <note> <bendMsb> <bendLsb> [outFile]" -- work/dsp_hypersaw_master_cell_
	// sweep_findings.md's open item: HyperSaw's header formal 4 (X:$566B6, hdr4) reads $0 across
	// every static-UI-parameter sweep tried so far (Density/DetuneSpread/Semitone/Keyfollow all
	// left it untouched). The doc's own §8.2 reading ("5b8a5 copy *hdr4 -> X:$1f31 ; raw pitch
	// input", read EVERY TICK not just at voice-build) suggests hdr4 is not a static master-cell
	// UI parameter at all but a per-tick-refreshed pitch INPUT -- and since a plain note-number
	// change (60 vs 64) was never isolated as its own test in that session (mode switched to
	// HyperSaw only at the same cb the swept param changed, entangled with note-on), a real
	// pitch-bend send is the cleanest disambiguator: if hdr4 tracks bend amount while a note
	// sustains, that confirms "dynamic note-pitch/bend input, not a UI parameter" and closes the
	// item (not "pinned to a control," but "identified as a non-parameter pitch feed"). Engages
	// HyperSaw via a LIVE PARAM_CHANGE (not baked into the bulk preset) per the project's own
	// "bulk write is inert for effect-rebuild-triggering type selectors" lesson (Oscillator Model
	// is exactly that class of selector, same as Chorus Type). Two dumps in one run (baseline
	// pre-bend, then post-bend) using the same dumpRange idiom as oscwave_probe's two-snapshot
	// pattern -- families dumped: $56680-$566DF (the master-cell family incl. hdr4 itself) and
	// $1f28-$1f40 (the downstream $1f31/$1f32 pitch-pipeline scratch cells hdr4 feeds into).
	int runHdr4PitchBendProbe(int _note, int _bendMsb, int _bendLsb, const std::string& _outFile)
	{
		auto rom = ROMLoader::findROM(DeviceModel::TI2);
		if (!rom.isValid())
		{
			std::cout << "ROM not found/invalid." << std::endl;
			return 1;
		}

		Microcontroller::TPreset preset{};
		// Same base bank as the proven-working HyperSaw master-cell sweep (VocoPad XM, bank
		// 11/124) -- confirmed to actually engage HyperSaw's live rebuild path in that session.
		rom.getSingle(11, 124, preset);
		std::cout << "Using preset \"" << ROMFile::getSingleName(preset) << "\" as hdr4_pitch_probe "
			"base, note=" << _note << " bend=(" << _bendMsb << "," << _bendLsb << ")" << std::endl;

		DspSingle* dsp1raw = nullptr;
		DspSingle* dsp2raw = nullptr;
		virusLib::Device::createDspInstances(dsp1raw, dsp2raw, rom, static_cast<float>(rom.getSamplerate()));
		std::unique_ptr<DspSingle> dsp1(dsp1raw);

		Microcontroller uc(*dsp1, rom, false);
		if (dsp2raw)
			uc.addDSP(*dsp2raw, false);

		dsp56k::SpscSemaphore sem(1);
		uint32_t callbackCount = 0;
		int32_t notifyTimeout = 0;
		constexpr uint32_t blockSize = 64;
		const uint32_t notifyThreshold = blockSize > 4 ? blockSize - 4 : 0;
		std::vector<SMidiEvent> midiEvents;

		bool presetSent = false, modeSent = false, noteSent = false, bendSent = false;
		bool baselineDumped = false, postBendDumped = false;
		std::ofstream out(_outFile);

		auto& esai = dsp1->getAudio();
		esai.setCallback([&](dsp56k::Audio*)
		{
			const auto availableSize = esai.getAudioOutputs().size();
			const auto sizeReached = availableSize >= notifyThreshold;
			--notifyTimeout;
			if (notifyTimeout <= 0 && sizeReached)
			{
				notifyTimeout = static_cast<int>(notifyThreshold);
				sem.notify();
			}

			++callbackCount;
			if ((callbackCount & 0x3) != 0)
				return;

			uc.readMidiOut(midiEvents);
			const auto audioCallbackCount = callbackCount >> 2;
			uc.process();

			if (audioCallbackCount == 1)
			{
				dsp1->drainESSI1();
				uc.sendInitControlCommands(127);
			}
			else if (audioCallbackCount == 256 && !presetSent)
			{
				dsp1->drainESSI1();
				dsp1->disableESSI1();
				std::cout << "[cb " << audioCallbackCount << "] Sending preset" << std::endl;
				uc.writeSingle(BankNumber::EditBuffer, virusLib::SINGLE, preset);
				presetSent = true;
			}
			else if (audioCallbackCount == 600 && !modeSent)
			{
				std::cout << "[cb " << audioCallbackCount << "] Sending live PARAM_CHANGE Osc1 Mode=HyperSaw" << std::endl;
				synthLib::SysexBuffer sysex{
					0xf0, 0x00, 0x20, 0x33, 0x01, 0x00,
					0x6E, virusLib::SINGLE, 30, 1,
					0xf7
				};
				std::vector<SMidiEvent> responses;
				uc.sendSysex(sysex, responses, MidiEventSource::Host);
				modeSent = true;
			}
			else if (audioCallbackCount == 900 && !noteSent)
			{
				std::cout << "[cb " << audioCallbackCount << "] Sending Note On " << _note << std::endl;
				uc.sendMIDI(SMidiEvent(MidiEventSource::Host, 0x90, static_cast<uint8_t>(_note), 100));
				uc.sendPendingMidiEvents(std::numeric_limits<uint32_t>::max());
				noteSent = true;
			}
			else if (audioCallbackCount == 1050 && !baselineDumped)
			{
				out << "=== cb1050 BASELINE (post-note, pre-bend) ===\n";
				const auto& mem1 = dsp1->getMemory();
				dumpRange(mem1, dsp56k::MemArea_X, "dsp1_x", 0x56680, 0x60, out);
				dumpRange(mem1, dsp56k::MemArea_X, "dsp1_x", 0x1f28, 0x18, out);
				baselineDumped = true;
			}
			else if (audioCallbackCount == 1150 && !bendSent)
			{
				std::cout << "[cb " << audioCallbackCount << "] Sending Pitch Bend msb=" << _bendMsb
					<< " lsb=" << _bendLsb << std::endl;
				uc.sendMIDI(SMidiEvent(MidiEventSource::Host, 0xE0, static_cast<uint8_t>(_bendLsb), static_cast<uint8_t>(_bendMsb)));
				uc.sendPendingMidiEvents(std::numeric_limits<uint32_t>::max());
				bendSent = true;
			}
			else if (audioCallbackCount == 1400 && !postBendDumped)
			{
				out << "=== cb1400 POST-BEND ===\n";
				const auto& mem1 = dsp1->getMemory();
				dumpRange(mem1, dsp56k::MemArea_X, "dsp1_x", 0x56680, 0x60, out);
				dumpRange(mem1, dsp56k::MemArea_X, "dsp1_x", 0x1f28, 0x18, out);
				postBendDumped = true;
			}
		});

		virusLib::Device::bootDSPs(dsp1.get(), dsp2raw, rom, false);

		constexpr uint32_t kTotalSamples = 8 * 44100;
		AudioProcessor proc(rom.getSamplerate(), "xmem_hdr4_pitch_probe_throwaway.wav", false, kTotalSamples, dsp1.get(), dsp2raw);
		while (!proc.finished())
		{
			sem.wait();
			proc.processBlock(blockSize);
		}

		out.close();
		std::cout << "Wrote " << _outFile << std::endl;
		return 0;
	}

	// "portamento_probe <portaVal> <noteA> <noteB> [outFile]" -- work/dsp_hypersaw_master_cell_
	// sweep_part2_findings.md's flagged open follow-up: hdr4 (X:$566B6) stayed exactly $0 under
	// every pitch-bend/note-number test tried there, refuting it as a live pitch/bend input --
	// but Portamento Time was never engaged in any of those tests (Portamento Time = page
	// 112/0x70 idx 5, 0-127, 0=off), and hdr4's own prologue op (5b8a5, "copy *hdr4 -> X:$1f31")
	// feeds directly into the pitchmap op as its "raw pitch input" field, structurally exactly
	// where a glide offset would enter. Unlike runHdr4PitchBendProbe (which reused the generic
	// fx_live cb1200 live-param slot, fine for testing a steady-state pitch), a real portamento
	// glide needs the live PARAM_CHANGE enabling Portamento Time (and Osc1 Mode=HyperSaw) sent
	// BEFORE any note-on transition -- the existing fx_live/chorus_pc_trace harness fixes its
	// live-param send at cb1200, strictly *after* both of its baked-in notes (cb512/cb900), so
	// it structurally cannot catch a glide-in-progress (by cb1200 any note transition that
	// happened under Portamento=off has already snapped instantly). This mode reorders that:
	// preset -> live PARAM_CHANGE (Portamento Time + Osc1 Mode=HyperSaw) -> Note On A -> Note On
	// B (the real transition Portamento is supposed to smooth) -> several dumps at increasing
	// delays after Note B, to catch a genuinely in-progress (not yet converged) glide value.
	// Dumps both DSP1 and DSP2 for the master-cell family + the $1f28-$1f3f pitch-pipeline
	// scratch window, per this project's "check both DSPs" methodological note (part2 §3).
	int runPortamentoProbe(int _portaVal, int _noteA, int _noteB, const std::string& _outFile)
	{
		auto rom = ROMLoader::findROM(DeviceModel::TI2);
		if (!rom.isValid())
		{
			std::cout << "ROM not found/invalid." << std::endl;
			return 1;
		}

		Microcontroller::TPreset preset{};
		// Same base bank as the proven-working HyperSaw master-cell sweeps (VocoPad XM, 11/124).
		rom.getSingle(11, 124, preset);
		std::cout << "Using preset \"" << ROMFile::getSingleName(preset) << "\" as portamento_probe "
			"base, PortamentoTime=" << _portaVal << " noteA=" << _noteA << " noteB=" << _noteB << std::endl;

		DspSingle* dsp1raw = nullptr;
		DspSingle* dsp2raw = nullptr;
		virusLib::Device::createDspInstances(dsp1raw, dsp2raw, rom, static_cast<float>(rom.getSamplerate()));
		std::unique_ptr<DspSingle> dsp1(dsp1raw);

		Microcontroller uc(*dsp1, rom, false);
		if (dsp2raw)
			uc.addDSP(*dsp2raw, false);

		dsp56k::SpscSemaphore sem(1);
		uint32_t callbackCount = 0;
		int32_t notifyTimeout = 0;
		constexpr uint32_t blockSize = 64;
		const uint32_t notifyThreshold = blockSize > 4 ? blockSize - 4 : 0;
		std::vector<SMidiEvent> midiEvents;

		bool presetSent = false, liveParamsSent = false, noteASent = false, noteBSent = false;
		bool preNoteBDumped = false;
		// Checkpoints relative to Note B's cb (900 base below), spanning ~0.06s to ~14.5s post-
		// transition so a slow (val=127) glide is very likely to be caught genuinely in progress
		// at more than one of them, not just "already converged" or "hasn't started."
		const std::vector<uint32_t> relCheckpoints{ 10, 50, 150, 400, 900, 1700, 2500 };
		std::vector<bool> checkpointDumped(relCheckpoints.size(), false);
		std::ofstream out(_outFile);

		constexpr uint32_t kNoteACb = 700;
		constexpr uint32_t kNoteBCb = 900;

		auto dumpBoth = [&](const char* _label)
		{
			out << "=== " << _label << " ===\n";
			const auto& mem1 = dsp1->getMemory();
			dumpRange(mem1, dsp56k::MemArea_X, "dsp1_x", 0x56680, 0x60, out);
			dumpRange(mem1, dsp56k::MemArea_X, "dsp1_x", 0x1f28, 0x18, out);
			if (dsp2raw)
			{
				const auto& mem2 = dsp2raw->getMemory();
				dumpRange(mem2, dsp56k::MemArea_X, "dsp2_x", 0x56680, 0x60, out);
				dumpRange(mem2, dsp56k::MemArea_X, "dsp2_x", 0x1f28, 0x18, out);
			}
		};

		auto& esai = dsp1->getAudio();
		esai.setCallback([&](dsp56k::Audio*)
		{
			const auto availableSize = esai.getAudioOutputs().size();
			const auto sizeReached = availableSize >= notifyThreshold;
			--notifyTimeout;
			if (notifyTimeout <= 0 && sizeReached)
			{
				notifyTimeout = static_cast<int>(notifyThreshold);
				sem.notify();
			}

			++callbackCount;
			if ((callbackCount & 0x3) != 0)
				return;

			uc.readMidiOut(midiEvents);
			const auto audioCallbackCount = callbackCount >> 2;
			uc.process();

			if (audioCallbackCount == 1)
			{
				dsp1->drainESSI1();
				uc.sendInitControlCommands(127);
			}
			else if (audioCallbackCount == 256 && !presetSent)
			{
				dsp1->drainESSI1();
				dsp1->disableESSI1();
				std::cout << "[cb " << audioCallbackCount << "] Sending preset" << std::endl;
				uc.writeSingle(BankNumber::EditBuffer, virusLib::SINGLE, preset);
				presetSent = true;
			}
			else if (audioCallbackCount == 450 && !liveParamsSent)
			{
				// Both sent BEFORE any note-on, so Portamento Time is already active when Note
				// On B creates a real pitch transition below.
				std::cout << "[cb " << audioCallbackCount << "] Sending live PARAM_CHANGE Osc1 Mode=HyperSaw" << std::endl;
				synthLib::SysexBuffer modeSysex{
					0xf0, 0x00, 0x20, 0x33, 0x01, 0x00,
					0x6E, virusLib::SINGLE, 30, 1,
					0xf7
				};
				std::vector<SMidiEvent> responses1;
				uc.sendSysex(modeSysex, responses1, MidiEventSource::Host);

				std::cout << "[cb " << audioCallbackCount << "] Sending live PARAM_CHANGE Portamento Time = " << _portaVal << std::endl;
				synthLib::SysexBuffer portaSysex{
					0xf0, 0x00, 0x20, 0x33, 0x01, 0x00,
					0x70, virusLib::SINGLE, 5, static_cast<uint8_t>(_portaVal),
					0xf7
				};
				std::vector<SMidiEvent> responses2;
				uc.sendSysex(portaSysex, responses2, MidiEventSource::Host);
				liveParamsSent = true;
			}
			else if (audioCallbackCount == kNoteACb && !noteASent)
			{
				std::cout << "[cb " << audioCallbackCount << "] Sending Note On A = " << _noteA << std::endl;
				uc.sendMIDI(SMidiEvent(MidiEventSource::Host, 0x90, static_cast<uint8_t>(_noteA), 100));
				uc.sendPendingMidiEvents(std::numeric_limits<uint32_t>::max());
				noteASent = true;
			}
			else if (audioCallbackCount == kNoteBCb - 20 && !preNoteBDumped)
			{
				dumpBoth("cb (NoteB-20) PRE-TRANSITION (steady state on Note A)");
				preNoteBDumped = true;
			}
			else if (audioCallbackCount == kNoteBCb && !noteBSent)
			{
				std::cout << "[cb " << audioCallbackCount << "] Sending Note On B = " << _noteB
					<< " (Note A left held, no Note Off sent)" << std::endl;
				uc.sendMIDI(SMidiEvent(MidiEventSource::Host, 0x90, static_cast<uint8_t>(_noteB), 100));
				uc.sendPendingMidiEvents(std::numeric_limits<uint32_t>::max());
				noteBSent = true;
			}
			else
			{
				for (size_t i = 0; i < relCheckpoints.size(); ++i)
				{
					if (checkpointDumped[i]) continue;
					if (audioCallbackCount == kNoteBCb + relCheckpoints[i])
					{
						dumpBoth(("cb NoteB+" + std::to_string(relCheckpoints[i])).c_str());
						checkpointDumped[i] = true;
						break;
					}
				}
			}
		});

		virusLib::Device::bootDSPs(dsp1.get(), dsp2raw, rom, false);

		// Long render: last checkpoint is NoteB+2500 (~14.5s past the transition) plus margin.
		constexpr uint32_t kTotalSamples = 20 * 44100;
		AudioProcessor proc(rom.getSamplerate(), "xmem_portamento_probe_throwaway.wav", false, kTotalSamples, dsp1.get(), dsp2raw);
		while (!proc.finished())
		{
			sem.wait();
			proc.processBlock(blockSize);
		}

		out.close();
		std::cout << "Wrote " << _outFile << std::endl;
		return 0;
	}

	int runVmWatch(const std::string& _outFile)
	{
		auto rom = ROMLoader::findROM(DeviceModel::TI2);
		if (!rom.isValid())
		{
			std::cout << "ROM not found/invalid. Place a valid TI2 firmware .bin next to this executable." << std::endl;
			return 1;
		}

		Microcontroller::TPreset preset{};
		rom.getSingle(1, 0, preset); // known-safe fallback preset (bank 0/program 0 crashes the core)
		std::cout << "Using preset \"" << ROMFile::getSingleName(preset) << "\" as vm_watch base." << std::endl;

		if (preset.size() >= 305)
		{
			// Delay -- Mode off initially (toggled live below), everything else set to a real
			// audible value so the on-transition is meaningful.
			preset[112] = 0;  // Delay Mode
			preset[113] = 64; // Delay Send
			preset[114] = 64; // Delay Time
			preset[116] = 64; // Delay Feedback

			// Phaser -- same pattern. Mode=3 (not 1) matches the "sweep" defaults block's proven
			// non-zero on-value for this field (it's an enum, not a plain boolean).
			preset[212] = 0;  // Phaser Mode
			preset[213] = 64; // Phaser Mix
			preset[214] = 36; // Phaser Rate
			preset[215] = 112;// Phaser Depth
			preset[216] = 64; // Phaser Frequency

			// Reverb -- same pattern.
			preset[257] = 0;  // Reverb Mode
			preset[258] = 64; // Reverb Send
			preset[259] = 0;  // Reverb Type
			preset[260] = 64; // Reverb Time
			preset[261] = 10; // Reverb Damping
			preset[262] = 64; // Reverb Color
			preset[265] = 10; // Reverb Predelay
		}

		DspSingle* dsp1raw = nullptr;
		DspSingle* dsp2raw = nullptr;
		virusLib::Device::createDspInstances(dsp1raw, dsp2raw, rom, static_cast<float>(rom.getSamplerate()));
		std::unique_ptr<DspSingle> dsp1(dsp1raw);

		Microcontroller uc(*dsp1, rom, false);
		if (dsp2raw)
			uc.addDSP(*dsp2raw, false);

		dsp56k::SpscSemaphore sem(1);
		uint32_t callbackCount = 0;
		int32_t notifyTimeout = 0;
		constexpr uint32_t blockSize = 64;
		const uint32_t notifyThreshold = blockSize > 4 ? blockSize - 4 : 0;
		std::vector<SMidiEvent> midiEvents;

		bool presetSent = false, noteSent = false;
		bool delayOnSent = false, delayOffSent = false;
		bool phaserOnSent = false, phaserOffSent = false;
		bool reverbOnSent = false, reverbOffSent = false;
		bool programChangeSent = false, secondNoteSent = false;
		bool longTailDumped = false, finalTailDumped = false;
		// 2026-07-15 second-round additions: bracket patch-load itself more tightly (the first
		// round's earliest checkpoint was cb700, well after the initial preset send at cb256
		// finished settling), plus two FX modules not in the first candidate batch -- Filter Bank
		// (Comb/Vowel-style module, page 110 idx 19/20) and Patch Distortion (a continuous Mix
		// knob with no separate Mode toggle, page 110 idx 72) -- since Delay/Phaser/Reverb/Program
		// Change/Note-retrigger all came back negative in that first round.
		bool earlyDump1Done = false, earlyDump2Done = false;
		bool filterBankOnSent = false, filterBankOffSent = false;
		bool distortionOffSent = false, distortionOnSent = false;
		bool midBatchFinalDumped = false;

		auto sendLiveParam = [&](uint8_t _page, uint8_t _param, uint8_t _value, const char* _label, uint32_t _cb)
		{
			std::cout << "[cb " << _cb << "] Sending live PARAM_CHANGE: " << _label << " = "
				<< static_cast<int>(_value) << std::endl;
			synthLib::SysexBuffer sysex{
				0xf0, 0x00, 0x20, 0x33, 0x01, 0x00,
				_page, virusLib::SINGLE, _param, _value,
				0xf7
			};
			std::vector<SMidiEvent> responses;
			uc.sendSysex(sysex, responses, MidiEventSource::Host);
		};

		std::ofstream out(_outFile);
		out << "Mode: vm_watch (continuous VM-struct timeline across candidate triggers, single "
			   "continuous render, dumps taken in-callback)\n";
		out << "Checkpoints (each captures the SETTLED state resulting from the PREVIOUS action, "
			   "before the next action fires): cb266=after PresetLoad(tight) "
			   "cb400=PresetSettledPreNoteOn cb700=after NoteOn cb1000=after DelayON "
			   "cb1300=after DelayOFF cb1600=after PhaserON cb1900=after PhaserOFF "
			   "cb2200=after ReverbON cb2500=after ReverbOFF cb2800=after ProgramChange "
			   "cb3100=after SecondNoteOn cb3400=after FilterBankON cb3700=after FilterBankOFF "
			   "cb4000=after DistortionOFF cb4300=after DistortionON "
			   "cb20000=full-run-longtail cb30000=final-tail\n\n";

		auto& mem1 = dsp1->getMemory();
		int checkpointIdx = 0;

		auto dumpCheckpoint = [&](const char* _label, uint32_t _audioCb)
		{
			const double tSec = static_cast<double>(callbackCount) / rom.getSamplerate();
			const auto ip = mem1.get(dsp56k::MemArea_X, 0x5c69b);
			const auto busy = mem1.get(dsp56k::MemArea_X, 0x5c69c);
			const auto halt = mem1.get(dsp56k::MemArea_X, 0x5c69d);

			// Edge-triggered console line: only print when the VM leaves its documented idle
			// state (IP != $5C74A, or busy/halt != 0) -- the full timeline is in the dump file
			// regardless.
			if (ip != 0x5C74A || busy != 0 || halt != 0)
			{
				std::cout << "  [checkpoint " << checkpointIdx << " '" << _label << "', t~" << tSec
					<< "s, cb=" << _audioCb << "] NON-IDLE: DSP1 IP=$" << std::hex << std::uppercase
					<< ip << " busy=$" << busy << " halt=$" << halt << std::dec << std::endl;
			}

			out << "=== checkpoint " << checkpointIdx << " '" << _label << "' (t~" << tSec
				<< "s, audioCallbackCount=" << _audioCb << ") ===\n";
			dumpRange(mem1, dsp56k::MemArea_X, "dsp1_x", 0x5c670, 0x90, out);
			if (dsp2raw)
			{
				auto& mem2 = dsp2raw->getMemory();
				dumpRange(mem2, dsp56k::MemArea_X, "dsp2_x", 0x5c670, 0x90, out);
			}
			out.flush();
			++checkpointIdx;
		};

		auto& esai = dsp1->getAudio();
		esai.setCallback([&](dsp56k::Audio*)
		{
			const auto availableSize = esai.getAudioOutputs().size();
			const auto sizeReached = availableSize >= notifyThreshold;
			--notifyTimeout;
			if (notifyTimeout <= 0 && sizeReached)
			{
				notifyTimeout = static_cast<int>(notifyThreshold);
				sem.notify();
			}

			++callbackCount;
			if ((callbackCount & 0x3) != 0)
				return;

			uc.readMidiOut(midiEvents);
			const auto audioCallbackCount = callbackCount >> 2;
			uc.process();

			if (audioCallbackCount == 1)
			{
				dsp1->drainESSI1();
				uc.sendInitControlCommands(127);
			}
			else if (audioCallbackCount == 256 && !presetSent)
			{
				dsp1->drainESSI1();
				dsp1->disableESSI1();
				std::cout << "[cb " << audioCallbackCount << "] Sending preset" << std::endl;
				uc.writeSingle(BankNumber::EditBuffer, virusLib::SINGLE, preset);
				presetSent = true;
			}
			else if (audioCallbackCount == 266 && !earlyDump1Done)
			{
				// Bracket patch-load itself tightly: 10 ticks after cb256's preset send, well
				// before the first round's earliest checkpoint (cb700) -- catches a transient
				// patch-load crossfade the coarser original design couldn't have seen.
				dumpCheckpoint("immediately_after_preset_load", audioCallbackCount);
				earlyDump1Done = true;
			}
			else if (audioCallbackCount == 400 && !earlyDump2Done)
			{
				dumpCheckpoint("preset_settled_pre_noteon", audioCallbackCount);
				earlyDump2Done = true;
			}
			else if (audioCallbackCount == 512 && !noteSent)
			{
				std::cout << "[cb " << audioCallbackCount << "] Sending Note On" << std::endl;
				uc.sendMIDI(SMidiEvent(MidiEventSource::Host, 0x90, 60, 0x5f));
				uc.sendPendingMidiEvents(std::numeric_limits<uint32_t>::max());
				noteSent = true;
			}
			else if (audioCallbackCount == 700 && !delayOnSent)
			{
				dumpCheckpoint("post_noteon_settled", audioCallbackCount);
				sendLiveParam(112, 112, 1, "Delay Mode ON", audioCallbackCount);
				delayOnSent = true;
			}
			else if (audioCallbackCount == 1000 && !delayOffSent)
			{
				dumpCheckpoint("post_delay_on_settled", audioCallbackCount);
				sendLiveParam(112, 112, 0, "Delay Mode OFF", audioCallbackCount);
				delayOffSent = true;
			}
			else if (audioCallbackCount == 1300 && !phaserOnSent)
			{
				dumpCheckpoint("post_delay_off_settled", audioCallbackCount);
				sendLiveParam(113, 84, 3, "Phaser Mode ON", audioCallbackCount);
				phaserOnSent = true;
			}
			else if (audioCallbackCount == 1600 && !phaserOffSent)
			{
				dumpCheckpoint("post_phaser_on_settled", audioCallbackCount);
				sendLiveParam(113, 84, 0, "Phaser Mode OFF", audioCallbackCount);
				phaserOffSent = true;
			}
			else if (audioCallbackCount == 1900 && !reverbOnSent)
			{
				dumpCheckpoint("post_phaser_off_settled", audioCallbackCount);
				sendLiveParam(110, 1, 1, "Reverb Mode ON", audioCallbackCount);
				reverbOnSent = true;
			}
			else if (audioCallbackCount == 2200 && !reverbOffSent)
			{
				dumpCheckpoint("post_reverb_on_settled", audioCallbackCount);
				sendLiveParam(110, 1, 0, "Reverb Mode OFF", audioCallbackCount);
				reverbOffSent = true;
			}
			else if (audioCallbackCount == 2500 && !programChangeSent)
			{
				dumpCheckpoint("post_reverb_off_settled", audioCallbackCount);
				std::cout << "[cb " << audioCallbackCount << "] Sending Program Change (program 1)" << std::endl;
				uc.sendMIDI(SMidiEvent(MidiEventSource::Host, 0xC0, 1, 0));
				uc.sendPendingMidiEvents(std::numeric_limits<uint32_t>::max());
				programChangeSent = true;
			}
			else if (audioCallbackCount == 2800 && !secondNoteSent)
			{
				dumpCheckpoint("post_program_change_settled", audioCallbackCount);
				std::cout << "[cb " << audioCallbackCount << "] Sending second Note On (retrigger, note 64)" << std::endl;
				uc.sendMIDI(SMidiEvent(MidiEventSource::Host, 0x90, 64, 0x5f));
				uc.sendPendingMidiEvents(std::numeric_limits<uint32_t>::max());
				secondNoteSent = true;
			}
			else if (audioCallbackCount == 3100 && !filterBankOnSent)
			{
				// Second candidate batch (2026-07-15): Filter Bank (Comb/Vowel-style module,
				// page 110 idx 19/20) and Patch Distortion (page 110 idx 72) -- neither was in
				// the first round's Delay/Phaser/Reverb/ProgramChange/Note-retrigger batch, which
				// came back fully negative. Note the Program Change at cb2500 already replaced
				// the base preset, so these run against whatever "Alead   BC" has -- fine for a
				// yes/no idle-vs-triggered screen, doesn't need a controlled baseline.
				dumpCheckpoint("post_second_noteon_settled", audioCallbackCount);
				sendLiveParam(110, 19, 1, "Filter Bank Type -> real algorithm", audioCallbackCount);
				sendLiveParam(110, 20, 100, "Filter Bank Mix ON", audioCallbackCount);
				filterBankOnSent = true;
			}
			else if (audioCallbackCount == 3400 && !filterBankOffSent)
			{
				dumpCheckpoint("post_filterbank_on_settled", audioCallbackCount);
				sendLiveParam(110, 20, 0, "Filter Bank Mix OFF", audioCallbackCount);
				filterBankOffSent = true;
			}
			else if (audioCallbackCount == 3700 && !distortionOffSent)
			{
				dumpCheckpoint("post_filterbank_off_settled", audioCallbackCount);
				sendLiveParam(110, 72, 0, "Patch Distortion Mix OFF", audioCallbackCount);
				distortionOffSent = true;
			}
			else if (audioCallbackCount == 4000 && !distortionOnSent)
			{
				dumpCheckpoint("post_distortion_off_settled", audioCallbackCount);
				sendLiveParam(110, 72, 127, "Patch Distortion Mix ON", audioCallbackCount);
				distortionOnSent = true;
			}
			else if (audioCallbackCount == 4300 && !midBatchFinalDumped)
			{
				dumpCheckpoint("post_distortion_on_settled", audioCallbackCount);
				midBatchFinalDumped = true;
			}
			else if (audioCallbackCount == 20000 && !longTailDumped)
			{
				// ~1.5s after the second FX batch (cb4300) -- catches a slower/delayed reaction
				// that a tight post-action read might miss, across BOTH candidate batches.
				dumpCheckpoint("full_run_settled_longtail", audioCallbackCount);
				longTailDumped = true;
			}
			else if (audioCallbackCount == 30000 && !finalTailDumped)
			{
				dumpCheckpoint("final_tail_settle", audioCallbackCount);
				finalTailDumped = true;
			}
		});

		virusLib::Device::bootDSPs(dsp1.get(), dsp2raw, rom, false);

		// Single continuous render -- see the deadlock root-cause note above the doc comment for
		// why this must never construct a second AudioProcessor. audioCallbackCount ticks at
		// samplerate/4 (~11025 Hz @ 44100), so the last checkpoint (cb30000) lands at ~2.7s of
		// simulated audio; render 4s (176400 samples) for comfortable margin beyond it.
		constexpr uint32_t kTotalSamples = 176400; // ~4s @ 44100Hz
		std::cout << "Booted. Rendering " << kTotalSamples << " samples (~4s) in one continuous pass, "
			"dumping the VM struct at each checkpoint..." << std::endl;

		AudioProcessor proc(rom.getSamplerate(), "xmem_vm_watch_throwaway.wav", false, kTotalSamples, dsp1.get(), dsp2raw);
		while (!proc.finished())
		{
			sem.wait();
			proc.processBlock(blockSize);
		}

		std::cout << "Done. " << checkpointIdx << " checkpoints written (see console above for any "
			"non-idle ones; " << _outFile << " has the full timeline)." << std::endl;

		out.close();
		std::cout << "Wrote " << _outFile << std::endl;
		return 0;
	}

	// "rotor_timing <speedVal> <mix2Val> [outFile]" -- Rotary Speaker absolute-rotor-Hz LIVE
	// measurement (work/dsp_rotary_rotor_hz_live_measurement_findings.md). Follow-up to
	// work/dsp_rotary_chorus_cell_naming_live_sweep_findings.md sec 6 (dsp2_x:$1F20/$1F21 stayed
	// byte-identical across every live Speed sweep tried there -- a clean, reproducible negative)
	// and work/dsp_rotary_rotor_hz_static_derivation_findings.md (bit-exact static derivation of
	// the exp2/inertia-smoother/phase-accumulator chain, predicting Hz = rate_reg*Fs/4, with an
	// honestly-flagged ~2x residual vs. commonly-cited real Leslie specs). This mode differs from
	// every prior "fx_live"-family probe in two ways, each targeting a specific candidate
	// explanation for the negative result:
	//  1. It forces Chorus/Mix2 (idx104 -- confirmed via the cell-naming session's sec 3 to be
	//     Rotary's REAL on-screen Mix knob, distinct from idx105 "Chorus Mix" which the shared
	//     FX-defaults block already sets but Rotary's own program never reads) to an explicit,
	//     caller-chosen value. No prior Part-B test ever set idx104 -- if Rotary's per-sample
	//     chain gates on a nonzero Mix2 (silently bypassing the whole per-sample effect loop,
	//     including the phase accumulator, when the effect is inaudible), that alone would
	//     explain a frozen $1F21 regardless of Speed. Passing mix2Val=0 vs. a real value (e.g.
	//     100) lets this be tested directly instead of assumed.
	//  2. It sends live Speed (idx106) and live Type (idx103, ->6/Rotary) as TWO SEPARATE SysEx
	//     with a real ~18ms gap (200 audio-callback ticks = 800 samples @44100Hz) between them,
	//     Speed first -- unlike the predecessor session's tests 3/4, which sent multiple 11-byte
	//     SysEx back-to-back within the same simulated tick (zero realistic inter-message gap,
	//     nowhere close to a real ~3.5ms/message MIDI transmission time) and got garbled readback
	//     instead of a clean second build. This guarantees the Type-triggered build (confirmed
	//     build-time-only per doc/dsp56300_synth_engine.md's "Builder lineage" section) reads the
	//     caller's desired Speed value, not a stale default.
	// After the build settles, this mode samples dsp2_x:$1F20 (rate) and dsp2_x:$1F21 (phase
	// accumulator) every 100 ticks (400 samples, ~9.07ms @44100Hz -- comfortably >8x oversampled
	// relative to the static prediction's fastest ~13Hz case) for 500 samples (~4.53s total),
	// enough margin to unwrap $1F21's 24-bit wraps into a continuous phase-vs-time series and fit
	// a slope (measured Hz) even at the slowest predicted rate (~1.3Hz, ~0.77s/rotation). Output
	// records the exact integer raw-sample count (callbackCount, which increments 1:1 with real
	// rendered audio samples) rather than a pre-computed float seconds value, so a companion
	// Python script can do the unwrap+regression in double precision without any C++-side
	// rounding -- this mode's only job is to produce a clean, precisely-timestamped raw sequence.
	int runRotorTimingProbe(int _speedVal, int _mix2Val, const std::string& _outFile)
	{
		auto rom = ROMLoader::findROM(DeviceModel::TI2);
		if (!rom.isValid())
		{
			std::cout << "ROM not found/invalid. Place a valid TI2 firmware .bin next to this executable." << std::endl;
			return 1;
		}

		Microcontroller::TPreset preset{};
		rom.getSingle(11, 124, preset); // "VocoPad XM" -- same base preset the other Chorus/DSP2 probes use
		std::cout << "Using preset \"" << ROMFile::getSingleName(preset) << "\" as rotor_timing base, "
			"Speed=" << _speedVal << " Mix2=" << _mix2Val << " Fs=" << rom.getSamplerate() << std::endl;

		if (preset.size() >= 305)
		{
			// Reuse the proven FX-defaults block verbatim (Reverb/Delay/Phaser/Distortion all
			// forced on) -- work/dsp_chorus_live_program_matrix_findings.md found an earlier
			// attempt with only the Chorus fields set left DSP2_X:$1F41 (the chorus dispatch
			// pointer) at $0 for the whole render, i.e. Chorus/Rotary never actually engaged.
			preset[257] = 1;  preset[258] = 64; preset[259] = 0; preset[260] = 64;
			preset[261] = 10; preset[262] = 64; preset[265] = 10; // Reverb on

			preset[103] = 1; // Chorus/Type = Classic (NOT Rotary yet -- the live Type SysEx below
			                 // triggers the real, timed build instead of baking Rotary in cold)
			preset[104] = static_cast<uint8_t>(_mix2Val); // Chorus/Mix2 == Rotary's real Mix knob
			preset[105] = 64; // Chorus Mix (idx105 -- confirmed inert for Rotary itself, kept for
			                  // parity with the proven defaults block)
			preset[106] = 43; // Chorus Rate/Speed cold-bake default (overridden live below)
			preset[107] = 64; // Chorus Depth/Distance
			preset[108] = 32; // Chorus Delay/Mic Angle

			preset[112] = 1;  preset[113] = 64; preset[114] = 64; preset[116] = 64; // Delay on
			preset[212] = 3;  preset[213] = 64; preset[214] = 36; preset[215] = 112; preset[216] = 64; // Phaser on
			preset[228] = 1;  preset[229] = 64; preset[328] = 127; // Distortion on
		}

		DspSingle* dsp1raw = nullptr;
		DspSingle* dsp2raw = nullptr;
		virusLib::Device::createDspInstances(dsp1raw, dsp2raw, rom, static_cast<float>(rom.getSamplerate()));
		std::unique_ptr<DspSingle> dsp1(dsp1raw);

		Microcontroller uc(*dsp1, rom, false);
		if (dsp2raw)
			uc.addDSP(*dsp2raw, false);

		// JIT-block coverage tracking (same AddrTracker/DebuggerInterface technique as pc_trace/
		// chorus_pc_trace above, doc/tooling.md's "xmemProbe pc_trace mode" section) -- a cheap,
		// independent cross-check that directly discriminates two very different explanations for
		// a frozen dsp2_x:$1F20/$1F21: (a) the runtime per-tick handler chain (P:$05b758 phase
		// accumulator, P:$05b785 inertia smoother, P:$059234 exp2) never gets wired up/invoked AT
		// ALL under this trigger path (a wiring/reachability gap -- consistent with AGENTS.md's own
		// documented caveat that gearmulator's Microcontroller is a "from-scratch protocol
		// reimplementation" of the 8051 host, not the real firmware, so any real-hardware command
		// sequence needed to establish this specific runtime chain might not be replicated), vs.
		// (b) the handlers DO run repeatedly but always compute the identical steady-state output
		// (a genuine property of the smoother's math, not a reachability gap). Checked on BOTH
		// DSPs since which one runs Chorus/Rotary was never independently re-verified this session
		// (every static/live finding so far assumed dsp2_x, consistent with all prior sessions'
		// convention, but this confirms it structurally rather than by convention alone).
		AddrTracker rotorTracker1(dsp1->getDSP(), "dsp1");
		dsp1->getDSP().setDebugger(&rotorTracker1);
		std::unique_ptr<AddrTracker> rotorTracker2;
		if (dsp2raw)
		{
			rotorTracker2 = std::make_unique<AddrTracker>(dsp2raw->getDSP(), "dsp2");
			dsp2raw->getDSP().setDebugger(rotorTracker2.get());
		}

		dsp56k::SpscSemaphore sem(1);
		uint32_t callbackCount = 0;
		int32_t notifyTimeout = 0;
		constexpr uint32_t blockSize = 64;
		const uint32_t notifyThreshold = blockSize > 4 ? blockSize - 4 : 0;
		std::vector<SMidiEvent> midiEvents;

		bool presetSent = false, noteSent = false, secondNoteSent = false;
		bool mix2Sent = false, speedSent = false, typeSent = false;
		bool preCheckDumped = false;
		uint32_t fineSamplesTaken = 0;

		// 40 ticks = 160 raw samples (~3.6ms @44100Hz) -- >20x oversampled relative to the static
		// derivation doc's fastest predicted rate (~13Hz, ~77ms/rotation), so consecutive samples
		// can never differ by more than a small fraction of a full 24-bit phase wrap (safe to
		// unwrap in post-processing). 2000 samples * 40 ticks = 80000 ticks (~7.26s) of continuous
		// coverage from just after the live Type SysEx -- long enough to see the settle transition
		// AND several seconds of whatever steady-state (or non-steady-state) behavior follows it.
		constexpr uint32_t kFineIntervalCbGlobal = 40;
		constexpr uint32_t kFineSampleCountGlobal = 2000;

		auto sendLiveParam = [&](uint8_t _page, uint8_t _param, uint8_t _value, const char* _label, uint32_t _cb)
		{
			std::cout << "[cb " << _cb << "] Sending live PARAM_CHANGE: " << _label << " = "
				<< static_cast<int>(_value) << std::endl;
			synthLib::SysexBuffer sysex{
				0xf0, 0x00, 0x20, 0x33, 0x01, 0x00,
				_page, virusLib::SINGLE, _param, _value,
				0xf7
			};
			std::vector<SMidiEvent> responses;
			uc.sendSysex(sysex, responses, MidiEventSource::Host);
		};

		std::ofstream out(_outFile);
		out << "Mode: rotor_timing  Speed=" << _speedVal << " Mix2=" << _mix2Val
			<< " Fs=" << rom.getSamplerate() << "\n";
		out << "Timeline (audioCallbackCount ticks; 1 tick = 4 raw audio samples, confirmed via "
			"runVmWatch's own documented cb->real-time convention): cb256=PresetLoad(Type=Classic) "
			"cb512=NoteOn cb900=SecondNoteOn cb1100=PreCheck cb1150=Mix2Live(idx104) "
			"cb1350=SpeedLive(idx106) cb1550=TypeLive(idx103->6/Rotary), each live SysEx ~18ms "
			"(200 ticks) after the previous, then CONTINUOUS fine sampling of ALL 5 cells every "
			<< kFineIntervalCbGlobal << " ticks (~" << (kFineIntervalCbGlobal * 4.0 / rom.getSamplerate() * 1000.0)
			<< "ms) from cb" << (1550 + 10) << " onward, " << kFineSampleCountGlobal << " samples total.\n";
		out << "  A first diagnostic run (kept for context, see work/dsp_rotary_rotor_hz_live_"
			"measurement_findings.md) found dsp2_x:$566A9/$566AB take >1600 but <3200 ticks to "
			"reflect the live SysEx, THEN REVERT to their pre-live-param baseline by ~6000 ticks -- "
			"continuous fine sampling from immediately after the Type SysEx exists specifically to "
			"characterize this transient window, not just measure phase after an assumed-stable "
			"settle point.\n";
		out << "FINE line format: FINE cb=<audioCallbackCount> samples=<raw audio sample count, "
			"exact> dsp2_x:$566A9=$<type> dsp2_x:$566AB=$<speed> dsp2_x:$1F20=$<rate> "
			"dsp2_x:$1F21=$<phase> dsp2_x:$1F41=$<dispatch_ptr>\n\n";

		auto& esai = dsp1->getAudio();
		esai.setCallback([&](dsp56k::Audio*)
		{
			const auto availableSize = esai.getAudioOutputs().size();
			const auto sizeReached = availableSize >= notifyThreshold;
			--notifyTimeout;
			if (notifyTimeout <= 0 && sizeReached)
			{
				notifyTimeout = static_cast<int>(notifyThreshold);
				sem.notify();
			}

			++callbackCount;
			if ((callbackCount & 0x3) != 0)
				return;

			uc.readMidiOut(midiEvents);
			const auto audioCallbackCount = callbackCount >> 2;
			uc.process();

			if (audioCallbackCount == 1)
			{
				dsp1->drainESSI1();
				uc.sendInitControlCommands(127);
			}
			else if (audioCallbackCount == 256 && !presetSent)
			{
				dsp1->drainESSI1();
				dsp1->disableESSI1();
				std::cout << "[cb " << audioCallbackCount << "] Sending preset" << std::endl;
				uc.writeSingle(BankNumber::EditBuffer, virusLib::SINGLE, preset);
				presetSent = true;
			}
			else if (audioCallbackCount == 512 && !noteSent)
			{
				std::cout << "[cb " << audioCallbackCount << "] Sending Note On" << std::endl;
				uc.sendMIDI(SMidiEvent(MidiEventSource::Host, 0x90, 60, 0x5f));
				uc.sendPendingMidiEvents(std::numeric_limits<uint32_t>::max());
				noteSent = true;
			}
			else if (audioCallbackCount == 900 && !secondNoteSent)
			{
				std::cout << "[cb " << audioCallbackCount << "] Sending second Note On (note 64)" << std::endl;
				uc.sendMIDI(SMidiEvent(MidiEventSource::Host, 0x90, 64, 0x5f));
				uc.sendPendingMidiEvents(std::numeric_limits<uint32_t>::max());
				secondNoteSent = true;
			}
			else if (audioCallbackCount == 1100 && !preCheckDumped)
			{
				if (dsp2raw)
				{
					auto& mem2 = dsp2raw->getMemory();
					out << "=== pre_speed_change (cb=1100 samples=" << callbackCount << ") ===\n"
						<< "  dsp2_x:$566A9=$" << std::hex << std::uppercase << mem2.get(dsp56k::MemArea_X, 0x566A9)
						<< " dsp2_x:$566AB=$" << mem2.get(dsp56k::MemArea_X, 0x566AB)
						<< " dsp2_x:$1F20=$" << mem2.get(dsp56k::MemArea_X, 0x1F20)
						<< " dsp2_x:$1F21=$" << mem2.get(dsp56k::MemArea_X, 0x1F21)
						<< " dsp2_x:$1F41=$" << mem2.get(dsp56k::MemArea_X, 0x1F41) << std::dec << "\n\n";
				}
				preCheckDumped = true;
			}
			else if (audioCallbackCount == 1150 && !mix2Sent)
			{
				// Live Mix2 (idx104, confirmed Rotary's real on-screen Mix knob) -- the bulk
				// preset write above ALSO bakes _mix2Val into preset[104], but per work/dsp_
				// chorus_live_program_matrix_findings.md the bulk path is inert for chorus
				// reconfiguration, so send it live too: tests whether a live Mix2=0 (silent/
				// bypassed effect) vs. a real nonzero value changes whether the per-sample rate/
				// phase chain ever runs at all.
				sendLiveParam(0x70, 104, static_cast<uint8_t>(_mix2Val), "Chorus/Mix2", audioCallbackCount);
				mix2Sent = true;
			}
			else if (audioCallbackCount == 1350 && !speedSent)
			{
				sendLiveParam(0x70, 106, static_cast<uint8_t>(_speedVal), "Chorus/Speed", audioCallbackCount);
				speedSent = true;
			}
			else if (audioCallbackCount == 1550 && !typeSent)
			{
				sendLiveParam(0x70, 103, 6, "Chorus/Type -> Rotary", audioCallbackCount);
				typeSent = true;
			}
			else if (typeSent && audioCallbackCount > 1550 && fineSamplesTaken < kFineSampleCountGlobal &&
				dsp2raw && (audioCallbackCount - 1560) % kFineIntervalCbGlobal == 0)
			{
				auto& mem2 = dsp2raw->getMemory();
				const auto type = mem2.get(dsp56k::MemArea_X, 0x566A9);
				const auto speed = mem2.get(dsp56k::MemArea_X, 0x566AB);
				const auto rate = mem2.get(dsp56k::MemArea_X, 0x1F20);
				const auto phase = mem2.get(dsp56k::MemArea_X, 0x1F21);
				const auto dispatch = mem2.get(dsp56k::MemArea_X, 0x1F41);
				out << "FINE cb=" << audioCallbackCount << " samples=" << callbackCount
					<< " dsp2_x:$566A9=$" << std::hex << std::uppercase << type
					<< " dsp2_x:$566AB=$" << speed
					<< " dsp2_x:$1F20=$" << rate
					<< " dsp2_x:$1F21=$" << phase
					<< " dsp2_x:$1F41=$" << dispatch << std::dec << "\n";
				++fineSamplesTaken;
				if ((fineSamplesTaken % 100) == 0)
					out.flush();
			}
		});

		virusLib::Device::bootDSPs(dsp1.get(), dsp2raw, rom, false);

		// Total real-time budget: last scheduled FINE sample lands at cb 1560 +
		// kFineIntervalCbGlobal*kFineSampleCountGlobal ticks; render enough raw samples (*4/tick)
		// plus a comfortable margin to cover it.
		const uint32_t kLastFineCb = 1560 + kFineIntervalCbGlobal * kFineSampleCountGlobal;
		const uint32_t kTotalSamples = kLastFineCb * 4 + 40000; // ~+0.9s margin @44100Hz
		std::cout << "Booted. Rendering " << kTotalSamples << " samples (~"
			<< (kTotalSamples / rom.getSamplerate()) << "s), Speed=" << _speedVal
			<< " Mix2=" << _mix2Val << ", continuously sampling dsp2_x:$566A9/$566AB/$1F20/$1F21/$1F41 "
			"every " << kFineIntervalCbGlobal << " ticks from cb1560 onward..." << std::endl;

		AudioProcessor proc(rom.getSamplerate(), "xmem_rotor_timing_throwaway.wav", false, kTotalSamples, dsp1.get(), dsp2raw);
		while (!proc.finished())
		{
			sem.wait();
			proc.processBlock(blockSize);
		}

		std::cout << "Done. " << fineSamplesTaken << " FINE samples taken (of " << kFineSampleCountGlobal
			<< " scheduled)." << std::endl;

		dsp1->getDSP().setDebugger(nullptr);
		if (dsp2raw)
			dsp2raw->getDSP().setDebugger(nullptr);

		out << "\n=== JIT-block coverage (rotor_timing's AddrTracker cross-check) ===\n";
		const std::vector<std::pair<dsp56k::TWord, const char*>> rotorTargets = {
			{ 0x057da5, "func_057da5 (builder lineage entry, doc/dsp56300_synth_engine.md)" },
			{ 0x059234, "5922e/059234 (exp2 handler body)" },
			{ 0x05b78b, "5b785/05b78b (inertia smoother body)" },
			{ 0x05b75e, "5b758/05b75e (phase accumulator body)" },
		};
		writeSpeculationLegend(out);
		for (auto* tracker : { &rotorTracker1, rotorTracker2.get() })
		{
			if (!tracker)
				continue;
			out << "--- " << tracker->m_label << ": " << tracker->m_blockStarts.size()
				<< " distinct JIT blocks compiled ---\n";
			std::cout << "  [" << tracker->m_label << "] " << tracker->m_blockStarts.size()
				<< " distinct JIT blocks compiled" << std::endl;
			for (const auto& [addr, desc] : rotorTargets)
			{
				const bool startsBlock = tracker->m_blockStarts.count(addr) != 0;
				const bool covered = tracker->covers(addr);
				const char* status = startsBlock ? "BLOCK-START" : (covered ? "covered-mid-block" : "NOT REACHED");
				const char* note = speculationNote(startsBlock, addr);
				out << "  $" << std::hex << std::uppercase << addr << std::dec << "  " << status
					<< "  -- " << desc << note << "\n";
				std::cout << "    $" << std::hex << std::uppercase << addr << std::dec << " " << status
					<< " -- " << desc << note << std::endl;
			}
		}

		out.close();
		std::cout << "Wrote " << _outFile << std::endl;
		return 0;
	}

	struct Experiment
	{
		std::string name;
		uint32_t paramOffset;   // byte offset into TPreset (page*128+index)
		const char* paramLabel;
		bool wantNonZero;       // true = engaged (test), false = disengaged (control)
		uint8_t patchValue;     // value to force if no matching factory preset is found

		// If set, don't rely on the bulk preset upload to engage the parameter -- instead
		// send a real live PARAM_CHANGE SysEx (F0 00 20 33 01 <devId> <page> <part> <param>
		// <value> F7, per virusLib/microcontroller.cpp's sendSysex PAGE_A..PAGE_D handling)
		// AFTER a note is already sounding, exactly like a front-panel knob turn would.
		bool useLiveParamChange = false;
		uint8_t livePage = 0;   // e.g. 0x71 = PAGE_B
		uint8_t liveParam = 0;  // raw per-page parameter index (NOT the page*128+index byte offset)
		uint8_t liveValue = 0;
		// Audio callback count at which to send the live PARAM_CHANGE. Default (700) is well
		// after Note On (sent at cb 512) -- mimics "note already sounding, then turn the knob".
		// Set below 512 (e.g. 400) to send it *before* Note On instead -- mimics "turn the knob,
		// then play a note", which is the more common real-world case and exercises the voice
		// allocator's initial read of the parameter rather than any live re-evaluation path.
		uint32_t liveParamCallback = 400;

		// If >= 0, skip the "first matching preset" search below and load this exact bank/
		// program instead (still must satisfy the param condition -- this is just for picking
		// a *specific* one of several matches, e.g. to diff the Vocoder slot table across
		// multiple genuinely different Vocoder-engaged presets found via "vocoder_scan").
		int forcedBank = -1;
		int forcedProgram = -1;

		// If true, send a SECOND Note On a few audio callbacks after the first (chord, not
		// unison) -- a structural sanity check that the linked-list walk itself can produce a
		// node count > 1 under a condition guaranteed to allocate multiple voices, independent of
		// whatever Unison Mode does or doesn't do. If this comes back at 1 node too, that would
		// mean the walk logic (or its termination-condition assumption) is wrong, not that
		// polyphony/unison isn't duplicating voices.
		bool secondNoteOn = false;
		uint8_t secondNoteNumber = 64;
		uint32_t secondNoteCallback = 520; // must be > the first Note On's cb 512
	};

	// Known preset byte offsets (page*128+index), from source/osTIrusJucePlugin/parameterDescriptions_TI.json:
	//   Vocoder Mode:  page 113 (PAGE_B=0x71->offset 1)  idx 39  -> 1*128+39  = 167
	//   Unison Mode:   page 111 (PAGE_6F=0x6f->offset 3)  idx 120 -> 3*128+120 = 504
	const Experiment kExperiments[] = {
		{ "vocoder", 167, "Vocoder Mode", true, 1 },
		// Second, genuinely different Vocoder-engaged factory preset, for slot-table diffing --
		// "vocoder_scan" found only two factory presets with Vocoder Mode != 0 in this ROM:
		// bank 11/124 "VocoPad XM" (VocoderMode=1, the default "vocoder" experiment above) and
		// bank 16/97 "SplddVOCJL" (VocoderMode=2 -- a different vocoder *type/algorithm*, not
		// just different band/frequency settings, per the "vocoderMode" toText enum in
		// parameterDescriptions_TI.json -- min:0 max:6).
		{ "vocoder2", 167, "Vocoder Mode", true, 1, false, 0, 0, 0, 700, 16, 97 },
		{ "control", 167, "Vocoder Mode", false, 0 },
		{ "unison", 504, "Unison Mode", true, 1 },
		{ "unison_control", 504, "Unison Mode", false, 0 },
		// Same Unison Mode test, but engaged via a real live PARAM_CHANGE SysEx after the
		// note is already sounding, instead of baking the byte into the bulk preset upload --
		// the "unison"/"unison_control" pair above came back byte-for-byte identical, and the
		// leading theory is that the bulk-upload path doesn't trigger whatever re-evaluation
		// a live parameter change does. Unison Mode is page 111 = raw SysEx page byte
		// PAGE_6F=0x6f (per the offset table above), index 120, value 1 ("Twin").
		// NB: an earlier draft of this line used 0x71/39, which is actually Vocoder Mode
		// (page 113/PAGE_B idx 39, see the "vocoder" experiment above) -- caught and fixed
		// by cross-checking against parameterDescriptions_TI.json before this was ever run.
		{ "unison_live", 504, "Unison Mode", false, 0, true, 0x6f, 120, 1 },
		// Control for the control: send the exact same live PARAM_CHANGE SysEx (same page/part/
		// param, same timing at cb 700) but with value=0 -- i.e. a live no-op, since the base
		// preset's Unison Mode byte is already 0. If this comes back identical to plain
		// "unison_control" (no SysEx sent at all), that isolates "unison_live"'s differences
		// (if any) as caused by the 0->1 transition specifically, not merely by the DSP
		// processing *any* live PARAM_CHANGE command at that tick.
		{ "unison_live_control", 504, "Unison Mode", false, 0, true, 0x6f, 120, 0 },
		// Third variant: send the live PARAM_CHANGE *before* Note On (cb 400, vs. the default
		// 700 which is well after cb 512's Note On) -- "turn the unison knob, then play a note",
		// exercising the voice allocator's initial read of the parameter at note-on time, rather
		// than a live re-evaluation of an already-sounding voice (which "unison_live" above
		// showed produces no unison-specific effect in the probed region at all -- see findings).
		{ "unison_live_pretrigger", 504, "Unison Mode", false, 0, true, 0x6f, 120, 1, 400 },
		// Control for the above: same cb-400 pretrigger timing, but value=0 (no-op).
		{ "unison_live_pretrigger_control", 504, "Unison Mode", false, 0, true, 0x6f, 120, 0, 400 },
		// Isolating control: does *any* live PARAM_CHANGE sent at cb 400 (pretrigger timing)
		// perturb the $54132-$54135 list-traversal globals / $566B9 scatter-table slot a little,
		// purely from generic command-dispatch timing jitter, regardless of which parameter or
		// value is written? Uses Portamento Time (page 112/PAGE_A idx 5), value 0 vs 50 -- a
		// parameter with no plausible connection to voice allocation/unison. If this pair shows
		// the same small residual diff "unison_live_pretrigger" showed vs its own value=0
		// control, that confirms the residual is generic jitter, not unison-specific.
		// Portamento Time preset byte offset: page 112/PAGE_A(0x70)->offset 0, idx 5 -> offset 5.
		{ "inert_param_live_pretrigger_control", 5, "Portamento Time (inert)", false, 0, true, 0x70, 5, 0, 400 },
		{ "inert_param_live_pretrigger", 5, "Portamento Time (inert)", false, 0, true, 0x70, 5, 50, 400 },
		// Structural sanity check for the active-voice linked-list walk added this session (see
		// dumpVoiceLinkedList above): Unison Mode == 0 (base preset, no live SysEx at all), but
		// send a SECOND Note On (note 64, a major third above the first note 60) at cb 520, 8
		// audio callbacks after the first Note On at cb 512 -- i.e. a genuine 2-note chord, no
		// unison involved. This is guaranteed (assuming the preset is polyphonic, which "64Degee
		// MS" is by default) to result in 2 independently-allocated voices, so the linked list
		// MUST show 2 nodes here if the walk logic is correct. If this also comes back at 1 node,
		// that indicts the walk itself (wrong head-cell/sentinel assumption, wrong per-node
		// offset, or reading at the wrong time) rather than telling us anything about unison.
		{ "chord_2note", 504, "Unison Mode (unused -- chord sanity check)", false, 0, false, 0, 0, 0, 700, -1, -1, true, 64, 520 },
	};
}

namespace
{
	// "drift_watch" -- OS 4.5.1/4.5.2 Mod Matrix "drift in time" A/B probe
	// (work/dsp_modmatrix_drift_452_boundary_diff_findings.md). Boots whichever TI installer
	// .bin sits next to the executable (swap 4.5.1.04 vs 4.5.1.07 between runs), loads a factory
	// preset FROM THAT ROM (no cross-version preset-format assumptions), forces a Mod Matrix
	// Slot 1 assignment, holds one note, and samples per-voice + master-clock cells over time.
	//
	// NOTE: the fixed global addresses below are the *4.5.x-era* layout (v45104/v45107 verified
	// identical for these: L:$B17 beat latch, Y:$48633 position-in-beat, clock cells
	// Y:$53d99/$53d9a/$53da2, walker globals X:$46f96/$46f97). Do NOT use this mode against
	// 5.1.7.00 (there: L:$B57, Y:$48573, Y:$53eb7/b8/c0, X:$46eae/af).
	//
	// Per-voice bases come from X:$0 (r1, X-side) / Y:$0 (r4, Y-side), which the per-tick voice
	// walk publishes in both versions (v45104 P:$55e62-3 and the site-2 block itself). Offsets
	// +$8d/+$90..$94 are the record-walk state (v45104 == v45107 layout at this boundary).
	int runDriftWatch(const std::string& _outFile)
	{
		auto rom = ROMLoader::findROM(DeviceModel::TI2);
		if (!rom.isValid())
		{
			std::cout << "ROM not found/invalid. Place a valid TI installer .bin next to this executable." << std::endl;
			return 1;
		}

		Microcontroller::TPreset preset{};
		rom.getSingle(1, 0, preset);
		std::cout << "drift_watch: ROM loaded, base preset \"" << ROMFile::getSingleName(preset) << "\"" << std::endl;

		// Mod Matrix Slot 1 (legacy Assign1, stable preset offsets since Virus C):
		// Source=preset[192], Destination=preset[193], Amount=preset[194]. Source enum identity
		// for 4.5-era not re-verified -- any nonzero assignment suffices; the buggy path
		// (X:$B17-gated) ran per voice regardless of source choice.
		if (preset.size() > 194)
		{
			preset[192] = 10;
			preset[193] = 24; // Filter 1 Cutoff (legacy destination enum)
			preset[194] = 127;
		}

		// Engage the master clock's beat-latch path: a first run with no clock consumer showed
		// the phase accumulator (Y:$53d99/9a) advancing but L:$B17/Y:$48633 pinned at 0 for the
		// whole render -- the beat decomposition bails unless something consumes the clock.
		// LFO1 Clock (page B idx 18 -> preset[146]) nonzero = tempo-synced LFO1, no arp (the arp
		// would retrigger voices and confound the per-voice drift observation).
		if (preset.size() > 146)
		{
			preset[146] = 9; // LFO1 Clock: some real clock divider
			std::cout << "  Forcing LFO1 Clock=9 (synced LFO engages the clock path), "
				"Mod Matrix Slot1 src=10 dst=24 amt=127" << std::endl;
		}

		// Force a sustaining amp envelope -- the first "64Degee MS" run decayed to silence by
		// ~2s (verified from the rendered wav), leaving no live voice to observe.
		if (preset.size() > 63)
		{
			preset[61] = 127; // Amp Env Sustain = max
			preset[62] = 64;  // Amp Env Sustain Slope = hold
		}

		DspSingle* dsp1raw = nullptr;
		DspSingle* dsp2raw = nullptr;
		virusLib::Device::createDspInstances(dsp1raw, dsp2raw, rom, static_cast<float>(rom.getSamplerate()));
		std::unique_ptr<DspSingle> dsp1(dsp1raw);

		Microcontroller uc(*dsp1, rom, false);
		if (dsp2raw)
			uc.addDSP(*dsp2raw, false);

		AddrTracker tracker1(dsp1->getDSP(), "dsp1");
		dsp1->getDSP().setDebugger(&tracker1);
		std::unique_ptr<AddrTracker> tracker2;
		if (dsp2raw)
		{
			tracker2 = std::make_unique<AddrTracker>(dsp2raw->getDSP(), "dsp2");
			dsp2raw->getDSP().setDebugger(tracker2.get());
		}

		dsp56k::SpscSemaphore sem(1);
		uint32_t callbackCount = 0;
		int32_t notifyTimeout = 0;
		constexpr uint32_t blockSize = 64;
		const uint32_t notifyThreshold = blockSize > 4 ? blockSize - 4 : 0;
		std::vector<SMidiEvent> midiEvents;

		bool presetSent = false, noteSent = false, liveSent = false;

		std::ofstream out(_outFile);
		out << "drift_watch time series. 4.5.x-era fixed addresses (see mode comment).\n"
			"columns: cb dsp xbase ybase | X:B17 Y:B17 Y:48633 | Y:53d99 Y:53d9a Y:53da2 | "
			"Yv+91 Yv+92 Xv+8d Xv+90 Xv+91 Xv+92 Xv+93 | X:46f96 X:46f97\n\n";

		auto sampleDsp = [&](DspSingle* _dsp, const char* _tag, uint32_t _cb)
		{
			const auto& mem = _dsp->getMemory();
			const auto get = [&mem](dsp56k::EMemArea _a, uint32_t _addr) -> uint32_t
			{
				return mem.get(_a, _addr);
			};
			const uint32_t xb = get(dsp56k::MemArea_X, 0x0);
			const uint32_t yb = get(dsp56k::MemArea_Y, 0x0);
			out << std::dec << _cb << ' ' << _tag << ' '
				<< std::hex << std::nouppercase
				<< xb << ' ' << yb << " | "
				<< get(dsp56k::MemArea_X, 0xb17) << ' '
				<< get(dsp56k::MemArea_Y, 0xb17) << ' '
				<< get(dsp56k::MemArea_Y, 0x48633) << " | "
				<< get(dsp56k::MemArea_Y, 0x53d99) << ' '
				<< get(dsp56k::MemArea_Y, 0x53d9a) << ' '
				<< get(dsp56k::MemArea_Y, 0x53da2) << " | ";
			const bool xbOk = xb > 0 && xb < 0x100000 - 0x100;
			const bool ybOk = yb > 0 && yb < 0x100000 - 0x100;
			if (ybOk)
				out << get(dsp56k::MemArea_Y, yb + 0x91) << ' '
					<< get(dsp56k::MemArea_Y, yb + 0x92) << ' ';
			else
				out << "- - ";
			if (xbOk)
				out << get(dsp56k::MemArea_X, xb + 0x8d) << ' '
					<< get(dsp56k::MemArea_X, xb + 0x90) << ' '
					<< get(dsp56k::MemArea_X, xb + 0x91) << ' '
					<< get(dsp56k::MemArea_X, xb + 0x92) << ' '
					<< get(dsp56k::MemArea_X, xb + 0x93) << ' ';
			else
				out << "- - - - - ";
			out << "| "
				<< get(dsp56k::MemArea_X, 0x46f96) << ' '
				<< get(dsp56k::MemArea_X, 0x46f97);
			// Fixed-base sample of the first allocated voice (X:$49B9E / Y:$49CE8, observed
			// live in the v45104 run at cb 568 -- same X base insights.md already documents
			// for 5.1.7, so plausibly stable across 4.5.x builds too; the X:$0/Y:$0 pair above
			// usually holds the LAST-walked list node, not the active voice).
			out << " || "
				<< get(dsp56k::MemArea_Y, 0x49ce8 + 0x91) << ' '
				<< get(dsp56k::MemArea_Y, 0x49ce8 + 0x92) << ' '
				<< get(dsp56k::MemArea_X, 0x49b9e + 0x8d) << ' '
				<< get(dsp56k::MemArea_X, 0x49b9e + 0x90) << ' '
				<< get(dsp56k::MemArea_X, 0x49b9e + 0x91) << ' '
				<< get(dsp56k::MemArea_X, 0x49b9e + 0x92) << ' '
				<< get(dsp56k::MemArea_X, 0x49b9e + 0x93) << '\n';
		};

		auto& esai = dsp1->getAudio();
		esai.setCallback([&](dsp56k::Audio*)
		{
			const auto availableSize = esai.getAudioOutputs().size();
			const auto sizeReached = availableSize >= notifyThreshold;
			--notifyTimeout;
			if (notifyTimeout <= 0 && sizeReached)
			{
				notifyTimeout = static_cast<int>(notifyThreshold);
				sem.notify();
			}

			++callbackCount;
			if ((callbackCount & 0x3) != 0)
				return;

			uc.readMidiOut(midiEvents);
			const auto audioCallbackCount = callbackCount >> 2;
			uc.process();

			if (audioCallbackCount == 1)
			{
				dsp1->drainESSI1();
				uc.sendInitControlCommands(127);
			}
			else if (audioCallbackCount == 256 && !presetSent)
			{
				dsp1->drainESSI1();
				dsp1->disableESSI1();
				std::cout << "[cb " << audioCallbackCount << "] Sending preset" << std::endl;
				uc.writeSingle(BankNumber::EditBuffer, virusLib::SINGLE, preset);
				presetSent = true;
			}
			else if (audioCallbackCount == 512 && !noteSent)
			{
				std::cout << "[cb " << audioCallbackCount << "] Sending Note On" << std::endl;
				uc.sendMIDI(SMidiEvent(MidiEventSource::Host, 0x90, 60, 0x5f));
				uc.sendPendingMidiEvents(std::numeric_limits<uint32_t>::max());
				noteSent = true;
			}
			else if (audioCallbackCount == 400 && !liveSent)
			{
				// The bulk preset write is inert for rebuild-triggering selectors (documented
				// trap, insights.md) -- LFO Clock plausibly included. Re-send the clock + Mod
				// Matrix params as live PARAM_CHANGEs, the path real editors use. Sent BEFORE
				// the note-on so the voice bakes them in at allocation.
				const std::array<std::array<uint8_t, 3>, 4> lp = {{
					{0x71, 18, 9},   // LFO1 Clock = 9
					{0x71, 64, 10},  // Assign1 Source
					{0x71, 65, 24},  // Assign1 Destination
					{0x71, 66, 127}, // Assign1 Amount
				}};
				for (const auto& p : lp)
				{
					std::cout << "[cb " << audioCallbackCount << "] live PARAM_CHANGE page $"
						<< std::hex << static_cast<int>(p[0]) << std::dec << " idx "
						<< static_cast<int>(p[1]) << " = " << static_cast<int>(p[2]) << std::endl;
					synthLib::SysexBuffer sysex{
						0xf0, 0x00, 0x20, 0x33, 0x01, 0x00,
						p[0], virusLib::SINGLE, p[1], p[2],
						0xf7
					};
					std::vector<SMidiEvent> responses;
					uc.sendSysex(sysex, responses, MidiEventSource::Host);
				}
				liveSent = true;
				// Start the MIDI clock: M_START then 24-PPQN ticks (sent below). Without real
				// clock the beat-latch (L:$B17) machinery provably never engages (two full runs:
				// latch pinned 0 0 0 while the free-running phase accumulator advanced).
				std::cout << "[cb " << audioCallbackCount << "] MIDI Start + clock ticks begin (120 BPM)" << std::endl;
				uc.sendMIDI(SMidiEvent(MidiEventSource::Host, 0xfa, 0, 0));
				uc.sendPendingMidiEvents(std::numeric_limits<uint32_t>::max());
			}
			if (liveSent && (audioCallbackCount % 230) == 0)
			{
				// ~11025 audio-cbs/s (1 cb = 4 samples at 44.1k); 120 BPM = 48 ticks/s -> one
				// 0xF8 every ~230 cbs.
				uc.sendMIDI(SMidiEvent(MidiEventSource::Host, 0xf8, 0, 0));
				uc.sendPendingMidiEvents(std::numeric_limits<uint32_t>::max());
			}
			if (audioCallbackCount >= 560 && (audioCallbackCount & 0x7) == 0)
			{
				sampleDsp(dsp1.get(), "dsp1", audioCallbackCount);
				if (dsp2raw)
					sampleDsp(dsp2raw, "dsp2", audioCallbackCount);
			}
		});

		virusLib::Device::bootDSPs(dsp1.get(), dsp2raw, rom, false);

		installFaultHandler();
		g_faultDsp1 = &dsp1->getDSP();
		if (dsp2raw) g_faultDsp2 = &dsp2raw->getDSP();
		registerMemRange("dsp1_X", dsp1->getMemory().getMemAreaPtr(dsp56k::MemArea_X), 0x100000);
		registerMemRange("dsp1_Y", dsp1->getMemory().getMemAreaPtr(dsp56k::MemArea_Y), 0x100000);
		registerMemRange("dsp1_P", dsp1->getMemory().getMemAreaPtr(dsp56k::MemArea_P), 0x100000);
		if (dsp2raw)
		{
			registerMemRange("dsp2_X", dsp2raw->getMemory().getMemAreaPtr(dsp56k::MemArea_X), 0x100000);
			registerMemRange("dsp2_Y", dsp2raw->getMemory().getMemAreaPtr(dsp56k::MemArea_Y), 0x100000);
			registerMemRange("dsp2_P", dsp2raw->getMemory().getMemAreaPtr(dsp56k::MemArea_P), 0x100000);
		}

		constexpr uint32_t kTotalSamples = 12 * 44100;
		std::cout << "Booted. Rendering " << kTotalSamples << " samples (~12s), sampling drift cells every 8 audio callbacks after cb 560..." << std::endl;

		AudioProcessor proc(rom.getSamplerate(), "xmem_drift_watch_throwaway.wav", false, kTotalSamples, dsp1.get(), dsp2raw);
		while (!proc.finished())
		{
			sem.wait();
			proc.processBlock(blockSize);
		}

		dsp1->getDSP().setDebugger(nullptr);
		if (dsp2raw)
			dsp2raw->getDSP().setDebugger(nullptr);

		// Reachability report for the drift-relevant v45104 addresses (v45107 equivalents are
		// -1/-3 words off; block coverage is range-based so tiny shifts don't matter much, but
		// interpret against the right version's map):
		// $5141b = the (pre-fix) X:$B17-gated caller site, $514ca = func_0514ca body,
		// $5179a = func_05179a record-walk body, $53047 = beat-latch writer.
		const std::array<std::pair<const char*, dsp56k::TWord>, 6> pois = {{
			{"buggy-caller $5141b", 0x5141b}, {"func_0514ca $514ca", 0x514ca},
			{"func_05179a $5179a", 0x5179a}, {"latch-writer $53047", 0x53047},
			{"legit-caller $51402", 0x51402}, {"site3-block $51629", 0x51629},
		}};
		for (const auto& [name, addr] : pois)
		{
			out << "reach " << name << ": dsp1=" << (tracker1.covers(addr) ? "YES" : "no");
			if (tracker2)
				out << " dsp2=" << (tracker2->covers(addr) ? "YES" : "no");
			out << "\n";
			std::cout << "reach " << name << ": dsp1=" << (tracker1.covers(addr) ? "YES" : "no")
				<< (tracker2 ? (tracker2->covers(addr) ? " dsp2=YES" : " dsp2=no") : "") << std::endl;
		}

		out.close();
		std::cout << "drift_watch: wrote " << _outFile << std::endl;
		return 0;
	}
}

int runRotaryRender(const std::string& _outWav)
{
	auto rom = ROMLoader::findROM(DeviceModel::TI2);
	if (!rom.isValid()) return 1;

	Microcontroller::TPreset preset{};
	rom.getSingle(11, 124, preset);
	if (preset.size() >= 305)
	{
		preset[103] = 6; // Chorus Type = Rotary
		preset[105] = 64; // Chorus Mix
		preset[53] = 3;  // Filter Routing = Split Mode
		preset[54] = 64; // Filter Balance (center)
	}

	DspSingle* dsp1raw = nullptr;
	DspSingle* dsp2raw = nullptr;
	virusLib::Device::createDspInstances(dsp1raw, dsp2raw, rom, static_cast<float>(rom.getSamplerate()));
	std::unique_ptr<DspSingle> dsp1(dsp1raw);

	Microcontroller uc(*dsp1, rom, false);
	if (dsp2raw) uc.addDSP(*dsp2raw, false);

	dsp56k::SpscSemaphore sem(1);
	uint32_t callbackCount = 0;
	int32_t notifyTimeout = 0;
	constexpr uint32_t blockSize = 64;
	const uint32_t notifyThreshold = blockSize > 4 ? blockSize - 4 : 0;
	std::vector<SMidiEvent> midiEvents;
	bool presetSent = false, noteSent = false;

	auto& esai = dsp1->getAudio();
	esai.setCallback([&](dsp56k::Audio*)
	{
		const auto availableSize = esai.getAudioOutputs().size();
		if (--notifyTimeout <= 0 && availableSize >= notifyThreshold)
		{
			notifyTimeout = static_cast<int>(notifyThreshold);
			sem.notify();
		}

		if ((++callbackCount & 0x3) != 0) return;
		uc.readMidiOut(midiEvents);
		const auto audioCallbackCount = callbackCount >> 2;
		uc.process();

		if (audioCallbackCount == 1)
		{
			dsp1->drainESSI1();
			uc.sendInitControlCommands(127);
		}
		else if (audioCallbackCount == 256 && !presetSent)
		{
			dsp1->drainESSI1(); dsp1->disableESSI1();
			uc.writeSingle(BankNumber::EditBuffer, virusLib::SINGLE, preset);
			presetSent = true;
		}
		else if (audioCallbackCount == 512 && !noteSent)
		{
			uc.sendMIDI(SMidiEvent(MidiEventSource::Host, 0x90, 60, 0x5f));
			uc.sendPendingMidiEvents(std::numeric_limits<uint32_t>::max());
			noteSent = true;
		}
		else if (audioCallbackCount == 1024)
		{
			synthLib::SysexBuffer sysexBuf = {0xF0, 0x00, 0x20, 0x33, 0x01, 0x10, 0x70, 0x00, 106, 127, 0xF7};
			std::vector<SMidiEvent> throwawayResp;
			uc.sendSysex(sysexBuf, throwawayResp, MidiEventSource::Host);
		}
	});

	virusLib::Device::bootDSPs(dsp1.get(), dsp2raw, rom, false);
	constexpr uint32_t kTotalSamples = 8 * 44100;
	std::cout << "Rendering Rotary Split to " << _outWav << "..." << std::endl;
	AudioProcessor proc(rom.getSamplerate(), _outWav.c_str(), false, kTotalSamples, dsp1.get(), dsp2raw);
	while (!proc.finished())
	{
		sem.wait();
		proc.processBlock(blockSize);
	}
	std::cout << "Render complete: " << _outWav << std::endl;
	return 0;
}

// "hdi08_relay" mode -- Milestone 4 Phase B (work/8051_oracle_milestone4_design_2026-07-28.md
// section 5). Boots a real dual-DSP TI2 instance exactly like every other mode above, but instead
// of driving it with a live preset/MIDI, it replays the 8051 oracle's own recorded HDI08
// tx-dumps (--hdi08-dump/--hdi08-dump2 from tools/8051_oracle/virus8051_oracle.c) through the
// byte-triplet assembler and the real HDI08 peripheral, and records every reply word the DSP
// sends back. Usage:
//   xmemProbe hdi08_relay <firmware> --tx1 tx1.bin --tx2 tx2.bin --rx1-out rx1.bin --rx2-out rx2.bin
// --tx2/--rx2-out are optional (single-DSP ROMs, or a DSP1-only check).
//
// ENDIANNESS -- corrects an implicit assumption in the design doc, found while implementing this
// mode (2026-07-28, same day as hdi08_triplet_assembler.h's own HLEND-direction correction; see
// that header's file comment for the assembler's own derivation, which this does NOT re-litigate
// or modify). The design doc's section 4 says "every known transfer on this path sets HLEND=1
// ... and leaves it" -- true for the *tail* of a recording, false for the *bulk* of it:
//
//   Live-tracing a fresh oracle run (--trace, grepping for hdi08_icr) shows the firmware's FIRST
//   ever write to ICR happens at CODE:0x51ce/0x51d3 ("MOV A,#0x31" / "MOVX @DPTR,A") -- and that
//   is the instruction immediately after the boot-chunk-transfer loop's own exit path
//   (CODE:0x51bf "MOV A,R7" / 0x51c0 "JZ 0x51cb" / 0x51cb "LCALL 0x5feb", the chunk-chain's
//   completion handler). The chunk-transfer loop itself (CODE:0x519d-0x51b6, an inline
//   R0/R1/R2->TXH/TXM/TXL triplet write, NOT a call to CODE:0x6113) never touches ICR at all. So
//   the ~489,510-byte / 163,170-word boot chunk stream -- the overwhelming majority of any
//   recording -- is written entirely BEFORE HLEND is ever configured to 1, under whatever the
//   hardware's power-on-reset state is. Reassembling that region with the assembler's hlend=false
//   (H-major, "big-endian... matching the name") formula reproduces gearmulator's OWN
//   already-parsed ROMFile::getBootRom()/getCommandStream() exactly (this is the section-9.2
//   cross-check below) -- consistent with why check_dsp_stream.py's byte-level check already
//   passes on this same data without any HLEND reasoning at all: ROMFile::readChunks() parses the
//   firmware image with the identical naive (buf[0]<<16)|(buf[1]<<8)|buf[2] formula, so
//   "hlend=false on the recorded wire bytes" and "the image's own stored big-endian words" are
//   the same computation here.
//
//   Only the short TAIL written after that first ICR=0x31 write -- empirically 4 words on a real
//   recording, and they reproduce virusLib::Microcontroller::sendInitControlCommands's own
//   {0xF4F473, 0x407F00, 0xF4F473, 0x401000} literal EXACTLY under the assembler's documented
//   hlend=true (L-major) formula -- actually runs under HLEND=1.
//
// So this mode reassembles the recorded stream in TWO pieces with two different _hlend values,
// split at a boundary computed from the ROM itself (2 header words + getBootRom().data.size() +
// getCommandStream().size(), all hlend=false), not a hardcoded byte offset. The RX (DSP-to-host)
// direction is disassembled with hlend=true throughout, since by the time the DSP could plausibly
// reply, ICR=0x31 is already the live state on every known path -- consistent with, but not
// itself proof of, the assembler header's own "what is NOT independently confirmed" caveat about
// the RX direction. Full trace: work/8051_oracle_milestone4_phaseB_findings_2026-07-28.md.
namespace
{
	int64_t nowNs()
	{
		return std::chrono::duration_cast<std::chrono::nanoseconds>(
			std::chrono::steady_clock::now().time_since_epoch()).count();
	}

	struct Hdi08RelayInput
	{
		std::string label;
		std::vector<virusOracle::TWord> chunkWords;      // hlend=false region: 2 header words + bootRom.data + commandStream, ALL of it (used for the section-9.2 cross-check only)
		std::vector<virusOracle::TWord> commandStreamWords;  // the commandStream SLICE of chunkWords -- what DspSingle::boot() actually wants as its _commandStream parameter (the boot ROM itself is handled separately, via boot()'s own P-memory poke of the _bootRom argument; feeding the header+bootROM words too would make the boot ROM's own loader misinterpret them as bogus commands)
		std::vector<virusOracle::TWord> handshakeWords;  // hlend=true region, after the firmware's first ICR=0x31 write
		bool crossCheckPass = false;
	};

	// Splits a recorded HDI08 tx-dump into its two endianness regions (see the mode's own comment
	// above) and cross-checks the hlend=false region against the ROM's own already-parsed boot
	// ROM / command stream (design doc section 9.2). Returns false only on a structural failure
	// (short/malformed input); a cross-check MISMATCH is reported but does not itself return
	// false, so the caller can still decide what to do (see main()'s dispatch below).
	bool prepareHdi08RelayInput(const std::string& _label, const std::vector<uint8_t>& _raw,
		const ROMFile::BootRom& _bootRom, const std::vector<virusOracle::TWord>& _cmdStream,
		Hdi08RelayInput& _out)
	{
		_out.label = _label;

		const size_t chunkStreamWords = 2 + _bootRom.data.size() + _cmdStream.size();
		const size_t chunkStreamBytes = chunkStreamWords * 3;

		if (_raw.size() < chunkStreamBytes)
		{
			std::cout << "[" << _label << "] recorded stream (" << _raw.size() << " bytes) is shorter than "
				"the boot chunk stream this ROM expects (" << chunkStreamBytes << " bytes, "
				<< chunkStreamWords << " words) -- cannot proceed." << std::endl;
			return false;
		}

		const std::vector<uint8_t> chunkBytes(_raw.begin(), _raw.begin() + static_cast<long>(chunkStreamBytes));
		std::vector<uint8_t> tailBytes(_raw.begin() + static_cast<long>(chunkStreamBytes), _raw.end());

		try
		{
			_out.chunkWords = virusOracle::assembleStream(chunkBytes, /*_hlend=*/false);
		}
		catch (const std::exception& e)
		{
			std::cout << "[" << _label << "] failed to assemble the chunk-stream region: " << e.what() << std::endl;
			return false;
		}

		if (tailBytes.size() % 3 != 0)
		{
			const auto drop = tailBytes.size() % 3;
			std::cout << "[" << _label << "] " << tailBytes.size() << " trailing bytes after the chunk stream "
				"are not a multiple of 3 -- dropping the last " << drop << " incomplete byte(s)." << std::endl;
			tailBytes.resize(tailBytes.size() - drop);
		}
		try
		{
			_out.handshakeWords = virusOracle::assembleStream(tailBytes, /*_hlend=*/true);
		}
		catch (const std::exception& e)
		{
			std::cout << "[" << _label << "] failed to assemble the post-boot handshake tail: " << e.what() << std::endl;
			return false;
		}

		// section 9.2 cross-check
		bool pass = true;
		auto reportMismatch = [&](const std::string& _what, uint32_t _actual, uint32_t _expected)
		{
			std::cout << "[" << _label << "] MISMATCH " << _what << ": reassembled 0x" << std::hex << _actual
				<< ", ROM's own parse 0x" << _expected << std::dec << std::endl;
			pass = false;
		};

		if (_out.chunkWords[0] != _bootRom.size)
			reportMismatch("bootROM size word", _out.chunkWords[0], _bootRom.size);
		if (_out.chunkWords[1] != _bootRom.offset)
			reportMismatch("bootROM load-address word", _out.chunkWords[1], _bootRom.offset);
		for (size_t i = 0; i < _bootRom.data.size() && pass; ++i)
		{
			if (_out.chunkWords[2 + i] != _bootRom.data[i])
				reportMismatch("bootROM instruction word " + std::to_string(i), _out.chunkWords[2 + i], _bootRom.data[i]);
		}
		const size_t cmdBase = 2 + _bootRom.data.size();
		for (size_t i = 0; i < _cmdStream.size() && pass; ++i)
		{
			if (_out.chunkWords[cmdBase + i] != _cmdStream[i])
				reportMismatch("commandStream word " + std::to_string(i), _out.chunkWords[cmdBase + i], _cmdStream[i]);
		}

		// What DspSingle::boot() actually wants as its _commandStream argument: JUST the
		// commandStream slice, not the 2 header words + bootROM instruction words that precede it
		// in the recorded stream -- those are redundant with (and, if fed over HDI08 to a DSP
		// whose P-memory the caller already poked separately via _bootRom, actively misinterpreted
		// by) the boot ROM's own command dispatcher. See this file's own comment above
		// runHdi08Relay for the full reasoning; this bug was caught by a first live run hanging
		// indefinitely (work/8051_oracle_milestone4_phaseB_findings_2026-07-28.md).
		if (cmdBase <= _out.chunkWords.size())
			_out.commandStreamWords.assign(_out.chunkWords.begin() + static_cast<long>(cmdBase), _out.chunkWords.end());

		_out.crossCheckPass = pass;
		std::cout << "[" << _label << "] section 9.2 cross-check: " << (pass ? "PASS" : "FAIL")
			<< " -- " << _out.chunkWords.size() << " chunk-stream words (hlend=false) + "
			<< _out.handshakeWords.size() << " handshake-tail words (hlend=true)" << std::endl;
		return true;
	}

	int runHdi08Relay(const std::string& _firmwarePath, const std::string& _tx1Path, const std::string& _tx2Path,
		const std::string& _rx1OutPath, const std::string& _rx2OutPath)
	{
		auto rom = ROMLoader::findROM(_firmwarePath, DeviceModel::TI2);
		if (!rom.isValid())
		{
			std::cout << "ROM not found/invalid: \"" << _firmwarePath << "\"" << std::endl;
			return 1;
		}

		std::vector<uint8_t> tx1Bytes;
		if (!baseLib::filesystem::readFile(tx1Bytes, _tx1Path))
		{
			std::cout << "Failed to read --tx1 " << _tx1Path << std::endl;
			return 1;
		}

		bool haveTx2 = !_tx2Path.empty();
		std::vector<uint8_t> tx2Bytes;
		if (haveTx2 && !baseLib::filesystem::readFile(tx2Bytes, _tx2Path))
		{
			std::cout << "Failed to read --tx2 " << _tx2Path << std::endl;
			return 1;
		}

		DspSingle* dsp1raw = nullptr;
		DspSingle* dsp2raw = nullptr;
		virusLib::Device::createDspInstances(dsp1raw, dsp2raw, rom, static_cast<float>(rom.getSamplerate()));
		std::unique_ptr<DspSingle> dsp1(dsp1raw);

		if (dsp2raw && !haveTx2)
			std::cout << "Warning: this ROM has a second DSP but no --tx2 was given -- DSP2 will not be booted." << std::endl;
		if (!dsp2raw && haveTx2)
		{
			std::cout << "Warning: this ROM has only one DSP -- --tx2 is ignored." << std::endl;
			haveTx2 = false;
		}

		// NOTE 2026-08-01: `ROMFile::getCommandStream()` does not exist on the pinned gearmulator
		// (26cec557) -- `m_commandStream` is private and has no accessor. This mode has therefore
		// never compiled in this tree; the call was added on 2026-07-31 after the last successful
		// build and was never exercised. Left as a hard stop rather than guessed at, because
		// `_cmdStream.size()` is load-bearing: it decides where the boot chunk stream ends in the
		// recorded HDI08 dump, so substituting an empty vector would silently mis-split the input.
		// To revive: reimplement the chunk parse over the public `rom.getRomFileData()`.
		std::cout << "hdi08_relay is unavailable on this gearmulator revision (ROMFile has no public "
			"command-stream accessor). See the comment at this line." << std::endl;
		return 1;
#if 0
		const auto& bootRom = rom.getBootRom();
		const auto& cmdStream = rom.getCommandStream();
		std::cout << "ROM's own boot ROM: " << bootRom.data.size() << " words at P:$" << std::hex << bootRom.offset
			<< std::dec << "; command stream: " << cmdStream.size() << " words." << std::endl;

		Hdi08RelayInput in1;
		if (!prepareHdi08RelayInput("dsp1", tx1Bytes, bootRom, cmdStream, in1))
			return 1;

		Hdi08RelayInput in2;
		if (haveTx2 && !prepareHdi08RelayInput("dsp2", tx2Bytes, bootRom, cmdStream, in2))
			return 1;

		struct Capture
		{
			std::vector<uint8_t> rxBytes;
			std::vector<std::pair<uint64_t, uint32_t>> rxLog;  // (DSP instruction count, word)
			std::vector<uint64_t> rxSamplePos;                 // rendered-sample position of each word
		};
		Capture cap1, cap2;
		std::atomic<bool> stop{false};
		std::atomic<int64_t> lastActivityNs{nowNs()};

		// Progress is measured in RENDERED AUDIO SAMPLES, not wall time -- see the audio-pump
		// block below for why. The poller threads stamp lastActivitySamples so the main thread's
		// idle test is "no TX for N rendered samples", which is what the DSP actually experiences.
		std::atomic<uint64_t> renderedSamples{0};
		std::atomic<uint64_t> lastActivitySamples{0};
		std::atomic<uint64_t> rxWordCount{0};

		// Poll hasTX() before ever calling readTX() -- readTX() blocks on empty
		// (dsp56kEmu::HDI08::readTX(), hdi08.cpp: "m_dataTX.waitNotEmpty()"). The ring buffer is
		// internally lock-guarded (RingBuffer<TWord,8192,true>), so this is safe to run on its own
		// thread concurrently with the DSP's own execution thread.
		auto pollLoop = [&](DspSingle* _dsp, Capture& _cap)
		{
			auto& hdi08 = _dsp->getHDI08();
			while (!stop.load(std::memory_order_relaxed))
			{
				if (hdi08.hasTX())
				{
					const auto w = hdi08.readTX();
					const auto t = virusOracle::disassembleWord(w, /*_hlend=*/true);
					_cap.rxBytes.push_back(t.h);
					_cap.rxBytes.push_back(t.m);
					_cap.rxBytes.push_back(t.l);
					_cap.rxLog.emplace_back(_dsp->getDSP().getInstructionCounter(), w);
					_cap.rxSamplePos.push_back(renderedSamples.load(std::memory_order_relaxed));
					lastActivityNs.store(nowNs(), std::memory_order_relaxed);
					lastActivitySamples.store(renderedSamples.load(std::memory_order_relaxed), std::memory_order_relaxed);
					rxWordCount.fetch_add(1, std::memory_order_relaxed);
				}
				else
				{
					std::this_thread::sleep_for(std::chrono::microseconds(200));
				}
			}
		};

		std::thread poller1(pollLoop, dsp1.get(), std::ref(cap1));
		std::thread poller2;
		if (haveTx2)
			poller2 = std::thread(pollLoop, dsp2raw, std::ref(cap2));

		// Step 1 (design doc section 5): boot exactly via DspSingle::boot(), unmodified -- same
		// mechanism every other mode's Device::bootDSPs() ultimately calls, just fed the relay's
		// OWN reassembled commandStreamWords slice instead of rom.getCommandStream() directly, so
		// this mode actually exercises the recorded oracle data rather than silently substituting
		// gearmulator's internal copy. boot() pokes bootRom into P-memory directly (the
		// boot-ROM-over-HDI08 shortcut the design doc's section 2 explicitly says not to
		// re-verify) and feeds ONLY the command-stream words via HDI08::writeRX internally, using
		// its own read-rx callback to drip-feed the rest as the DSP consumes them -- NOT the full
		// chunkWords (which also carries the 2 header words + bootROM instruction words the
		// section-9.2 cross-check above needed but boot()'s own loader does not expect over HDI08).
		std::cout << "Booting DSP1 (" << in1.commandStreamWords.size() << "-word command stream)..." << std::endl;
		auto loader1 = dsp1->boot(bootRom, in1.commandStreamWords);
		dsp1->startDSPThread(false);

		std::thread loader2;
		if (haveTx2)
		{
			std::cout << "Booting DSP2 (" << in2.commandStreamWords.size() << "-word command stream)..." << std::endl;
			loader2 = dsp2raw->boot(bootRom, in2.commandStreamWords);
			dsp2raw->startDSPThread(false);
		}

		loader1.join();
		std::cout << "DSP1 command stream fully delivered (" << in1.commandStreamWords.size() << " words consumed)." << std::endl;
		if (loader2.joinable())
		{
			loader2.join();
			std::cout << "DSP2 command stream fully delivered (" << in2.commandStreamWords.size() << " words consumed)." << std::endl;
		}

		// Step 1.25 (added 2026-07-29): CLOCK THE DSP WITH REAL AUDIO FRAMES.
		//
		// This is what every previous Phase B run was missing, and the reason all of them captured
		// exactly 0 reply bytes on both DSPs (work/8051_oracle_milestone4_phaseB_findings_ and
		// _hostflag_and_idlewindow_2026-07-28.md, which tested the two candidate explanations then
		// on record -- host flags and a 10x-wider idle window -- and found neither changed the
		// result; both were sound tests of the wrong thing).
		//
		// A DspSingle only advances when its ESAI/ESSI audio peripheral is fed and drained: the
		// emulated peripheral blocks the DSP thread when its input ring runs dry or its output ring
		// fills (dsp56kEmu Audio::readRX/writeTX wait on those ring buffers). Nothing in the relay
		// ever called processAudio, so after boot() delivered the command stream the DSP ran only
		// until it first touched the ESAI and then blocked -- long before any HDI08 TX.
		//
		// gearmulator's own boot path says exactly this, in code: virusLib::Device's constructor
		// (device.cpp:63-65) does "while(!m_mc->dspHasBooted()) dummyProcess(8);" -- it PUMPS AUDIO
		// in a loop waiting for the DSP's boot-complete reply. That reply is a real HDI08 TX
		// message: Hdi08TxParser's own g_knownPatterns table (hdi08TxParser.cpp:15-18) lists
		// {0xf40000, 0x7f0000} as "sent after DSP has booted", and matching it is what sets
		// m_dspHasBooted. So the DSP does reply -- but only if it is being clocked.
		//
		// Wall-clock windows are therefore the wrong unit for this mode: the DSP's own notion of
		// elapsed time is rendered samples. Both stopping conditions below are counted in samples.
		constexpr uint32_t kBlockSize = 64;
		std::vector<uint32_t> audioInL(kBlockSize, 0), audioInR(kBlockSize, 0);
		std::vector<uint32_t> audioOutL(kBlockSize, 0), audioOutR(kBlockSize, 0);
		synthLib::TAudioInputsInt audioIns{};
		synthLib::TAudioOutputsInt audioOuts{};
		audioIns[0] = audioInL.data();
		audioIns[1] = audioInR.data();
		audioOuts[0] = audioOutL.data();
		audioOuts[1] = audioOutR.data();

		// dsp1 is really a DspMultiTI for a TI/TI2 ROM (Device::createDspInstances), whose
		// processAudio override drives BOTH DSPs' ESAI/ESAI_1 chain -- so this must be called on
		// dsp1 only, never separately on dsp2raw. Silent inputs, discarded outputs: this mode
		// cares about HDI08 traffic, not audio (same "throwaway audio" pattern every other
		// xmemProbe mode uses via virusConsoleLib::AudioProcessor).
		const auto pumpOneBlock = [&]()
		{
			dsp1->processAudio(audioIns, audioOuts, kBlockSize, kBlockSize);
			renderedSamples.fetch_add(kBlockSize, std::memory_order_relaxed);
		};

		constexpr uint64_t kBootReplyCapSamples = 44100ull * 4;   // ~4s of audio to see a first TX word
		std::cout << "Clocking the DSP with audio until its first TX word (cap "
			<< kBootReplyCapSamples << " samples)..." << std::endl;
		while (rxWordCount.load(std::memory_order_relaxed) == 0 &&
			renderedSamples.load(std::memory_order_relaxed) < kBootReplyCapSamples)
			pumpOneBlock();
		std::cout << "After " << renderedSamples.load() << " rendered samples: "
			<< rxWordCount.load() << " TX word(s) captured so far." << std::endl;

		// Step 1.5: reproduce the host-flag transition the real ICR=0x31 write also carries.
		// doc/8051_boot_and_memory_map.md's decode of CODE:0x6113's ICR write ("0x31 decodes to
		// RREQ | HF1 | HLEND") already established this bit is set at exactly the boundary this
		// mode's own header comment identifies (CODE:0x51ce/0x51d3's ICR=0x31, "on both DSP
		// blocks") -- HF1=1, HF0=0 (unset in 0x31). The recorded tx-dump only captures
		// TXH/TXM/TXL writes (--hdi08-dump), so this transition is invisible to
		// prepareHdi08RelayInput and every earlier Phase B run silently dropped it, despite
		// already having decoded it. gearmulator's own already-validated boot path
		// (Microcontroller::sendInitControlCommands, used by every non-oracle xmemProbe mode)
		// calls writeHostBitsWithWait(0, 1) as its very first action, immediately before sending
		// the literal {0xF4F473, 0x407F00, 0xF4F473, 0x401000} -- exactly in1/in2.handshakeWords
		// under this recording. Reproduce that ordering here, unconditionally (the real ICR write
		// happens regardless of whether a given recording captured a non-empty tail).
		dsp1->getHDI08().setHostFlagsWithWait(0, 1);
		if (haveTx2)
			dsp2raw->getHDI08().setHostFlagsWithWait(0, 1);

		// Step 2: whatever the recording shows after the chunk stream -- deliver it too, via a
		// direct HDI08::writeRX (not boot()'s auto-feed machinery, which only exists for the
		// initial command stream), so the relay reproduces 100% of the recorded bytes, not just
		// the portion boot() already knows how to drive.
		if (!in1.handshakeWords.empty())
		{
			std::cout << "Feeding DSP1's post-boot handshake tail (" << in1.handshakeWords.size() << " words)..." << std::endl;
			dsp1->getHDI08().writeRX(in1.handshakeWords);
		}
		if (haveTx2 && !in2.handshakeWords.empty())
		{
			std::cout << "Feeding DSP2's post-boot handshake tail (" << in2.handshakeWords.size() << " words)..." << std::endl;
			dsp2raw->getHDI08().writeRX(in2.handshakeWords);
		}

		// Step 3/4: TX input is now fully exhausted on the host side; run until a short idle
		// window produces no new TX, then stop -- mirroring the 8051 oracle's own --idle-stop
		// concept, per the design doc. A hard safety cap prevents an infinite wait if the DSP
		// never settles (e.g. it's stuck emitting a periodic telemetry word forever).
		//
		// lastActivityNs was initialized once at function entry, well before the ROM load / boot
		// / cross-check above (which can easily take longer than the idle window itself) -- reset
		// it here, right as the wait actually begins, or the very first poll below would already
		// see more than kIdleWindowNs of (spurious) "idle" time and exit before giving the DSP any
		// real chance to reply. Caught by a second live run producing 0 captured bytes in well
		// under a second of wall time despite a 30s hard cap
		// (work/8051_oracle_milestone4_phaseB_findings_2026-07-28.md).
		// (2026-07-29) Both windows are now counted in RENDERED SAMPLES, not wall time -- see the
		// audio-pump block above. A wall-clock window measures how long the host thread slept, which
		// says nothing about how much the DSP advanced when nothing was clocking it; that is what
		// made the earlier 1s-vs-10s idle-window A/B uninformative rather than a real negative.
		lastActivityNs.store(nowNs(), std::memory_order_relaxed);
		lastActivitySamples.store(renderedSamples.load(std::memory_order_relaxed), std::memory_order_relaxed);
		constexpr uint64_t kIdleSamples = 44100ull / 2;      // 0.5s of audio with no new TX -> done
		constexpr uint64_t kHardCapSamples = 44100ull * 20;  // 20s of audio total, then stop regardless
		std::cout << "Rendering until " << kIdleSamples << " samples pass with no new TX (hard cap "
			<< kHardCapSamples << " samples)..." << std::endl;
		for (;;)
		{
			pumpOneBlock();
			const auto rendered = renderedSamples.load(std::memory_order_relaxed);
			if (rendered - lastActivitySamples.load(std::memory_order_relaxed) >= kIdleSamples)
				break;
			if (rendered >= kHardCapSamples)
			{
				std::cout << "Hit the " << kHardCapSamples << "-sample safety cap while TX was still active -- "
					"stopping anyway (this is a real finding, not a bug: the DSP kept sending)." << std::endl;
				break;
			}
		}
		std::cout << "Rendered " << renderedSamples.load() << " samples total." << std::endl;

		stop.store(true);
		poller1.join();
		if (poller2.joinable())
			poller2.join();

		std::cout << "DSP1: captured " << cap1.rxBytes.size() << " reply bytes (" << cap1.rxLog.size() << " words)." << std::endl;
		if (haveTx2)
			std::cout << "DSP2: captured " << cap2.rxBytes.size() << " reply bytes (" << cap2.rxLog.size() << " words)." << std::endl;

		// Print the head of each capture as raw 24-bit words with the rendered-sample position they
		// arrived at. This is the actual evidence a follow-up session reads (e.g. whether the first
		// two words are Hdi08TxParser's own documented boot pattern F40000/7F0000); the .bin files
		// hold the same data byte-wise but say nothing about ordering or timing.
		const auto printHead = [](const char* _label, const Capture& _cap)
		{
			if (_cap.rxLog.empty())
				return;
			const size_t n = std::min<size_t>(_cap.rxLog.size(), 64);
			std::cout << "[" << _label << "] first " << n << " TX word(s) (sample@ / DSP instr / word):" << std::endl;
			for (size_t i = 0; i < n; ++i)
			{
				char buf[128];
				snprintf(buf, sizeof(buf), "  [%3zu] sample@%-8llu instr=%-12llu %06x",
					i, static_cast<unsigned long long>(i < _cap.rxSamplePos.size() ? _cap.rxSamplePos[i] : 0),
					static_cast<unsigned long long>(_cap.rxLog[i].first), _cap.rxLog[i].second);
				std::cout << buf << std::endl;
			}
		};
		printHead("dsp1", cap1);
		if (haveTx2)
			printHead("dsp2", cap2);

		if (!baseLib::filesystem::writeFile(_rx1OutPath, cap1.rxBytes))
		{
			std::cout << "Failed to write " << _rx1OutPath << std::endl;
			return 1;
		}
		std::cout << "Wrote " << _rx1OutPath << " (" << cap1.rxBytes.size() << " bytes)" << std::endl;

		if (haveTx2 && !_rx2OutPath.empty())
		{
			if (!baseLib::filesystem::writeFile(_rx2OutPath, cap2.rxBytes))
			{
				std::cout << "Failed to write " << _rx2OutPath << std::endl;
				return 1;
			}
			std::cout << "Wrote " << _rx2OutPath << " (" << cap2.rxBytes.size() << " bytes)" << std::endl;
		}

		const bool allPass = in1.crossCheckPass && (!haveTx2 || in2.crossCheckPass);
		std::cout << "Overall section 9.2 cross-check: " << (allPass ? "PASS" : "FAIL") << std::endl;
		return allPass ? 0 : 2;
#endif	// hdi08_relay: see the getCommandStream note at the top of this function
	}
}

int main(int _argc, const char* _argv[])
{
	const std::string modeArg = _argc > 1 ? _argv[1] : "vocoder";

	// "speculation_selftest" -- the both-directions gate on the BLOCK-START speculative-risk flag.
	// Deliberately FIRST and ROM-free: it must be runnable even when the emulator cannot boot, and
	// nothing about it should depend on a container's state. See runSpeculationSelftest above.
	if (modeArg == "speculation_selftest")
		return runSpeculationSelftest();

	// "hdi08_relay <firmware> --tx1 tx1.bin [--tx2 tx2.bin] --rx1-out rx1.bin [--rx2-out rx2.bin]"
	// -- Milestone 4 Phase B, see runHdi08Relay's own comment above for the full design.
	if (modeArg == "hdi08_relay")
	{
		if (_argc < 3)
		{
			std::cout << "usage: xmemProbe hdi08_relay <firmware> --tx1 tx1.bin [--tx2 tx2.bin] "
				"--rx1-out rx1.bin [--rx2-out rx2.bin]" << std::endl;
			return 1;
		}
		const std::string firmwarePath = _argv[2];
		std::string tx1Path, tx2Path, rx1OutPath, rx2OutPath;
		for (int i = 3; i < _argc; ++i)
		{
			const std::string arg = _argv[i];
			if (arg == "--tx1" && i + 1 < _argc)
				tx1Path = _argv[++i];
			else if (arg == "--tx2" && i + 1 < _argc)
				tx2Path = _argv[++i];
			else if (arg == "--rx1-out" && i + 1 < _argc)
				rx1OutPath = _argv[++i];
			else if (arg == "--rx2-out" && i + 1 < _argc)
				rx2OutPath = _argv[++i];
			else
				std::cout << "hdi08_relay: ignoring unrecognized argument \"" << arg << "\"" << std::endl;
		}
		if (tx1Path.empty() || rx1OutPath.empty())
		{
			std::cout << "hdi08_relay: --tx1 and --rx1-out are required." << std::endl;
			return 1;
		}
		return runHdi08Relay(firmwarePath, tx1Path, tx2Path, rx1OutPath, rx2OutPath);
	}

	// "pc_coverage --out <prefix> [--preset b:p ...] [--slot N] [--no-cc] [--bank-sweep B]
	//              [--param page:index:value ...] [--jit-control] [--pdump lo:hi ...]"
	// Whole-image DSP execution coverage; see runPcCoverage's comment for what the number means and,
	// more importantly, what an UNEXECUTED address does not mean.
	if (modeArg == "pc_coverage")
	{
		std::string outPrefix = "pc_coverage";
		std::vector<std::pair<int, int>> presets;
		uint32_t slot = 800;
		uint32_t maxSamples = 0;
		uint32_t firstSlot = 256;
		int watchdogSecs = 0;
		bool sweepControls = true;
		bool jitControl = false;						// T19 2026-08-02, --jit-control
		dsp56k::TWord icacheBase = 0;					// 2026-08-07, --icache-model <base>, 0 = off
		std::vector<std::array<uint8_t, 3>> liveParams;	// T12 2026-08-02, --param page:idx:value
		std::vector<std::pair<uint32_t, uint32_t>> pdumpRanges;	// 2026-08-02, --pdump lo:hi
		for (int i = 2; i < _argc; ++i)
		{
			const std::string arg = _argv[i];
			if (arg == "--out" && i + 1 < _argc)
				outPrefix = _argv[++i];
			else if (arg == "--slot" && i + 1 < _argc)
				slot = static_cast<uint32_t>(std::stoul(_argv[++i]));
			else if (arg == "--samples" && i + 1 < _argc)
				maxSamples = static_cast<uint32_t>(std::stoul(_argv[++i]));
			else if (arg == "--watchdog" && i + 1 < _argc)
				watchdogSecs = std::stoi(_argv[++i]);
			else if (arg == "--first-slot" && i + 1 < _argc)
				firstSlot = static_cast<uint32_t>(std::stoul(_argv[++i]));
			else if (arg == "--no-cc")
				sweepControls = false;
			else if (arg == "--jit-control")
				jitControl = true;
			else if (arg == "--icache-model" && i + 1 < _argc)
			{
				// The first CACHEABLE program address. Base 0 parsing with a trailing-garbage
				// check, same contract as --pdump: a bare "1c00" would parse as decimal 1900 and
				// quietly move the boundary, which is the exact class of misparse this mode's
				// --pdump comment already records paying for. Write 0x1c00.
				const std::string spec = _argv[++i];
				size_t n = 0;
				const unsigned long v = std::stoul(spec, &n, 0);
				if (n != spec.size() || v == 0)
				{
					std::cout << "pc_coverage: --icache-model wants a nonzero first-cacheable "
						"program address (use 0x-prefixed hex, e.g. 0x1c00 for the TI2), got \""
						<< spec << "\"" << std::endl;
					return 1;
				}
				icacheBase = static_cast<dsp56k::TWord>(v);
			}
			else if (arg == "--preset" && i + 1 < _argc)
			{
				const std::string spec = _argv[++i];
				const auto colon = spec.find(':');
				if (colon == std::string::npos)
				{
					std::cout << "pc_coverage: --preset wants bank:program, got \"" << spec << "\"" << std::endl;
					return 1;
				}
				presets.emplace_back(std::stoi(spec.substr(0, colon)), std::stoi(spec.substr(colon + 1)));
			}
			else if (arg == "--param" && i + 1 < _argc)
			{
				// T12 2026-08-02. "--param page:index:value", repeatable. Page is the raw SysEx
				// page byte (112 = PARAM_CHANGE_A / $70, 113 = PARAM_CHANGE_B / $71, 110 = $6E);
				// std::stoi with base 0 so "0x70" and "112" both work and nobody has to guess
				// which convention a log line used.
				const std::string spec = _argv[++i];
				const auto c1 = spec.find(':');
				const auto c2 = c1 == std::string::npos ? std::string::npos : spec.find(':', c1 + 1);
				if (c1 == std::string::npos || c2 == std::string::npos)
				{
					std::cout << "pc_coverage: --param wants page:index:value, got \"" << spec << "\"" << std::endl;
					return 1;
				}
				const int page = std::stoi(spec.substr(0, c1), nullptr, 0);
				const int idx = std::stoi(spec.substr(c1 + 1, c2 - c1 - 1), nullptr, 0);
				const int val = std::stoi(spec.substr(c2 + 1), nullptr, 0);
				if (page < 0 || page > 255 || idx < 0 || idx > 127 || val < 0 || val > 127)
				{
					std::cout << "pc_coverage: --param out of range: page " << page << " idx " << idx
						<< " value " << val << " (index/value must be 0-127)" << std::endl;
					return 1;
				}
				liveParams.push_back({static_cast<uint8_t>(page), static_cast<uint8_t>(idx), static_cast<uint8_t>(val)});
			}
			else if (arg == "--pdump" && i + 1 < _argc)
			{
				// "--pdump lo:hi", repeatable, INCLUSIVE, hex accepted with 0x / $ / bare-hex is
				// NOT assumed -- std::stoul base 0, so write 0x124c (or 4684). A bare "124c" would
				// silently parse as decimal 124 up to the 'c', which is exactly the class of quiet
				// misparse this project keeps paying for, so a trailing-garbage check rejects it.
				const std::string spec = _argv[++i];
				const auto colon = spec.find(':');
				if (colon == std::string::npos)
				{
					std::cout << "pc_coverage: --pdump wants lo:hi, got \"" << spec << "\"" << std::endl;
					return 1;
				}
				const std::string loS = spec.substr(0, colon), hiS = spec.substr(colon + 1);
				size_t nLo = 0, nHi = 0;
				const unsigned long lo = std::stoul(loS, &nLo, 0);
				const unsigned long hi = std::stoul(hiS, &nHi, 0);
				if (nLo != loS.size() || nHi != hiS.size() || hi < lo)
				{
					std::cout << "pc_coverage: --pdump could not fully parse \"" << spec
						<< "\" as lo:hi with lo <= hi (use 0x-prefixed hex)" << std::endl;
					return 1;
				}
				pdumpRanges.emplace_back(static_cast<uint32_t>(lo), static_cast<uint32_t>(hi));
			}
			else if (arg == "--bank-sweep" && i + 1 < _argc)
			{
				// Every Nth program of every ROM bank -- the cheap way to widen the envelope a lot.
				const int stride = std::stoi(_argv[++i]);
				for (int b = 1; b < 26; ++b)
					for (int p = 0; p < 128; p += stride)
						presets.emplace_back(b, p);
			}
			else
				std::cout << "pc_coverage: ignoring unrecognized argument \"" << arg << "\"" << std::endl;
		}
		if (presets.empty())
			presets = { {11, 124} }; // "VocoPad XM", this project's standard known-good trigger
		return runPcCoverage(outPrefix, presets, slot, sweepControls, maxSamples, firstSlot, watchdogSecs,
			liveParams, jitControl, pdumpRanges, icacheBase);
	}

	// Enumeration-only mode: list every factory preset with Vocoder Mode != 0, plus a couple of
	// other vocoder-relevant byte values (Vocoder/Bands: page 112/PAGE_A idx 58 -> preset offset
	// 58; Filter Select: page 113/PAGE_B idx 122 -> preset offset 1*128+122=250), so we can pick
	// presets that differ in secondary vocoder params for the slot-table diffing experiment below.
	// Does not boot the DSP -- pure ROM/preset-table scan, exits immediately after listing.
	if (modeArg == "vocoder_scan")
	{
		auto rom = ROMLoader::findROM(DeviceModel::TI2);
		if (!rom.isValid())
		{
			std::cout << "ROM not found/invalid." << std::endl;
			return 1;
		}
		for (uint32_t b = 1; b < 26; ++b)
		{
			for (uint32_t p = 0; p < rom.getPresetsPerBank(); ++p)
			{
				Microcontroller::TPreset data;
				if (!rom.getSingle(static_cast<int>(b), static_cast<int>(p), data))
					continue;
				if (data.size() <= 250 || data[167] == 0)
					continue;
				std::cout << "bank " << b << " program " << p << " \"" << ROMFile::getSingleName(data)
					<< "\" VocoderMode=" << static_cast<int>(data[167])
					<< " Bands=" << static_cast<int>(data[58])
					<< " FilterSelect=" << static_cast<int>(data[250]) << std::endl;
			}
		}
		return 0;
	}

	// Re-check (this session) the earlier finding that no factory preset in the ROM ships with
	// Unison Mode != 0 (preset offset 504) -- if one exists, per the task brief it's a more
	// realistic test than a hand-forced live SysEx/bulk patch. Pure ROM/preset-table scan, same
	// shape as "vocoder_scan" above, doesn't boot the DSP.
	if (modeArg == "unison_scan")
	{
		auto rom = ROMLoader::findROM(DeviceModel::TI2);
		if (!rom.isValid())
		{
			std::cout << "ROM not found/invalid." << std::endl;
			return 1;
		}
		int found = 0;
		for (uint32_t b = 1; b < 26; ++b)
		{
			for (uint32_t p = 0; p < rom.getPresetsPerBank(); ++p)
			{
				Microcontroller::TPreset data;
				if (!rom.getSingle(static_cast<int>(b), static_cast<int>(p), data))
					continue;
				if (data.size() <= 504 || data[504] == 0)
					continue;
				++found;
				std::cout << "bank " << b << " program " << p << " \"" << ROMFile::getSingleName(data)
					<< "\" UnisonMode=" << static_cast<int>(data[504]) << std::endl;
			}
		}
		std::cout << "Total factory presets with Unison Mode != 0: " << found << std::endl;
		return 0;
	}

	if (modeArg == "vm_watch")
		return runVmWatch("xmem_vm_watch_dump.txt");

	if (modeArg == "drift_watch")
		return runDriftWatch(_argc > 2 ? _argv[2] : "xmem_drift_watch_dump.txt");

	if (modeArg == "pc_trace")
	{
		const uint32_t bank = _argc > 2 ? static_cast<uint32_t>(std::stoi(_argv[2], nullptr, 0)) : 11;
		const uint32_t prog = _argc > 3 ? static_cast<uint32_t>(std::stoi(_argv[3], nullptr, 0)) : 124;
		const int ovOff = _argc > 4 ? std::stoi(_argv[4], nullptr, 0) : -1;
		const int ovVal = _argc > 5 ? std::stoi(_argv[5], nullptr, 0) : 0;
		// Optional SECOND override pair (2026-08-03): pc_trace <bank> <prog> <off1> <val1> [off2] [val2].
		const int ov2Off = _argc > 6 ? std::stoi(_argv[6], nullptr, 0) : -1;
		const int ov2Val = _argc > 7 ? std::stoi(_argv[7], nullptr, 0) : 0;
		std::string suffix = (_argc > 2) ? "_b" + std::to_string(bank) + "p" + std::to_string(prog) : "";
		if (ovOff >= 0) suffix += "_o" + std::to_string(ovOff) + "v" + std::to_string(ovVal);
		// The second override MUST appear in the filename. Two runs that differ only in a
		// parameter absent from the name overwrite each other, and the surviving file then
		// carries the earlier run's answer under the later run's label.
		if (ov2Off >= 0) suffix += "_o" + std::to_string(ov2Off) + "v" + std::to_string(ov2Val);
		return runPcTrace("xmem_pc_trace_dump" + suffix + ".txt", bank, prog, ovOff, ovVal, ov2Off, ov2Val);
	}

	// Raw preset bytes, added 2026-08-03 to diff the presets that REACH func_051004 against those
	// that do not (claim-ledger row 91). Uses the ROM loader rather than re-deriving the bank
	// layout by hand. Byte offset -> parameter: offset = page*128 + index, where page 0 is SysEx
	// page 112 (0x70) and page 1 is page 113 (0x71) -- the same mapping "sweep" mode uses.
	if (modeArg == "presetdump" && _argc >= 4)
	{
		auto rom = ROMLoader::findROM(DeviceModel::TI2);
		if (!rom.isValid()) { std::cout << "ROM not found/invalid." << std::endl; return 1; }
		const auto b = static_cast<uint32_t>(std::stoi(_argv[2], nullptr, 0));
		const auto pr = static_cast<uint32_t>(std::stoi(_argv[3], nullptr, 0));
		Microcontroller::TPreset preset{};
		if (!rom.getSingle(b, pr, preset)) { std::cout << "no such preset" << std::endl; return 1; }
		std::cout << "PRESET " << b << " " << pr << " " << ROMFile::getSingleName(preset) << "\n";
		std::cout << "BYTES";
		for (size_t i = 0; i < preset.size(); ++i)
			std::cout << " " << static_cast<int>(preset[i]);
		std::cout << std::endl;
		return 0;
	}

	// Preset-name listing, so a coverage scenario is CHOSEN on evidence rather than guessed at.
	if (modeArg == "presetnames")
	{
		auto rom = ROMLoader::findROM(DeviceModel::TI2);
		if (!rom.isValid()) { std::cout << "ROM not found/invalid." << std::endl; return 1; }
		const uint32_t firstBank = _argc > 2 ? static_cast<uint32_t>(std::stoi(_argv[2], nullptr, 0)) : 0;
		const uint32_t lastBank  = _argc > 3 ? static_cast<uint32_t>(std::stoi(_argv[3], nullptr, 0)) : 25;
		for (uint32_t b = firstBank; b <= lastBank; ++b)
		{
			for (uint32_t p = 0; p < 128; ++p)
			{
				Microcontroller::TPreset pr{};
				if (!rom.getSingle(b, p, pr)) continue;
				const auto n = ROMFile::getSingleName(pr);
				if (n.empty()) continue;
				std::cout << b << " " << p << " " << n << "\n";
			}
		}
		return 0;
	}

	if (modeArg == "bootdump")
		return runBootDump("xmem_bootdump.txt");

	if (modeArg == "chorus_pc_trace" && _argc >= 3)
	{
		const int chorusType = std::stoi(_argv[2], nullptr, 0);
		const bool sendNotes = !(_argc >= 4 && std::string(_argv[3]) == "nonote");
		const std::string suffix = sendNotes ? "" : "_nonote";
		return runChorusPcTrace(chorusType, "xmem_chorus_pc_trace_type" + std::to_string(chorusType) + suffix + "_dump.txt", sendNotes);
	}

	// "chorus_buildarea <type>" -- chorus_pc_trace plus live PARAM_CHANGE Chorus Type and full
	// DSP2 X+Y dumps (see work/dsp_chorus_live_program_matrix_findings.md for the method this
	// evolved through).
	if (modeArg == "chorus_buildarea" && _argc >= 3)
	{
		const int chorusType = std::stoi(_argv[2], nullptr, 0);
		return runChorusPcTrace(chorusType, "xmem_chorus_buildarea_type" + std::to_string(chorusType) + "_dump.txt",
			true, -1, -1, -1, -1, true,
			{{0x70, 103, static_cast<uint8_t>(chorusType)}});
	}

	// "fx_live <page> <idx> <val> [<page2> <idx2> <val2>]" -- generic live-PARAM_CHANGE JIT-trace
	// probe: same base preset/notes as chorus_pc_trace, sends the given parameter(s) live at cb
	// 1200 (the path that actually triggers effect rebuilds, unlike the bulk preset write), and
	// reports JIT block sets (no full memory dumps -- diff block sets across runs to find
	// per-value launcher stubs/marshallers via tools/vm_catalog.py's catalog).
	if (modeArg == "fx_live" && _argc >= 5)
	{
		std::vector<std::array<uint8_t, 3>> lp;
		std::string tag;
		bool fullDump = false;
		for (int i = 2; i < _argc; ++i)
		{
			if (std::string(_argv[i]) == "fulldump") { fullDump = true; continue; }
			if (i + 2 >= _argc) break;
			const auto pg = static_cast<uint8_t>(std::stoi(_argv[i], nullptr, 0));
			const auto ix = static_cast<uint8_t>(std::stoi(_argv[i+1], nullptr, 0));
			const auto vl = static_cast<uint8_t>(std::stoi(_argv[i+2], nullptr, 0));
			lp.push_back({pg, ix, vl});
			tag += "_p" + std::to_string(pg) + "i" + std::to_string(ix) + "v" + std::to_string(vl);
			i += 2;
		}
		if (fullDump)
			tag += "_full";
		return runChorusPcTrace(1, "xmem_fx_live" + tag + "_dump.txt",
			true, -1, -1, -1, -1, fullDump, lp);
	}

	// "filterbank_pc_trace <type>" -- doc/dsp56300_synth_engine.md's own flagged disambiguation
	// target: is func_051004/func_050f7e (confirmed real per-voice filter/delay-line DSP code)
	// Filter Bank's "Comb Filter" mode, or the standard always-active per-voice filter? Reuses
	// chorus_pc_trace's machinery with Filter Bank Type/Mix overridden instead of Chorus Type,
	// Chorus left at Type=1 (Classic) throughout so it's a constant, not a confound.
	if (modeArg == "filterbank_pc_trace" && _argc >= 3)
	{
		const int fbType = std::stoi(_argv[2], nullptr, 0);
		return runChorusPcTrace(1, "xmem_filterbank_pc_trace_type" + std::to_string(fbType) + "_dump.txt", true, fbType);
	}

	// "distortion_pc_trace <type>" / "character_pc_trace <type>" -- addendum-diffing follow-up
	// (plan.md's "byte-level reading of the OS 4.0 boundary" item): same reuse pattern as
	// filterbank_pc_trace, testing whether OS 4.0's 6 new Distortion Curve types (Mint Overdrive=20
	// .. Chili Overdrive=25) or OS 3.3's 8 (Wide=12 .. Bit Reducer=19), and OS 4.0's Speaker Cabinet
	// Character Type (=8), get dedicated new P-memory code vs. reusing the pre-existing generic
	// engine the way Chorus/Filter Bank types were already shown to (work/dsp_chorus_type_pc_trace_
	// findings.md, work/dsp_filterbank_combfilter_pc_trace_findings.md).
	if (modeArg == "distortion_pc_trace" && _argc >= 3)
	{
		const int distType = std::stoi(_argv[2], nullptr, 0);
		return runChorusPcTrace(1, "xmem_distortion_pc_trace_type" + std::to_string(distType) + "_dump.txt", true, -1, distType);
	}

	if (modeArg == "character_pc_trace" && _argc >= 3)
	{
		const int charType = std::stoi(_argv[2], nullptr, 0);
		return runChorusPcTrace(1, "xmem_character_pc_trace_type" + std::to_string(charType) + "_dump.txt", true, -1, -1, charType);
	}

	// "modsource_pc_trace <sourceIdx>" -- addendum-diffing follow-up, OS 4.5's 9 new Mod Matrix
	// sources (see plan.md's addendum-diffing item, the still-open half of the OS 4.5 new-code zone
	// hypothesis after Hyper/Air Chorus was falsified). A-priori expectation from insights.md's
	// func_0001a8 finding (55+ callers, "blend two table entries by fractional weight", the shared
	// primitive nearly every modulation route already goes through): these are very likely new
	// SOURCE TABLE ENTRIES read by the existing per-tick Mod Matrix summing code, not new dedicated
	// code, unlike Distortion's confirmed-different-code-per-type result above.
	if (modeArg == "rotary_render" && _argc >= 3)
	{
		return runRotaryRender(_argv[2]);
	}

	if (modeArg == "modsource_pc_trace" && _argc >= 3)
	{
		const int srcIdx = std::stoi(_argv[2], nullptr, 0);
		return runChorusPcTrace(1, "xmem_modsource_pc_trace_src" + std::to_string(srcIdx) + "_dump.txt", true, -1, -1, -1, srcIdx);
	}

	// "arpmode_pc_trace <mode>" -- Site 1 part-2 probe item 1 (work/dsp_site1_live_trigger_
	// part2_findings.md): Arp Mode baked into the bulk preset write (before either Note On), same
	// pattern as modsource_pc_trace above, with the full Site1 stub-cluster/consumer-chain +
	// Y:$16/$23/$40-$4F fulldump probe enabled. mode=5 is "Random" in the arpModes enum.
	if (modeArg == "arpmode_pc_trace" && _argc >= 3)
	{
		const int arpMode = std::stoi(_argv[2], nullptr, 0);
		return runChorusPcTrace(1, "xmem_arpmode_pc_trace_mode" + std::to_string(arpMode) + "_dump.txt",
			true, -1, -1, -1, -1, true, {}, arpMode);
	}

	if (modeArg == "hardsync_pc_trace" && _argc >= 3)
	{
		const int hsMode = std::stoi(_argv[2], nullptr, 0);
		return runHardSyncPcTrace(hsMode, "xmem_hardsync_pc_trace_mode" + std::to_string(hsMode) + "_dump.txt");
	}

	// "site1_cold_build_pc_trace <candidate>" -- see runSite1ColdBuildProbe's own comment above for
	// full rationale. Part 3 of this investigation (work/dsp_site1_live_trigger_part3_findings.md)
	// extends part 2's cold-Program-Change-plus-chord-burst trigger condition (previously only ever
	// armed with one candidate, Arp Mode=Random) to the loose-end candidates part 2's section 6
	// flagged as untested under this specific trigger condition, following the project's established
	// "one candidate vs. a matched control per run" discipline rather than a combinatorial
	// cross-product:
	//   control     -- matched control, nothing armed (byte-for-byte part 2's old arm=0 run)
	//   arpmode     -- Arp Mode=Random (page113/idx15=5) -- re-run of part 2's arm=1, kept for parity
	//   lfo2sh      -- LFO2 Shape=S&H (page112/idx80=4) + Cutoff1<-LFO2 Amount=100 (page112/idx88),
	//                  a real nonzero depth away from the 64=center default
	//   lfo3sh      -- LFO3 Shape=S&H (page113/idx8=4) + Osc<-LFO3 Amount=100 (page113/idx12), a real
	//                  nonzero depth (LFO3's unipolar amount knob defaults to 0=off, unlike LFO1/2)
	//   unisonphase -- Unison Mode=1 (page111/idx120) + Unison LFO Phase=127 (page111/idx123)
	//   arppattern  -- task item 2: Arp Mode=Up=1 (page113/idx15, non-Off so pattern selection is
	//                  meaningful) + Arp Pattern Selct=42 (page113/idx2, away from its own default=1)
	if (modeArg == "site1_cold_build_pc_trace" && _argc >= 3)
	{
		const std::string candidate = _argv[2];
		std::vector<std::array<uint8_t, 3>> armParams;
		std::string label = "none (control)";
		if (candidate == "control")
		{
			// armParams stays empty, label stays "none (control)"
		}
		else if (candidate == "arpmode")
		{
			armParams = {{113, 15, 5}};
			label = "Arp Mode=Random";
		}
		else if (candidate == "lfo2sh")
		{
			armParams = {{112, 80, 4}, {112, 88, 100}};
			label = "LFO2 Shape=S&H, Cutoff1<-LFO2 Amount=100";
		}
		else if (candidate == "lfo3sh")
		{
			armParams = {{113, 8, 4}, {113, 12, 100}};
			label = "LFO3 Shape=S&H, Osc<-LFO3 Amount=100";
		}
		else if (candidate == "unisonphase")
		{
			armParams = {{111, 120, 1}, {111, 123, 127}};
			label = "Unison Mode=1, Unison LFO Phase=127";
		}
		else if (candidate == "arppattern")
		{
			armParams = {{113, 15, 1}, {113, 2, 42}};
			label = "Arp Mode=Up, Arp Pattern Selct=42";
		}
		// Matched control for "arppattern" specifically added after that run showed dsp1_y:$23 =
		// $10000, differing from every other cold-build candidate's $2000 -- Arp Mode=Up genuinely
		// changes downstream behavior on its own (the 4-note "chord burst" gets arpeggiated instead
		// of sounding as a simultaneous chord for the rest of the ~8s render), which is a confound
		// independent of which pattern slot is selected. This isolates that: same Arp Mode=Up, but
		// Arp Pattern Selct left at its own default (1, "2" in the User1-64 1-based display) instead
		// of overridden to 42 -- if Y:$23/block-list match "arppattern" here, the slot VALUE made no
		// difference (only "Arp Mode=Up being on at all" did); if they differ, that's a real slot-
		// content-dependent signal worth chasing further.
		else if (candidate == "arpmode_up_only")
		{
			armParams = {{113, 15, 1}};
			label = "Arp Mode=Up, Arp Pattern Selct left at default (matched control for arppattern)";
		}
		else
		{
			std::cout << "Unknown site1_cold_build_pc_trace candidate \"" << candidate << "\". Valid: "
				"control, arpmode, lfo2sh, lfo3sh, unisonphase, arppattern, arpmode_up_only." << std::endl;
			return 1;
		}
		return runSite1ColdBuildProbe(armParams, label, candidate,
			"xmem_site1_cold_build_pc_trace_" + candidate + "_dump.txt");
	}

	// "site1_multimode_pc_trace <candidate>" -- see runSite1MultiModeProbe's own comment above for
	// full rationale. First-ever Multi-mode test of Site 1 (or of any candidate in this investigation):
	//   control    -- matched control, no live PARAM_CHANGE sent to part 1
	//   modmatrix  -- Mod Matrix Assign1: Random(27) -> Filter1 Cutoff, Amount=127 (page113/idx64-66),
	//                 sent to part=1 specifically (not SINGLE) -- the strongest-motivated candidate
	//                 from parts 1-3 of this investigation, re-tried under the one axis (a specific
	//                 Multi part as the SysEx target) never tried before
	//   unisonphase -- Unison Mode=1 (page111/idx120) + Unison LFO Phase=127 (page111/idx123), part=1
	//   arpmode    -- Arp Mode=Random (page113/idx15=5), part=1
	if (modeArg == "site1_multimode_pc_trace" && _argc >= 3)
	{
		const std::string candidate = _argv[2];
		std::vector<std::array<uint8_t, 3>> liveParams;
		std::string label = "none (control)";
		if (candidate == "control")
		{
			// liveParams stays empty, label stays "none (control)"
		}
		else if (candidate == "modmatrix")
		{
			liveParams = {{113, 64, 27}, {113, 65, 24}, {113, 66, 127}};
			label = "Mod Matrix Assign1: Random(27) -> Filter1 Cutoff, Amount=127";
		}
		else if (candidate == "unisonphase")
		{
			liveParams = {{111, 120, 1}, {111, 123, 127}};
			label = "Unison Mode=1, Unison LFO Phase=127";
		}
		else if (candidate == "arpmode")
		{
			liveParams = {{113, 15, 5}};
			label = "Arp Mode=Random";
		}
		else if (candidate == "lfo1sh")
		{
			liveParams = {{112, 68, 4}, {112, 74, 100}};
			label = "LFO1 Shape=S&H, Osc1<-LFO1 Amount=100";
		}
		else if (candidate == "lfo2sh")
		{
			liveParams = {{112, 80, 4}, {112, 88, 100}};
			label = "LFO2 Shape=S&H, Cutoff1<-LFO2 Amount=100";
		}
		else if (candidate == "lfo3sh")
		{
			liveParams = {{113, 8, 4}, {113, 11, 1}, {113, 12, 100}};
			label = "LFO3 Shape=S&H, Dest=Osc 1+2 Pitch, Amount=100";
		}
		else if (candidate == "arppattern")
		{
			liveParams = {{113, 15, 1}, {113, 2, 42}};
			label = "Arp Mode=Up, Arp Pattern Selct=42";
		}
		else if (candidate == "arpmode_up_only")
		{
			liveParams = {{113, 15, 1}};
			label = "Arp Mode=Up only";
		}
		else if (candidate == "sysexplaymode")
		{
			// 2026-07-21 shm-exhaustion re-test: control run, but with the REAL PLAY_MODE=Multi
			// SysEx sent at cb2100 (the 2026-07-20 "bug #1" deterministic crash path) instead of
			// the writeMulti() workaround. No live params.
			label = "none (control) + real PLAY_MODE=Multi SysEx at cb2100";
		}
		else if (candidate == "part0sysex")
		{
			// 2026-07-21: the maximal originally-crashing config -- active parts {0,1} (re-testing
			// the since-downgraded "note-on to part 0 crashes" characterization) AND the real
			// PLAY_MODE=Multi SysEx. No live params.
			label = "none (control) + parts {0,1} + real PLAY_MODE=Multi SysEx";
		}
		else
		{
			std::cout << "Unknown site1_multimode_pc_trace candidate \"" << candidate << "\". Valid: "
				"control, modmatrix, unisonphase, arpmode, lfo1sh, lfo2sh, lfo3sh, arppattern, arpmode_up_only, sysexplaymode, part0sysex." << std::endl;
			return 1;
		}
		return runSite1MultiModeProbe(liveParams, label, candidate,
			"xmem_site1_multimode_pc_trace_" + candidate + "_dump.txt",
			candidate == "sysexplaymode" || candidate == "part0sysex",
			candidate == "part0sysex" ? 0 : 1,
			candidate == "part0sysex" ? 1 : 2);
	}

	if (modeArg == "oscwave_probe" && _argc >= 3)
	{
		const int waveSelect = std::stoi(_argv[2], nullptr, 0);
		return runOscWaveProbe(waveSelect, "xmem_oscwave_probe_" + std::to_string(waveSelect) + "_dump.txt");
	}

	if (modeArg == "ji_pitch_probe" && _argc >= 4)
	{
		const int note = std::stoi(_argv[2], nullptr, 0);
		const int pureTuning = std::stoi(_argv[3], nullptr, 0);
		const std::string outWav = _argc >= 5 ? _argv[4]
			: ("xmem_ji_pitch_note" + std::to_string(note) + "_pt" + std::to_string(pureTuning) + ".wav");
		return runJiPitchProbe(note, pureTuning, outWav);
	}

	if (modeArg == "hdr4_pitch_probe" && _argc >= 5)
	{
		const int note = std::stoi(_argv[2], nullptr, 0);
		const int bendMsb = std::stoi(_argv[3], nullptr, 0);
		const int bendLsb = std::stoi(_argv[4], nullptr, 0);
		const std::string outFile = _argc >= 6 ? _argv[5]
			: ("xmem_hdr4_pitch_probe_n" + std::to_string(note) + "_b" + std::to_string(bendMsb) + "_" + std::to_string(bendLsb) + "_dump.txt");
		return runHdr4PitchBendProbe(note, bendMsb, bendLsb, outFile);
	}

	if (modeArg == "portamento_probe" && _argc >= 5)
	{
		const int portaVal = std::stoi(_argv[2], nullptr, 0);
		const int noteA = std::stoi(_argv[3], nullptr, 0);
		const int noteB = std::stoi(_argv[4], nullptr, 0);
		const std::string outFile = _argc >= 6 ? _argv[5]
			: ("xmem_portamento_probe_pt" + std::to_string(portaVal) + "_a" + std::to_string(noteA) + "_b" + std::to_string(noteB) + "_dump.txt");
		return runPortamentoProbe(portaVal, noteA, noteB, outFile);
	}

	// "rotor_timing <speedVal> <mix2Val> [outFile]" -- see runRotorTimingProbe's own comment above
	// for full rationale (work/dsp_rotary_rotor_hz_live_measurement_findings.md).
	if (modeArg == "rotor_timing" && _argc >= 4)
	{
		const int speedVal = std::stoi(_argv[2], nullptr, 0);
		const int mix2Val = std::stoi(_argv[3], nullptr, 0);
		const std::string outFile = _argc >= 5 ? _argv[4]
			: ("xmem_rotor_timing_speed" + std::to_string(speedVal) + "_mix" + std::to_string(mix2Val) + "_dump.txt");
		return runRotorTimingProbe(speedVal, mix2Val, outFile);
	}

	Experiment sweepExp;
	const Experiment* exp = nullptr;
	if ((modeArg == "sweep" || modeArg == "sweep_live") && _argc >= 5)
	{
		// sweep_live: identical to sweep but drives the parameter via a live PARAM_CHANGE SysEx
		// (after Note On) instead of baking it into the bulk preset write. Used to validate that
		// the continuous-parameter memory mappings found via the bulk-write "sweep" are the same
		// under the live path -- the bulk write is inert for effect-rebuild-triggering type
		// selectors (see work/dsp_chorus_live_program_matrix_findings.md) but should be fine for
		// per-voice continuous params read fresh at note-on. Cross-check, not a new mapping tool.
		const bool live = (modeArg == "sweep_live");
		sweepExp.name = "sweep";
		sweepExp.paramLabel = "Sweep Parameter";

		int page = std::stoi(_argv[2], nullptr, 0);
		int param = std::stoi(_argv[3], nullptr, 0);

		int pageOffset = 0;
		if (page == 0x70) pageOffset = 0; // PAGE_A
		else if (page == 0x71) pageOffset = 1; // PAGE_B
		else if (page == 0x6E) pageOffset = 2;
		else if (page == 0x6F) pageOffset = 3;

		sweepExp.paramOffset = pageOffset * 128 + param;
		sweepExp.wantNonZero = true; // force it to patch
		sweepExp.patchValue = std::stoi(_argv[4], nullptr, 0);
		sweepExp.useLiveParamChange = live;
		if (live)
		{
			sweepExp.livePage = static_cast<uint8_t>(page);
			sweepExp.liveParam = static_cast<uint8_t>(param);
			sweepExp.liveValue = sweepExp.patchValue;
			sweepExp.liveParamCallback = 700; // after Note On (cb 512)
		}

        // Preset selectable 2026-08-03. It was hardcoded to 11/124, whose Delay Send and
        // Reverb Send are BOTH 0 -- so sweeping any delay or reverb parameter on it hits the
        // engagement gap and reports "no cell moved", which is what the all-zero type->program
        // matrices were. To map an effect's fields you must sweep on a preset where that
        // effect is actually running.
        sweepExp.forcedBank    = _argc > 5 ? static_cast<uint32_t>(std::stoi(_argv[5], nullptr, 0)) : 11;
        sweepExp.forcedProgram = _argc > 6 ? static_cast<uint32_t>(std::stoi(_argv[6], nullptr, 0)) : 124;

		exp = &sweepExp;
	}
	else
	{
		for (const auto& e : kExperiments)
		{
			if (e.name == modeArg)
			{
				exp = &e;
				break;
			}
		}
	}

	if (!exp)
	{
		std::cout << "Unknown mode \"" << modeArg << "\". Known modes: sweep vocoder_scan unison_scan vm_watch";
		for (const auto& e : kExperiments)
			std::cout << " " << e.name;
		std::cout << "\nUsage for sweep: sweep <page> <param> <value>" << std::endl;
		return 1;
	}
	const std::string outFile = "xmem_" + exp->name + "_dump.txt";

	auto rom = ROMLoader::findROM(DeviceModel::TI2);
	if (!rom.isValid())
	{
		std::cout << "ROM not found/invalid. Place a valid TI2 firmware .bin next to this executable." << std::endl;
		return 1;
	}
	std::cout << "Using ROM " << rom.getFilename() << " -- experiment \"" << exp->name << "\" ("
		<< exp->paramLabel << (exp->wantNonZero ? " != 0" : " == 0") << ")" << std::endl;

	// Find a factory single preset matching this experiment's parameter condition.
	int foundBank = -1, foundProgram = -1;
	Microcontroller::TPreset preset{};
	if (exp->forcedBank >= 0)
	{
		Microcontroller::TPreset data;
		if (rom.getSingle(exp->forcedBank, exp->forcedProgram, data) && data.size() > exp->paramOffset)
		{
			foundBank = exp->forcedBank;
			foundProgram = exp->forcedProgram;
			preset = data;
			std::cout << "Forced preset: bank " << foundBank << " program " << foundProgram
				<< " (\"" << ROMFile::getSingleName(preset) << "\"), " << exp->paramLabel << " byte = "
				<< static_cast<int>(preset[exp->paramOffset]) << std::endl;
		}
		else
		{
			std::cout << "Forced bank/program " << exp->forcedBank << "/" << exp->forcedProgram
				<< " invalid, falling back to search." << std::endl;
		}
	}
	// Skip bank 0 -- program 0 there turned out to be a blank/init template preset
	// (garbled name) whose degenerate parameter values crash the emulator's DSP core.
	// Not otherwise relevant to this experiment, so just avoid it.
	for (uint32_t b = 1; b < 26 && foundBank < 0; ++b)
	{
		for (uint32_t p = 0; p < rom.getPresetsPerBank(); ++p)
		{
			Microcontroller::TPreset data;
			if (!rom.getSingle(static_cast<int>(b), static_cast<int>(p), data))
				continue;
			if (data.size() <= exp->paramOffset)
				continue;
			const bool wantMatch = exp->wantNonZero ? (data[exp->paramOffset] != 0) : (data[exp->paramOffset] == 0);
			if (wantMatch)
			{
				foundBank = static_cast<int>(b);
				foundProgram = static_cast<int>(p);
				preset = data;
				std::cout << "Found preset: bank " << foundBank << " program " << foundProgram
					<< " (\"" << ROMFile::getSingleName(preset) << "\"), " << exp->paramLabel << " byte = "
					<< static_cast<int>(preset[exp->paramOffset]) << std::endl;
				break;
			}
		}
	}

	if (foundBank < 0)
	{
		std::cout << "No matching factory preset found. Falling back to preset 1/0, patching " << exp->paramLabel << "." << std::endl;
		rom.getSingle(1, 0, preset);
		std::cout << "Using preset \"" << ROMFile::getSingleName(preset) << "\"" << std::endl;
	}
    
        
    if (exp->name == "sweep" && preset.size() >= 305) {
        // Reverb defaults
        preset[257] = 1; // Reverb Mode = 1 (on)
        preset[258] = 64; // Reverb Send
        preset[259] = 0; // Reverb Type
        preset[260] = 64; // Reverb Time
        preset[261] = 10; // Reverb Damping
        preset[262] = 64; // Reverb Color
        preset[265] = 10; // Reverb Predelay
        
        // Chorus defaults (page 112/0x70 = PAGE_A, offset == index directly --
        // fixes a bug where this block wrote preset[300-304], which actually
        // decodes to PAGE_6E(0x6E) idx 44-48 (Oscillator 1 Interpolation plus
        // four literally-Undefined bytes per parameterDescriptions_TI.json),
        // never touching the real Chorus params at page 112 idx 103-109 at all)
        preset[103] = 1;  // Chorus/Type (1 = Classic)
        preset[105] = 64; // Chorus Mix
        preset[106] = 43; // Chorus Rate
        preset[107] = 64; // Chorus Depth
        preset[108] = 32; // Chorus Delay
        
        // Distortion defaults
        preset[228] = 1; // Distortion Curve (page 113 idx 100 = 1*128+100 = 228) - Type 1 (Light)
        preset[229] = 64; // Distortion Intensity (page 113 idx 101 = 229)
        preset[328] = 127; // Distortion Mix (page 110 idx 72 = 2*128+72 = 328)

        // Delay defaults
        preset[112] = 1; // Delay Mode (page 112 idx 112 = 0*128+112 = 112)
        preset[113] = 64; // Delay Send (page 112 idx 113)
        preset[114] = 64; // Delay Time (page 112 idx 114)
        preset[116] = 64; // Delay Feedback (page 112 idx 116)
        
        // Phaser defaults
        preset[212] = 3; // Phaser Mode (page 113 idx 84 = 1*128+84 = 212)
        preset[213] = 64; // Phaser Mix (page 113 idx 85 = 213)
        preset[214] = 36; // Phaser Rate (page 113 idx 86 = 214)
        preset[215] = 112; // Phaser Depth (page 113 idx 87 = 215)
        preset[216] = 64; // Phaser Frequency (page 113 idx 88 = 216)

        // Arp defaults (page 113 idx 15 = 1*128+15 = 143) -- 2026-07-23 retest: force Arp
        // actually running (Mode=1 "Up") so arp-runtime-gated sub-params (Hold Enable, Note
        // Length, Clock) are testable, matching the pattern already used above for Reverb/
        // Chorus/Distortion/Delay/Phaser. Previously left at the factory preset's own value
        // (VocoPad XM's baked Arp Mode, never verified) -- see
        // work/dsp_arp_mode_confound_retest_2026-07-23.md.
        preset[143] = 1; // Arp Mode = 1 (Up)

        // Filter Bank defaults (page 110 idx 19 = 2*128+19 = 275) -- 2026-07-23: force it engaged
        // (Type=1 "Ring Modulator", matching the JSON's own declared default) so the continuous
        // sub-params (Mix/Frequency/Stereo Phase/etc.) are testable, mirroring the Arp-Mode
        // precedent above -- an earlier Mix sweep this session came back confounded/inconclusive
        // because Filter Bank was left Off in the harness's ambient preset state. See
        // work/dsp_parameter_json_coverage_scan_2026-07-23.md.
        preset[275] = 1; // Filter Bank Type = 1 (Ring Modulator)

        // Delay Type default (page 110 idx 10 = 2*128+10 = 266) -- 2026-07-23: force it to a
        // Tape variant (1 = "Tape Clocked") so the Tape-Delay-specific continuous sub-params
        // (Ratio/Clock Left/Clock Right/Bandwidth, page 110 idx 12/13/14/17) are testable at all,
        // mirroring the Filter-Bank-Type/Arp-Mode precedent above -- confirmed via
        // work/dsp_057323_delaytype_table_resolved_findings.md that Delay Type is itself a
        // VM-built type-selector (P:057323, 4 entries: Classic/Tape Clocked/Tape Free/Tape
        // Doppler), same "needs forcing, invisible at Classic/default" shape as Filter Bank/
        // Chorus/Character/Distortion. See work/dsp_parameter_json_coverage_scan_2026-07-23.md.
        preset[266] = 1; // Delay Type = 1 (Tape Clocked)
    }

    // In live mode, leave the preset's factory value untouched so the ONLY thing that varies
    // across sweep_live invocations is the live PARAM_CHANGE -- otherwise the bulk write would
    // confound the cross-check by also applying the swept value.
    if (preset.size() > exp->paramOffset && !exp->useLiveParamChange)
        preset[exp->paramOffset] = exp->wantNonZero ? exp->patchValue : 0;


	DspSingle* dsp1raw = nullptr;
	DspSingle* dsp2raw = nullptr;
	virusLib::Device::createDspInstances(dsp1raw, dsp2raw, rom, static_cast<float>(rom.getSamplerate()));
	std::unique_ptr<DspSingle> dsp1(dsp1raw);

	Microcontroller uc(*dsp1, rom, false);
	if (dsp2raw)
		uc.addDSP(*dsp2raw, false);

	dsp56k::SpscSemaphore sem(1);
	uint32_t callbackCount = 0;
	int32_t notifyTimeout = 0;
	constexpr uint32_t blockSize = 64;
	const uint32_t notifyThreshold = blockSize > 4 ? blockSize - 4 : 0;
	std::vector<SMidiEvent> midiEvents; // touched only from the audio-callback thread below

	bool presetSent = false;
	bool noteSent = false;
	bool liveParamSent = false;
	bool secondNoteSent = false;
	bool chorusMixSent = false;

	// ---- MID-RENDER BASE SAMPLING (added 2026-08-03) ------------------------------------
	// Three separate probes across two days read a confident constant out of an r1/r4-relative
	// cell and were wrong, because "sweep"/"sweep_live" dump memory AFTER the render finishes.
	// By then x:$1 (r1 base), y:$1 (r4 base) and x:$B52 (voice node) point at a released or
	// different object: y:$1 read $49BB9 in one run and $49B9E in another, and a delay-field
	// probe at y:(r4+$66) returned an identical value for every parameter and every value
	// because r4 held the REVERB's base at dump time.
	//
	// This is exactly the fix runPcTrace already carries ("SAMPLE THE LANDING CHECK WHILE A
	// VOICE IS SOUNDING", cb 800): read the bases INTO LOCALS from inside the audio callback,
	// while the render is still running and the voice is still sounding, and print them.
	//
	// The second half of the same problem is coverage: even a correct base is useless if the
	// dump's windows don't reach it. So each snapshot also copies a window around each of the
	// three bases at that same instant, so every r1/r4-relative field is physically present in
	// the dump rather than sitting outside every window (the failure that cost 36 sweep runs,
	// work/page112_sweep_coverage_gap_2026-08-02.md).
	//
	// TWO snapshots, deliberately. cb 800 is 100 callbacks after sweep_live's cb-700
	// PARAM_CHANGE -- early enough that a slow-propagating parameter may not have landed yet,
	// so an "unchanged" reading there would be an inconclusive test, not a negative one (see
	// AGENTS.md Verification Discipline #4). midLast re-samples periodically and keeps the last
	// one, which is both settled and still mid-render. Comparing the two, and comparing either
	// against the end-of-render bases, is what actually tests the stale-base diagnosis.
	struct BaseSnapshot
	{
		bool valid = false;
		uint32_t cb = 0;
		dsp56k::TWord x1 = 0, y1 = 0, voice = 0;
		// 6 windows of kBaseWinCount words each, in order:
		// X@x1, Y@x1, X@y1, Y@y1, X@voice, Y@voice
		std::vector<dsp56k::TWord> win;
	};
	constexpr dsp56k::TWord kBaseWinBack  = 0x10;  // words dumped BEFORE the base
	constexpr uint32_t      kBaseWinCount = 0x90;  // total words per window (base sits at +$10)
	BaseSnapshot midFirst, midLast;
	auto takeBaseSnapshot = [&](BaseSnapshot& _s, uint32_t _cb)
	{
		const auto& m = dsp1->getMemory();
		_s.cb    = _cb;
		_s.x1    = m.get(dsp56k::MemArea_X, 0x1);
		_s.y1    = m.get(dsp56k::MemArea_Y, 0x1);
		_s.voice = m.get(dsp56k::MemArea_X, 0xB52);
		_s.win.clear();
		_s.win.reserve(6 * kBaseWinCount);
		const dsp56k::TWord bases[3] = { _s.x1, _s.y1, _s.voice };
		for (const auto b : bases)
		{
			// Both areas at every base on purpose. r1 and r4 are separate objects here and
			// assuming a shared base is precisely the error this whole block exists to undo.
			const dsp56k::TWord start = b >= kBaseWinBack ? b - kBaseWinBack : 0;
			for (uint32_t a = 0; a < kBaseWinCount; ++a)
				_s.win.push_back(m.get(dsp56k::MemArea_X, start + a));
			for (uint32_t a = 0; a < kBaseWinCount; ++a)
				_s.win.push_back(m.get(dsp56k::MemArea_Y, start + a));
		}
		_s.valid = true;
	};

	auto& esai = dsp1->getAudio();
	esai.setCallback([&](dsp56k::Audio*)
	{
		const auto availableSize = esai.getAudioOutputs().size();
		const auto sizeReached = availableSize >= notifyThreshold;
		--notifyTimeout;
		if (notifyTimeout <= 0 && sizeReached)
		{
			notifyTimeout = static_cast<int>(notifyThreshold);
			sem.notify();
		}

		++callbackCount;
		if ((callbackCount & 0x3) != 0)
			return;

		uc.readMidiOut(midiEvents);
		const auto audioCallbackCount = callbackCount >> 2;
		uc.process();

		if (audioCallbackCount == 1)
		{
			dsp1->drainESSI1();
			uc.sendInitControlCommands(127);
		}
		else if (audioCallbackCount == 256 && !presetSent)
		{
			dsp1->drainESSI1();
			dsp1->disableESSI1();
			std::cout << "[cb " << audioCallbackCount << "] Sending preset" << std::endl;
			uc.writeSingle(BankNumber::EditBuffer, virusLib::SINGLE, preset);
			presetSent = true;
		}
		else if (audioCallbackCount == 512 && !noteSent)
		{
			std::cout << "[cb " << audioCallbackCount << "] Sending Note On" << std::endl;
			uc.sendMIDI(SMidiEvent(MidiEventSource::Host, 0x90, 60, 0x5f));
			uc.sendPendingMidiEvents(std::numeric_limits<uint32_t>::max());
			noteSent = true;
		}
		else if (audioCallbackCount == exp->secondNoteCallback && exp->secondNoteOn && !secondNoteSent)
		{
			std::cout << "[cb " << audioCallbackCount << "] Sending SECOND Note On (note "
				<< static_cast<int>(exp->secondNoteNumber) << ")" << std::endl;
			uc.sendMIDI(SMidiEvent(MidiEventSource::Host, 0x90, exp->secondNoteNumber, 0x5f));
			uc.sendPendingMidiEvents(std::numeric_limits<uint32_t>::max());
			secondNoteSent = true;
		}
		else if (audioCallbackCount == 300 && exp->useLiveParamChange && !chorusMixSent)
		{
			std::cout << "[cb " << audioCallbackCount << "] Sending Chorus Mix = 127" << std::endl;
			synthLib::SysexBuffer initSysex{
				0xf0, 0x00, 0x20, 0x33, 0x01, 0x00,
				112, virusLib::SINGLE, 105, 127,
				0xf7
			};
			std::vector<SMidiEvent> initResponses;
			uc.sendSysex(initSysex, initResponses, MidiEventSource::Host);
			chorusMixSent = true;
		}
		else if (audioCallbackCount == exp->liveParamCallback && exp->useLiveParamChange && !liveParamSent)
		{
			std::cout << "[cb " << audioCallbackCount << "] Sending live PARAM_CHANGE: page=0x"
				<< std::hex << static_cast<int>(exp->livePage) << " param=" << std::dec
				<< static_cast<int>(exp->liveParam) << " value=" << static_cast<int>(exp->liveValue)
				<< std::endl;
			synthLib::SysexBuffer sysex{
				0xf0, 0x00, 0x20, 0x33, 0x01, 0x00,
				exp->livePage, virusLib::SINGLE, exp->liveParam, exp->liveValue,
				0xf7
			};
			std::vector<SMidiEvent> responses;
			uc.sendSysex(sysex, responses, MidiEventSource::Host);
			liveParamSent = true;
		}

		// Deliberately a SEPARATE `if`, not another link in the else-if chain above: an
		// else-if would silently skip the sample on any run where some other branch happens
		// to claim the same callback number (exp->secondNoteCallback is caller-settable), and
		// a sample that silently didn't happen is the exact class of instrument defect that
		// makes a dump look like a measurement.
		if (exp->name == "sweep")
		{
			if (audioCallbackCount == 800 && !midFirst.valid)
				takeBaseSnapshot(midFirst, audioCallbackCount);
			else if (audioCallbackCount > 800 && (audioCallbackCount % 500) == 0)
				takeBaseSnapshot(midLast, audioCallbackCount);	// keeps the LAST one
		}
	});

	virusLib::Device::bootDSPs(dsp1.get(), dsp2raw, rom, false);

	// Render several seconds' worth of audio (discarded to a throwaway wav) purely to
	// drive the DSP thread forward in real time -- we only care about the resulting
	// DSP-internal memory state, not the audio content itself.
	// 8s: comfortably past note-on (cb 512) AND, for live-param experiments, past the
	// cb-700 PARAM_CHANGE send, with several seconds of settle time after it.
	constexpr uint32_t kMaxSampleCount = 8 * 44100;
	AudioProcessor proc(rom.getSamplerate(), "xmem_vocoder_probe_throwaway.wav", false, kMaxSampleCount, dsp1.get(), dsp2raw);

	std::cout << "Booted. Rendering ~5s of audio to drive the engine forward..." << std::endl;

	while (!proc.finished())
	{
		sem.wait();
		proc.processBlock(blockSize);
		// Deliberately NOT touching midiEvents here -- it's only ever written from the
		// audio-callback thread (uc.readMidiOut above); clearing it from this thread too,
		// as ConsoleApp::run() does, is an unsynchronized cross-thread race (hit a SIGBUS
		// from it during testing). We don't consume midiEvents' contents in this probe, so
		// simply never touching it from this thread is the simplest safe fix.
	}

	std::cout << "Done processing. Dumping X-memory of interest..." << std::endl;

	auto& mem = dsp1->getMemory();

	std::ofstream out(outFile);
	std::ostream& o = out;

	o << "Mode: " << exp->name << " (" << exp->paramLabel << (exp->wantNonZero ? " != 0" : " == 0") << ")\n";
	o << "Preset used: bank " << foundBank << " program " << foundProgram
		<< " name=\"" << ROMFile::getSingleName(preset) << "\"\n";
	o << exp->paramLabel << " byte (preset offset " << exp->paramOffset << ") = "
		<< static_cast<int>(preset[exp->paramOffset]) << "\n\n";

	// ---- MID-RENDER BASES REPORT (added 2026-08-03) -------------------------------------
	// Printed FIRST, before any end-of-render dump, because it is the only part of this file
	// that was sampled while a voice was actually sounding. Everything below it is
	// end-of-render state and is only trustworthy for absolute addresses, never for anything
	// reached through x:$1 / y:$1 / x:$B52.
	//
	// Window lines carry a "MID " prefix and are therefore invisible to tools/sweep_params.py's
	// parser, which anchors on `^\s*(x|y|dsp2_x|dsp2_y):\$`. That is intentional: these lines
	// hold DIFFERENT values for the SAME addresses as the end-of-render dump below, and letting
	// them fall into the same address->value map would silently corrupt every existing sweep
	// comparison. Opt in by matching "MID " explicitly.
	if (exp->name == "sweep")
	{
		const dsp56k::TWord endX1    = mem.get(dsp56k::MemArea_X, 0x1);
		const dsp56k::TWord endY1    = mem.get(dsp56k::MemArea_Y, 0x1);
		const dsp56k::TWord endVoice = mem.get(dsp56k::MemArea_X, 0xB52);

		auto printSnapshot = [&](const BaseSnapshot& _s, const char* _label)
		{
			if (!_s.valid)
			{
				o << "BASES " << _label << " NOT SAMPLED -- the render never reached that callback.\n"
					"      Treat every r1/r4/voice-relative reading in this dump as UNVERIFIED.\n";
				return;
			}
			o << "BASES cb" << _s.cb << " " << _label
				<< " x1=$" << std::hex << std::uppercase << _s.x1
				<< " y1=$" << _s.y1
				<< " voice=$" << _s.voice << std::dec
				<< "   (vs end-of-render x1=$" << std::hex << std::uppercase << endX1
				<< " y1=$" << endY1 << " voice=$" << endVoice << std::dec << ")"
				<< "   MOVED: x1=" << (_s.x1 != endX1 ? "YES" : "no")
				<< " y1=" << (_s.y1 != endY1 ? "YES" : "no")
				<< " voice=" << (_s.voice != endVoice ? "YES" : "no") << "\n";
		};

		auto printSnapshotWindows = [&](const BaseSnapshot& _s, const char* _label)
		{
			if (!_s.valid)
				return;
			const dsp56k::TWord bases[3] = { _s.x1, _s.y1, _s.voice };
			const char* names[3] = { "x1(r1)", "y1(r4)", "voice(x:$B52)" };
			size_t idx = 0;
			for (int bi = 0; bi < 3; ++bi)
			{
				const dsp56k::TWord start = bases[bi] >= kBaseWinBack ? bases[bi] - kBaseWinBack : 0;
				for (int area = 0; area < 2; ++area)
				{
					const char* an = (area == 0) ? "x" : "y";
					o << "--- MID cb" << _s.cb << " " << _label << " " << names[bi]
						<< " base=$" << std::hex << std::uppercase << bases[bi] << std::dec
						<< "  window " << an << ":$" << std::hex << std::uppercase << start << std::dec
						<< " (" << kBaseWinCount << " words, base sits at +$"
						<< std::hex << kBaseWinBack << std::dec << ") ---\n";
					for (uint32_t a = 0; a < kBaseWinCount; ++a, ++idx)
					{
						o << "MID " << an << ":$" << std::hex << std::uppercase << (start + a)
							<< " = $" << _s.win[idx] << std::dec;
						if (start + a == bases[bi])
							o << "   <-- base+0";
						o << "\n";
					}
				}
			}
		};

		o << "\n=== MID-RENDER BASES (sampled from inside the audio callback, voice sounding) ===\n";
		printSnapshot(midFirst, "EARLY");
		printSnapshot(midLast, "LATE");
		o << "BASES end-of-render x1=$" << std::hex << std::uppercase << endX1
			<< " y1=$" << endY1 << " voice=$" << endVoice << std::dec << "\n";
		if (midFirst.valid && midLast.valid)
		{
			o << "BASES early-vs-late MOVED: x1=" << (midFirst.x1 != midLast.x1 ? "YES" : "no")
				<< " y1=" << (midFirst.y1 != midLast.y1 ? "YES" : "no")
				<< " voice=" << (midFirst.voice != midLast.voice ? "YES" : "no") << "\n";
		}
		o << "\n";
		printSnapshotWindows(midFirst, "EARLY");
		printSnapshotWindows(midLast, "LATE");
		o << "=== END MID-RENDER BASES ===\n";
	}

	o << "\n--- DSP1 State ---\n";
	dumpRange(mem, dsp56k::MemArea_X, "x", 0xb50, 8, o);      // ownership-claim flags neighborhood
	dumpRange(mem, dsp56k::MemArea_Y, "y", 0x48293, 1, o);    // DSP-role strap
	dumpRange(mem, dsp56k::MemArea_Y, "y", 0x47b85, 4, o);    // Sync event logging rings
	dumpRange(mem, dsp56k::MemArea_Y, "y", 0x47be9, 4, o);
	dumpRange(mem, dsp56k::MemArea_Y, "y", 0x47c4d, 4, o);
	dumpRange(mem, dsp56k::MemArea_X, "x", 0x54130, 8, o);    // list-traversal tracking globals ($54131-$54136)
	
	if (dsp2raw)
	{
		o << "\n--- DSP2 State ---\n";
		auto& mem2 = dsp2raw->getMemory();
		dumpRange(mem2, dsp56k::MemArea_Y, "y", 0x48293, 1, o);    // DSP-role strap
		dumpRange(mem2, dsp56k::MemArea_Y, "y", 0x47b85, 4, o);    // Sync event logging rings
		dumpRange(mem2, dsp56k::MemArea_Y, "y", 0x47be9, 4, o);
		dumpRange(mem2, dsp56k::MemArea_Y, "y", 0x47c4d, 4, o);
	}
	
	o << "\n--- End Dual-DSP Data ---\n";
	// doc/dsp56300_synth_engine.md's harmonic-engine section: $49940 = active slot count
	// (derived from voice +$94), $49942 = table running pointer, $49943/$49944 and $49947/$49948
	// = two (accumulator, delta) channel pairs.
	dumpRange(mem, dsp56k::MemArea_X, "x", 0x49940, 10, o);

	// X:$b52 is documented as an ownership-claim pointer, not a fixed table base -- follow
	// it live rather than assuming the static-image template address (0x49800).
	const auto b52 = mem.get(dsp56k::MemArea_X, 0xb52);
	o << "\nX:$b52 = $" << std::hex << std::uppercase << b52 << std::dec << " -- ";
	if (b52 != 0)
	{
		o << "nonzero, following it as a pointer (dumping 320 words = 32 slots x 10 words, "
			"per the documented table shape):\n";
		dumpRange(mem, dsp56k::MemArea_X, "x", b52, 320, o);
		// Also dump some words *before* the pointer in case it points mid-structure or the
		// header precedes the slot array.
		if (b52 >= 16)
			dumpRange(mem, dsp56k::MemArea_X, "x", b52 - 16, 16, o);
	}
	else
	{
		o << "zero / unclaimed, nothing to follow.\n";
	}

	// Also dump the static-image template region for reference/comparison.
	dumpRange(mem, dsp56k::MemArea_X, "x", 0x49800, 32, o);

	// work/dsp_osc_thread3_investigation_findings.md / work/dsp_osc_thread3_live_probe_and_correction.md:
	// func_056006's lazy-allocated singleton object (x:>$1f8b, same "allocate once, gated by
	// x:>$1f3a" pattern as the Vocoder table above) has a per-object "+$2b" field, fed by a
	// 59-word (0x3b) template statically read from X:$45c80 -- nothing in the static image
	// writes X:$45c80 directly, so this probe was added to read both live. Live result: +$2b
	// is irrelevant to the jmp(r5) dispatch this was originally chasing (see the "correction"
	// work file), but X:$45c80 is confirmed real, structured data worth having live visibility
	// into regardless.
	o << "\n--- x:>$1f8b singleton object (func_056006) ---\n";
	const auto obj1f8b = mem.get(dsp56k::MemArea_X, 0x1f8b);
	o << "X:$1f8a = $" << std::hex << std::uppercase << mem.get(dsp56k::MemArea_X, 0x1f8a) << std::dec << "\n";
	o << "X:$1f8b = $" << std::hex << std::uppercase << obj1f8b << std::dec << " -- ";
	if (obj1f8b != 0)
	{
		o << "nonzero, dumping 0x3c (60) words from the object base (covers the full 0x3b-word "
			"template, including +$2b/+$32):\n";
		dumpRange(mem, dsp56k::MemArea_X, "x", obj1f8b, 0x3c, o);
	}
	else
	{
		o << "zero / not yet allocated, nothing to follow.\n";
	}
	o << "\n--- X:$45c80 template/table region (4 records x 0x3b words, per func_052f46's stride) ---\n";
	dumpRange(mem, dsp56k::MemArea_X, "x", 0x45c80, 0x3b * 4, o);

	if (exp->name == "unison" || exp->name == "unison_control" ||
		exp->name == "unison_live" || exp->name == "unison_live_control" ||
		exp->name == "unison_live_pretrigger" || exp->name == "unison_live_pretrigger_control" ||
		exp->name == "inert_param_live_pretrigger" || exp->name == "inert_param_live_pretrigger_control" ||
		exp->name == "chord_2note")
	{
		// func_00024c ("resolve my primary voice") caches the resolved primary's +$2 field
		// here, and one confirmed caller scatters a per-tick value into a primary-+$27-indexed
		// slot of this 66-word table -- see doc/dsp56300_synth_engine.md.
		dumpRange(mem, dsp56k::MemArea_X, "x", 0x54136, 1, o);
		dumpRange(mem, dsp56k::MemArea_X, "x", 0x56684, 66, o);

		// The direct structural test this session was added for: walk the active-voice linked
		// list itself and report its node count/pointers, rather than only the secondary
		// tracking globals above (which the prior session's unison_live* runs already showed no
		// unison-specific signal in).
		dumpVoiceLinkedList(mem, o);
	}

	if (exp->name == "sweep")
	{
		// Dump the full X and Y internal memory
		dumpRange(mem, dsp56k::MemArea_X, "x", 0x0000, 0x10000, o);
		dumpRange(mem, dsp56k::MemArea_Y, "y", 0x0000, 0x10000, o);
		
		if (dsp2raw) {
			auto& mem2 = dsp2raw->getMemory();
			dumpRange(mem2, dsp56k::MemArea_X, "dsp2_x", 0x0000, 0x10000, o);
			dumpRange(mem2, dsp56k::MemArea_Y, "dsp2_y", 0x0000, 0x10000, o);
		}

		// func_05c9e8 VM cluster (doc/dsp56300_synth_engine.md): its struct fields
		// ($5c67a-$5c69d) sit above the 0x10000 ceiling of the bulk dump above, so
		// they're otherwise invisible to "sweep" mode -- dump them explicitly, both DSPs.
		dumpRange(mem, dsp56k::MemArea_X, "x", 0x5c670, 0x90, o);
		// Phaser Rate/Depth/Frequency/Feedback/Spread live-sweep candidates.
		dumpRange(mem, dsp56k::MemArea_X, "x", 0x49be0, 0x11, o);
		dumpRange(mem, dsp56k::MemArea_Y, "y", 0x49be0, 0x11, o);
		// Master patch-setup program's module/parameter-cell region (doc/dsp56300_synth_engine.md's
		// "master patch-setup program" section): Filter Bank Type's own value cells (X:$56698,
		// X:$5669f) plus the already-confirmed Rotary/Chorus module cells (X:$566aa-$566af) and
		// HyperSaw master cells (X:$566b2-$566b8) all live here, above the 0x10000 ceiling and
		// outside every other window above -- 2026-07-23, added because a Filter Bank Mix sweep
		// found zero effect anywhere in the windows that existed before this one, and this is
		// exactly the address family the analogous Rotary/Chorus/HyperSaw module cells turned out
		// to live in. See work/dsp_filterbank_continuous_subparams_sweep_2026-07-23.md.
		dumpRange(mem, dsp56k::MemArea_X, "x", 0x56680, 0x100, o);
		if (dsp2raw) {
			auto& mem2 = dsp2raw->getMemory();
			dumpRange(mem2, dsp56k::MemArea_X, "dsp2_x", 0x5c670, 0x90, o);
			dumpRange(mem2, dsp56k::MemArea_X, "dsp2_x", 0x49be0, 0x11, o);
			dumpRange(mem2, dsp56k::MemArea_Y, "dsp2_y", 0x49be0, 0x11, o);
			dumpRange(mem2, dsp56k::MemArea_X, "dsp2_x", 0x56680, 0x100, o);
		}

		// $757xx REVERB-TYPE COVERAGE WINDOW, added 2026-08-03 (ADDITIVE -- no existing
		// address changes value or disappears, so a concurrent sweep against the previous
		// binary stays comparable).
		//
		// WHY IT IS AN ABSOLUTE WINDOW AND NOT AN EXTENSION OF AN EXISTING ONE. The nearest
		// window in this block is $56680-$5677F; reaching $757B0 by extension would dump
		// ~0x1F130 extra words per area, i.e. more than the entire rest of the sweep. There
		// is nothing to extend -- $757xx is its own island.
		//
		// WHY THIS ADDRESS. work/dsp_reverb_remaining_params_sweep_2026-07-23.md attributes a
		// Reverb-Type coefficient trio to "DSP2_X:$75797/$75799/$7579A". Read back from the
		// raw dumps it cites (work/dsp_reverb_sweep_2026-07-23/type/*.txt) the label on those
		// lines is `x:`, i.e. DSP1 X, and they came from the RUNTIME-POINTER follow of
		// X:$b52 further down this function -- in that run X:$b52 happened to be $7570C, so
		// the 320-word follow window covered $7570C-$7584B. That base is voice-allocation
		// dependent: a different preset, or a render that ends with no claimed voice, moves
		// or removes the window entirely, which is exactly why the 2026-08-03 reverb sweep
		// saw nothing at these addresses. So dump the region at an ABSOLUTE address, on BOTH
		// DSPs and both areas, and let the data say which DSP it is rather than inheriting
		// the prior note's attribution.
		//
		// The range is $75700-$757FF rather than the minimal $75780-$757B0 because the same
		// 2026-07-23 dump shows a structurally identical quad at $7577C-$7577F (stride $1B),
		// and a claim about $75797 that cannot see its stride partner is not checkable.
		dumpRange(mem, dsp56k::MemArea_X, "x", 0x75700, 0x100, o);
		dumpRange(mem, dsp56k::MemArea_Y, "y", 0x75700, 0x100, o);
		if (dsp2raw) {
			auto& mem2 = dsp2raw->getMemory();
			dumpRange(mem2, dsp56k::MemArea_X, "dsp2_x", 0x75700, 0x100, o);
			dumpRange(mem2, dsp56k::MemArea_Y, "dsp2_y", 0x75700, 0x100, o);
		}
	}
		o << "--- X:$1F38 area ---\n";
		for(int i=0; i<8; i++) {
			o << "  X:$" << std::hex << (0x1F38 + i) << " = $" << mem.get(dsp56k::MemArea_X, 0x1F38 + i) << "\n";
		}
		o << "--- Voice Node $49B9E (Extended) ---\n";
		// EXTENDED 0x200 -> 0x300 on 2026-08-02, and the reason is worth keeping.
		//
		// At 0x200 this window ended at $49CFF. func_051004 takes its struct pointers from
		// x:$1 and y:$1, which hold DIFFERENT bases -- measured live: x:$1 = $49BB9 (r1, X side)
		// and y:$1 = $49D22 (r4, Y side). So every `y:(r4+N)` in func_050f2e-func_0510fe lands at
		// $49D22+N, and the r4 base sat 0x22 words PAST the end of this range. func_0510fe's two
		// stores -- y:(r4+$70) = Y:$49D92 (curve-table pointer) and y:(r4+$71) = Y:$49D93
		// (tap-table pointer) -- were therefore never dumped.
		//
		// 36 sweep runs were spent watching cells derived from the voice pointer x:$B52 = $49B9E
		// instead, found nothing, and the nothing was uninformative: the target was outside the
		// instrument. Both a "falsified" verdict and its retraction came out of that
		// (work/page112_sweep_coverage_gap_2026-08-02.md). 0x300 reaches $49DFF, covering the r4
		// base through +$dd, which spans every offset this subsystem uses (+$64 .. +$77).
		//
		// The X side is widened to match deliberately: r1 and r4 are separate objects here, and
		// assuming a shared base is precisely the error that cost those 36 runs.
		dumpRange(mem, dsp56k::MemArea_X, "x", 0x49B00, 0x300, o);
		dumpRange(mem, dsp56k::MemArea_Y, "y", 0x49B00, 0x300, o);
		
		o << "--- Voice Node $73B2F ---\n";
		dumpRange(mem, dsp56k::MemArea_X, "x", 0x73B2F, 64, o);

	out.close();
	std::cout << "Wrote " << outFile << std::endl;

	return 0;
}
