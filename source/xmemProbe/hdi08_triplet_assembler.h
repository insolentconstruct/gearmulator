// Local RE tooling for the virus-os-decompile project, NOT part of upstream gearmulator.
//
// Milestone 4 (offline HDI08 relay), Phase B/C prerequisite: the byte-triplet <-> 24-bit
// HDI08-word assembler. Design: work/8051_oracle_milestone4_design_2026-07-28.md, section 4
// ("The byte-triplet assembler — the one genuinely new piece of code") and section 9.1 (the
// acceptance test this header is built to satisfy).
//
// Nothing in dsp56kEmu (dsp56300/dsp56300/source/dsp56kEmu/hdi08.{h,cpp}) or virusLib turns
// three separate 8-bit host register writes/reads (the 8051's own view of the DSP56300's HI08
// peripheral, at XDATA offsets +0..+7 within each DSP's register block) into one 24-bit
// dsp56k::TWord for HDI08::writeRX/readTX, or back. This header is that missing piece,
// deliberately written with zero dependency on dsp56kEmu/gearmulator so it can be unit-tested
// standalone (see hdi08_triplet_assembler_test.cpp) before Phase B links it against the real
// HDI08 class inside xmemProbe.cpp.
//
// ---------------------------------------------------------------------------------------------
// Register table and write order — re-derived directly from raw disassembly before writing any
// of the logic below, per AGENTS.md's Verification Discipline (the design doc explicitly flags
// its own table as "transcribed from an existing doc, not independently re-checked for this
// design pass").
//
// CODE:0x6113 (work/listing_8051.txt:17761-17796), the 8051's own broadcast-a-word-to-both-DSPs
// routine:
//   MOV A,#0x31 ; MOV DPTR,#0x0 ; MOVX @DPTR,A ; INC DPH ; MOVX @DPTR,A
//       -- writes ICR=0x31 to BOTH DSP register blocks (0x0000 and 0x0100).
//       0x31 = RREQ(bit0=0x01) | HF1(bit4=0x10) | HLEND(bit5=0x20). Confirmed against
//       dsp56300/mc68k/hdi08.h's IcrBits enum (Rreq=1<<0, Hf1=1<<4, Hlend=1<<5): 0x01+0x10+0x20
//       = 0x31 exactly. So HLEND=1 is asserted, not a guess.
//   MOV DPTR,#0x5 ; MOV A,R7 ; MOVX @DPTR,A      -- write R7 to XDATA offset +5 (first DSP block)
//   INC DPL       ; MOV A,R6 ; MOVX @DPTR,A      -- write R6 to XDATA offset +6
//   INC DPL       ; MOV A,R5 ; MOVX @DPTR,A      -- write R5 to XDATA offset +7
//   MOV DPTR,#0x105 ; ... (identical R7,R6,R5 sequence to offsets 0x105/0x106/0x107, the
//       second DSP's block)
// This directly confirms, from raw bytes, both claims the design doc asked to be re-checked:
// the +5/+6/+7 register table (TXH/TXM/TXL, one 8051 write cycle broadcasting the same word to
// both DSPs) AND the write order R7->TXH(+5, written first), R6->TXM(+6), R5->TXL(+7, written
// last).
//
// CODE:0x61AF (work/listing_8051.txt:17849-17859), the boot-ack poll:
//   JNB 0xb2,... ; JB 0x05,... ; ... ; CLR 0x05 ; MOV DPTR,#0x7 ; MOVX A,@DPTR ; RET
// Gates on bit 0xb2 (P3.2/INT0, a real physical pin per
// doc/8051_boot_and_memory_map.md:155's SFR-bit-address note) before reading XDATA offset +7
// only -- a single-byte read of RXL, consistent with the +5/+6/+7 = TXH/TXM/TXL table (RXL
// lives at the same physical register as TXL, offset +7) but this particular call site does
// NOT itself exercise a full H,M,L three-register read -- see the endianness note below for why
// that distinction matters and what's actually confirmed vs. assumed on the RX side.
//
// ---------------------------------------------------------------------------------------------
// Endianness — CORRECTS a formula error in the design doc's own section 4.
//
// work/8051_oracle_milestone4_design_2026-07-28.md section 4 states the assembler should
// compute (H<<16)|(M<<8)|L when HLEND=1. That is backwards. The real DSP56300 HI08 peripheral's
// documented HLEND behavior -- independently modeled TWICE in this codebase, byte-for-byte, by
// two different device libraries emulating the identical silicon block (dsp56300/mc68k/hdi08.cpp,
// used for the MC68K-hosted synths that address HI08 at the same byte granularity the 8051 host
// bus uses; dsp56kEmu's own HDI08 sidesteps this entirely by only exposing whole-word
// writeRX/readTX with no byte-level model at all) -- is:
//
//   Hdi08::writeTX (dsp56300/mc68k/hdi08.cpp:221-245):
//       const auto word = littleEndian() ? l<<16 | m<<8 | h : h<<16 | m<<8 | l;
//   Hdi08::readRX  (dsp56300/mc68k/hdi08.cpp:267-323), the exact byte-order mirror:
//       le: bytes[0]=word&0xff (H reads word's LSB), bytes[2]=(word>>16)&0xff (L reads word's MSB)
//       !le: bytes[0]=(word>>16)&0xff (H reads word's MSB), bytes[2]=word&0xff (L reads word's LSB)
//
// So under HLEND=1 (this firmware's only observed mode), the register named "Low" carries the
// word's MOST significant byte and "High" carries the LEAST significant byte -- the naming
// refers to register ADDRESS ordering (H is written/read first), not byte significance. This is
// confirmed a THIRD, independent way: doc/8051_boot_and_memory_map.md:869-871 already flagged
// this from the raw 8051 disassembly alone ("the actual 24-bit word the DSP receives is
// R5<<16 | R6<<8 | R7 -- R5 is most significant despite being written to the register named
// Low"), which is exactly R5(TXL)<<16 | R6(TXM)<<8 | R7(TXH), i.e. TXL<<16|TXM<<8|TXH -- the
// same formula this header implements, and the opposite of the design doc's own section 4 text.
// Three independent derivations (this file's own read of dsp56300/mc68k/hdi08.cpp, the pre-existing
// doc/8051_boot_and_memory_map.md note, and the raw ICR=0x31/HLEND=1 decode) all agree; the
// design doc's section 4 formula is the one outlier and should be treated as wrong. Not yet
// corrected in the design doc itself -- flagged for a follow-up doc edit, not done as part of
// this change (this file is the load-bearing correction; the design doc's prose is now stale
// relative to it).
//
// The big-endian (HLEND=0) case is included for completeness and to avoid silently hard-coding
// HLEND=1, per the design doc's own explicit caveat -- not because it's been observed on this
// firmware. Every known transfer on this path sets ICR=0x31 (HLEND=1) and leaves it; assembleStream()
// below defaults to hlend=true but takes it as an explicit parameter rather than assuming it
// silently, and callers that care should assert the bit themselves before relying on the default.
//
// ---------------------------------------------------------------------------------------------
// What is NOT independently confirmed by raw disassembly (flag, not silently upgraded to
// "confirmed" -- Verification Discipline rule 6, default to falsify):
//
// The design doc's section 4 describes the assembler as "symmetric": one popped writeRX/readTX
// word "split back into three bytes... in the same H/M/L order as three separate reads of
// +5/+6/+7". CODE:0x61AF only reads offset +7 (RXL) as a single byte; no 8051 code site
// exercising a genuine three-register H,M,L read of one DSP word was found in this pass. (A
// different 3x-same-address pattern DOES exist in this firmware --
// doc/8051_boot_and_memory_map.md's "CODE:0x2644+ 0xF4/0xF5 command dispatcher" section
// describes code that reads XDATA:0x0007 (RXL) three times in a row with retry delays between
// each -- but that is three separate single-byte polls of the SAME register within a
// higher-level command/payload protocol, not a H,M,L read of three DIFFERENT registers
// assembling one 24-bit word, so it does not confirm or contradict the H/M/L-triple-read
// symmetry claim either way.) disassembleWord()/assembleStream()'s inverse below are therefore
// grounded in the HI08 peripheral's confirmed hardware behavior (real silicon, cross-confirmed
// by two independent device libraries, not firmware-specific), not in having found live 8051
// code that performs a symmetric 3-register RX read -- keep that distinction if this header is
// later used to justify a claim about what the 8051 firmware itself does on the RX side.

#pragma once

#include <array>
#include <cstddef>
#include <cstdint>
#include <stdexcept>
#include <vector>

namespace virusOracle
{
	// Matches dsp56k::TWord (dsp56300/dsp56300/source/dsp56kEmu/types.h:21, "typedef uint32_t
	// TWord"), duplicated here rather than included so this header has zero dependency on
	// dsp56kEmu/gearmulator.
	using TWord = uint32_t;

	// One 8051-side HDI08 write (or read) cycle's worth of bytes, always in the same H,M,L
	// order the 8051 firmware itself uses -- write order confirmed at CODE:0x6113 (TXH first,
	// from R7; TXM second, from R6; TXL last, from R5).
	struct Hdi08Triplet
	{
		uint8_t h = 0;  // XDATA offset +5 (TXH on write / RXH on read)
		uint8_t m = 0;  // XDATA offset +6 (TXM on write / RXM on read)
		uint8_t l = 0;  // XDATA offset +7 (TXL on write / RXL on read)

		constexpr bool operator==(const Hdi08Triplet& _o) const
		{
			return h == _o.h && m == _o.m && l == _o.l;
		}
	};

	// Assemble one 24-bit HDI08 word from a host-side H/M/L byte triplet.
	//
	// _hlend=true (ICR.HLEND=1, this firmware's only confirmed mode, see file header):
	//     word = (L << 16) | (M << 8) | H     -- "Low" is most significant.
	// _hlend=false (big-endian HI08 mode, not observed on this firmware but not silently
	// assumed away either, per the design doc's own caveat):
	//     word = (H << 16) | (M << 8) | L     -- "High" is most significant, matching the name.
	constexpr TWord assembleWord(const Hdi08Triplet& _t, bool _hlend)
	{
		return _hlend
			? (static_cast<TWord>(_t.l) << 16) | (static_cast<TWord>(_t.m) << 8) | static_cast<TWord>(_t.h)
			: (static_cast<TWord>(_t.h) << 16) | (static_cast<TWord>(_t.m) << 8) | static_cast<TWord>(_t.l);
	}

	// Split one 24-bit DSP-originated word back into the H/M/L byte triplet an 8051-side reader
	// would observe polling RXH/RXM/RXL, in the same H,M,L order. Exact algebraic inverse of
	// assembleWord() for the same _hlend -- see the file header's "what is NOT independently
	// confirmed" note before treating this as validated against live 8051 RX-read disassembly;
	// it is grounded in the HI08 peripheral's confirmed hardware behavior instead.
	constexpr Hdi08Triplet disassembleWord(TWord _word, bool _hlend)
	{
		if (_hlend)
		{
			return Hdi08Triplet{
				static_cast<uint8_t>(_word & 0xffu),          // RXH = word's LSB
				static_cast<uint8_t>((_word >> 8) & 0xffu),   // RXM = word's mid byte
				static_cast<uint8_t>((_word >> 16) & 0xffu),  // RXL = word's MSB
			};
		}
		return Hdi08Triplet{
			static_cast<uint8_t>((_word >> 16) & 0xffu),
			static_cast<uint8_t>((_word >> 8) & 0xffu),
			static_cast<uint8_t>(_word & 0xffu),
		};
	}

	// Assemble a flat byte stream -- as recorded by the oracle's --hdi08-dump/--hdi08-dump2
	// (three bytes per HDI08 write cycle, in the 8051's own TXH,TXM,TXL wire order) -- into a
	// vector of 24-bit words. Takes _hlend as an explicit parameter (defaulting to true, this
	// firmware's only confirmed mode) rather than hard-coding it, per the design doc's own
	// caveat against silently assuming the bit. Throws std::invalid_argument if the stream
	// length is not a multiple of 3 (an incomplete final triplet).
	inline std::vector<TWord> assembleStream(const std::vector<uint8_t>& _bytes, bool _hlend = true)
	{
		if (_bytes.size() % 3 != 0)
			throw std::invalid_argument("assembleStream: byte count is not a multiple of 3 (incomplete triplet)");

		std::vector<TWord> words;
		words.reserve(_bytes.size() / 3);

		for (size_t i = 0; i < _bytes.size(); i += 3)
		{
			const Hdi08Triplet t{_bytes[i], _bytes[i + 1], _bytes[i + 2]};
			words.push_back(assembleWord(t, _hlend));
		}

		return words;
	}

	// Inverse of assembleStream(): flatten a vector of 24-bit words back into a byte stream in
	// H,M,L wire order per word. For Phase C's future use (feeding recorded DSP replies back
	// into the oracle's --hdi08-rx tape: consumption) -- not exercised by any oracle code yet,
	// included here because it is the direct, trivially-derived counterpart of assembleStream()
	// and belongs with it rather than being re-derived later.
	inline std::vector<uint8_t> disassembleStream(const std::vector<TWord>& _words, bool _hlend = true)
	{
		std::vector<uint8_t> bytes;
		bytes.reserve(_words.size() * 3);

		for (const TWord w : _words)
		{
			const Hdi08Triplet t = disassembleWord(w, _hlend);
			bytes.push_back(t.h);
			bytes.push_back(t.m);
			bytes.push_back(t.l);
		}

		return bytes;
	}
}
