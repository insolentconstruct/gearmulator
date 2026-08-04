import json

with open("dsp56300/gearmulator/source/osTIrusJucePlugin/parameterDescriptions_TI.json", "r") as f:
    data = json.load(f)

for p in data:
    if p["name"] == "Arp Mode":
        print(f"Arp Mode: page {p['page']} (0x{p['page']:02x}), index {p['index']}")

