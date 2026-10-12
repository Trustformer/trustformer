#!/usr/bin/env python3
"""Fail on out-of-range part-selects in generated Verilog: Koika's semantics
zero-pads them, Verilog leaves the extra bits undefined (Yosys makes them 'x').
Usage: scripts/check-ranges.py build/*.v"""
import shutil
import subprocess
import sys


def find_verilator():
    if shutil.which("verilator"):
        return "verilator"
    sys.exit("verilator not found -- run inside 'nix develop'")


def out_of_range(verilator, path):
    lint = subprocess.run([verilator, "--lint-only", "-Wall", "-Wno-fatal", path],
                          capture_output=True, text=True)
    by_loc = {}
    for line in lint.stderr.splitlines():
        if line.startswith("%Warning-SELRANGE: "):
            loc, _, msg = line[len("%Warning-SELRANGE: "):].partition(": ")
            by_loc.setdefault(loc, []).append(msg)
    return by_loc


def main(paths):
    verilator = find_verilator()
    bad = 0
    for path in paths:
        for loc, msgs in out_of_range(verilator, path).items():
            bad += 1
            print(f"{loc}: {'; '.join(msgs)}")
    if bad:
        print(f"FAIL: {bad} out-of-range select(s); the extra bits are undefined in the netlist")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
