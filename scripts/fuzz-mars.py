#!/usr/bin/env python3
"""Differential fuzz of build/Example_MarsV2.v against the TCG reference emulator.

    scripts/fuzz-mars.py --emulator <dir> [--commands N] [--seed S ...] [--design FILE] [--keep DIR]

sim/fuzz/gen_mars_v2.c draws a seeded command stream and records, through the
emulator, the full public state expected after every command; the bench
sim/fuzz/tb_fuzz_mars_v2.sv replays it on the module with the real SHA/HMAC IPs.
The run fails on any mismatching line, adapter FAIL line or hang, and on any
public latency class that shows more than one cycle count.

Opt-in: `make test` never runs it.  The emulator is the TCG reference emulator
(github.com/TrustedComputingGroup/BIT, commit 63a59bed, c/); point --emulator
at it.  Run inside `nix develop`.
"""
import argparse
import importlib.util
import os
import shutil
import subprocess
import sys
import tempfile
from collections import Counter, defaultdict

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
GEN = os.path.join(ROOT, "sim", "fuzz", "gen_mars_v2.c")
TB = os.path.join(ROOT, "sim", "fuzz", "tb_fuzz_mars_v2.sv")
DESIGN = os.path.join(ROOT, "build", "Example_MarsV2.v")

NAMES = {0: "SelfTest", 1: "CapabilityGet", 2: "SequenceHash", 3: "SequenceUpdate",
         4: "SequenceComplete", 5: "PcrExtend", 6: "RegRead", 7: "Derive",
         8: "DpDerive", 9: "PublicRead", 10: "Quote", 11: "Sign",
         12: "SignatureVerify", 0xFFFF: "_MARS_Init"}
FIELDS = ["i", "code", "rc", "cap", "result", "dout", "snap", "pcr0", "pcr1", "failure", "st"]
RCS = ["0", "2", "4", "5", "6", "7"]


def load(name, file):
    spec = importlib.util.spec_from_file_location(name, os.path.join(ROOT, "scripts", file))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


golden = load("regen_golden", "regen-golden.py")
runsim = load("run_sim", "run-sim.py")


def build_bench(verilator, design, d):
    os.makedirs(d, exist_ok=True)
    rtl = [TB, design] + runsim.REAL_IP
    for f in rtl:
        shutil.copy(f, d)
    cmd = [verilator, "--binary", "--main", "--timing", "-Wno-fatal",
           "--build-jobs", "2", "--top-module", "tb_fuzz_mars_v2"]
    cmd += [os.path.basename(f) for f in rtl]
    build = subprocess.run(cmd, cwd=d, capture_output=True, text=True)
    if build.returncode:
        sys.exit("verilator failed:\n" + build.stderr.strip()[-2000:])
    return os.path.join(d, "obj_dir", "Vtb_fuzz_mars_v2")


def run_seed(gen, sim, seed, n, d):
    """Generate and replay one stream; return its file paths and the sim log."""
    f = {k: os.path.join(d, f"{k}.s{seed}.txt") for k in ("cmds", "exp", "meta", "hw", "lat")}
    pre = 20 + seed % 6
    g = subprocess.run([gen, str(seed), str(n), str(pre), f["cmds"], f["exp"], f["meta"]],
                       cwd=os.path.dirname(gen), capture_output=True, text=True)
    if g.returncode:
        sys.exit(f"gen_mars_v2 failed for seed {seed}:\n{g.stderr}")
    s = subprocess.run([sim, f"+cmds={f['cmds']}", f"+out={f['hw']}", f"+lat={f['lat']}"],
                       cwd=os.path.dirname(sim), capture_output=True, text=True)
    return f, s.stdout + s.stderr


def compare(runs):
    rules, tags, lat = Counter(), Counter(), defaultdict(Counter)
    cov = defaultdict(Counter)
    total, bad, fails, hangs, mismatches = 0, 0, 0, 0, []
    for seed, f, log in runs:
        fails += sum("FAIL" in l for l in log.splitlines())
        hangs += sum(l.startswith("HANG") for l in log.splitlines())
        exp = open(f["exp"]).read().splitlines()
        hw = open(f["hw"]).read().splitlines() if os.path.exists(f["hw"]) else []
        meta = open(f["meta"]).read().splitlines()
        lats = open(f["lat"]).read().splitlines() if os.path.exists(f["lat"]) else []
        if len(hw) != len(exp):
            bad += 1
            mismatches.append(f"seed {seed}: {len(hw)} hardware lines for {len(exp)} expected")
        for k, e in enumerate(exp):
            total += 1
            ef = e.split()
            _, _, rule, tag, fault, tcls = meta[k].split()
            rules[rule] += 1
            tags[tag] += 1
            cov[NAMES.get(int(ef[1], 16), "unknown")][ef[2]] += 1
            if k < len(lats):
                lat[tcls][int(lats[k].split()[3])] += 1
            h = hw[k] if k < len(hw) else ""
            if h != e:
                bad += 1
                hf = h.split()
                diff = [f"{FIELDS[j]}: exp {ef[j]} hw {hf[j] if j < len(hf) else '-'}"
                        for j in range(len(ef)) if j >= len(hf) or ef[j] != hf[j]]
                if len(mismatches) < 40:
                    mismatches.append(f"seed {seed} line {ef[0]} {NAMES.get(int(ef[1], 16), 'unknown')}"
                                      f" ({rule} {tag}): " + "; ".join(diff))
    return total, bad, fails, hangs, mismatches, rules, tags, cov, lat


def report(total, bad, fails, hangs, mismatches, rules, tags, cov, lat):
    emu = sum(v for r, v in rules.items() if r.startswith("E"))
    print(f"commands compared: {total}   mismatching lines: {bad}   "
          f"adapter FAIL lines: {fails}   hangs: {hangs}")
    print(f"answered by the emulator: {emu} ({100 * emu / total:.1f}%)   "
          f"checked against Profile rules: {total - emu} ({100 * (total - emu) / total:.1f}%)")
    print("rules: " + "  ".join(f"{r}={rules[r]}" for r in sorted(rules)))
    if mismatches:
        print("MISMATCHES:\n  " + "\n  ".join(mismatches))

    print("\nper command x rc:")
    print(f"  {'':<17}" + "".join(f"{'rc=' + r:>9}" for r in RCS))
    order = {v: k for k, v in NAMES.items()} | {"unknown": 1 << 20}
    for c in sorted(cov, key=order.get):
        print(f"  {c:<17}" + "".join(f"{cov[c].get(r, '-'):>9}" for r in RCS))

    split = [c for c in lat if len(lat[c]) > 1]
    print("\nbusy cycles per public latency class (one count expected per class):")
    for c in sorted(lat):
        counts = ", ".join(f"{nb} x{k}" for nb, k in sorted(lat[c].items()))
        print(f"  {c:<26} {counts}{'   <-- MORE THAN ONE' if c in split else ''}")
    return split


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--emulator", required=True,
                    help="directory holding the TCG reference C sources")
    ap.add_argument("--commands", type=int, default=3000, help="commands per seed")
    ap.add_argument("--seed", type=int, nargs="+", default=[1, 2, 3, 4],
                    help="each seed adds its own pre-Init phase")
    ap.add_argument("--design", default=DESIGN,
                    help="the Example_MarsV2 Verilog to test (default: build/)")
    ap.add_argument("--keep", metavar="DIR", help="keep the work files in DIR")
    args = ap.parse_args()

    if not os.path.isfile(args.design):
        sys.exit(f"{args.design} is missing -- run 'make all'")
    verilator = runsim.find_verilator()

    with tempfile.TemporaryDirectory() as tmp:
        work = os.path.abspath(args.keep) if args.keep else tmp
        emu = os.path.join(work, "emu")
        os.makedirs(emu, exist_ok=True)
        gen, _ = golden.build_emulator(args.emulator, GEN, emu, exe="gen_mars_v2",
                                       cflags=("-O2", "-std=gnu99", "-I.", "-include", "hw_sha2.h",
                                               "-Wno-deprecated-declarations"))
        sim = build_bench(verilator, os.path.abspath(args.design), os.path.join(work, "tb"))
        runs = []
        for seed in args.seed:
            f, log = run_seed(gen, sim, seed, args.commands, os.path.join(work, "tb"))
            runs.append((seed, f, log))
        result = compare(runs)
        split = report(*result)

    total, bad, fails, hangs = result[:4]
    ok = not (bad or fails or hangs or split)
    print(f"\n{'PASS' if ok else 'FAIL'}  ({total} commands, seeds {' '.join(map(str, args.seed))})")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
