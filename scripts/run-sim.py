#!/usr/bin/env python3
"""Run the testbenches in sim/ against the generated Verilog in build/.

    scripts/run-sim.py [-j N] [name ...]   names default to every testbench,
                                           N to half the CPUs

Every testbench decides its own verdict: it prints PASS or FAIL and exits
non-zero on failure.  This script only builds it, runs it, and reports.
See sim/README.md.
"""
import glob
import os
import shutil
import subprocess
import sys
import tempfile
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass, field

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

# The vendored crypto IP and the adapters that join it to a Trusted port group.
REAL_IP = sorted(glob.glob(os.path.join(ROOT, "external/glue/*.v"))
                 + glob.glob(os.path.join(ROOT, "external/sha256/*.v")))


@dataclass
class Bench:
    design: str                          # the build/<design>.v it drives
    sources: list = field(default_factory=list)   # extra RTL, absolute paths
    defines: dict = field(default_factory=dict)


BENCHES = {
    # Against a MODEL of the IP: identity or +1, latency 3, not pipelined.
    "tb_call":      Bench("Regression_Call"),
    "tb_two":       Bench("Regression_TwoCall"),
    "tb_chain":     Bench("Regression_ChainedCall"),
    "tb_branch":    Bench("Regression_BranchCall"),
    "tb_guard":     Bench("Regression_GuardCall"),
    "tb_arms":      Bench("Regression_ArmsSeq"),
    "tb_untaken":   Bench("Regression_ArmsSeq"),
    "tb_xport":     Bench("Regression_XPortGuard"),
    "tb_mars":      Bench("Example_Mars"),
    "tb_macrolib":  Bench("Regression_MacroLib"),

    # Against the REAL secworks/sha256 core through external/glue/.
    "tb_mars_v4": Bench(
        "Example_Mars",
        sources=REAL_IP,
        defines={"CORE_DIV": 1, "IP_LAT_SHA": 140, "IP_LAT_HMAC": 275},
    ),
    "tb_mars_pcrextend": Bench("Example_MarsSeq", sources=REAL_IP),

    # The Knox examples, coq/Examples/Knox/.
    "tb_knox_fig2":            Bench("Knox_Fig2Backup"),
    "tb_knox_pin_backup":      Bench("Knox_PinBackup"),
    "tb_knox_password_hasher": Bench("Knox_PwHasher", sources=REAL_IP),
    "tb_knox_otp":             Bench("Knox_Otp", sources=[os.path.join(ROOT, "sim/sha1_2blk_model.sv")]),
    "tb_knox_counter":         Bench("Knox_Counter"),
    "tb_knox_adder":           Bench("Knox_Adder"),
    "tb_knox_lockbox":         Bench("Knox_Lockbox"),
    "tb_knox_multi_lockbox":   Bench("Knox_MultiLockbox"),
    "tb_knox_fifo1":           Bench("Knox_Fifo1"),
    "tb_knox_fifo":            Bench("Knox_Fifo"),
}


def find_verilator():
    """flake.nix pins verilator; taking any other copy would test a different
    simulator than CI does."""
    if shutil.which("verilator"):
        return "verilator"
    sys.exit("verilator not found -- run inside 'nix develop'")


def run_one(name, bench, verilator, work):
    tb = os.path.join(ROOT, "sim", name + ".sv")
    design = os.path.join(ROOT, "build", bench.design + ".v")
    if not os.path.isfile(tb):
        return None, f"no such testbench: sim/{name}.sv"
    if not os.path.isfile(design):
        return None, f"build/{bench.design}.v is missing -- run 'make all'"

    d = os.path.join(work, name)
    os.makedirs(d, exist_ok=True)
    try:
        return build_and_run(name, bench, verilator, [tb, design] + bench.sources, d)
    finally:
        shutil.rmtree(d, ignore_errors=True)


def build_and_run(name, bench, verilator, rtl, d):
    for f in rtl:
        shutil.copy(f, d)

    # --build-jobs 2 is required: with one job verilator bundles main into
    # Vtb__ALL.a and the linker discards it.
    # -O0: compiling the C++ dominates, and every simulation runs in seconds.
    cmd = [verilator, "--binary", "--main", "--timing", "-Wno-fatal",
           "--build-jobs", "2", "--top-module", name,
           "-MAKEFLAGS", "OPT_FAST=-O0 OPT_SLOW=-O0 OPT_GLOBAL=-O0"]
    cmd += [f"+define+{k}={v}" for k, v in bench.defines.items()]
    cmd += [os.path.basename(f) for f in rtl]

    build = subprocess.run(cmd, cwd=d, capture_output=True, text=True)
    if build.returncode != 0:
        return False, "verilator failed:\n" + build.stderr.strip()[-2000:]

    sim = subprocess.run([os.path.join(".", "obj_dir", "V" + name)],
                         cwd=d, capture_output=True, text=True)
    out = sim.stdout
    bad = [l for l in out.splitlines() if l.startswith("FAIL")]
    if sim.returncode != 0 or bad:
        return False, "\n".join(bad) or out.strip()[-2000:]
    return True, next((l for l in out.splitlines() if l.startswith("PASS")), "")


def main(argv):
    args = argv[1:]
    jobs = max(1, (os.cpu_count() or 2) // 2)
    if args[:1] == ["-j"]:
        jobs, args = int(args[1]), args[2:]
    names = [os.path.basename(a).removesuffix(".sv") for a in args] or list(BENCHES)
    unknown = [n for n in names if n not in BENCHES]
    if unknown:
        sys.exit(f"unknown testbench(es): {', '.join(unknown)}\n"
                 f"known: {', '.join(BENCHES)}")

    verilator = find_verilator()
    status = 0
    with tempfile.TemporaryDirectory() as work, ThreadPoolExecutor(jobs) as pool:
        results = pool.map(lambda n: run_one(n, BENCHES[n], verilator, work), names)
        for name, (ok, detail) in zip(names, results):
            if ok:
                print(f"{name + '.sv':<28} -> {BENCHES[name].design:<28} PASS")
            else:
                status = 1
                print(f"{name + '.sv':<28} -> {BENCHES[name].design:<28} FAIL")
                for line in detail.splitlines():
                    print(f"    {line}")
    return status


if __name__ == "__main__":
    sys.exit(main(sys.argv))
