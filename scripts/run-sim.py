#!/usr/bin/env python3
"""Run the testbenches in sim/ against the generated Verilog in build/.

    scripts/run-sim.py [name ...]      names default to every testbench

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
    "tb_call":      Bench("Example_CallSpike"),
    "tb_two":       Bench("Example_TwoCallSpike"),
    "tb_chain":     Bench("Example_ChainedCallSpike"),
    "tb_branch":    Bench("Example_BranchCallSpike"),
    "tb_guard":     Bench("Example_GuardCallSpike"),
    "tb_arms":      Bench("Example_ArmsSeqSpike"),
    "tb_untaken":   Bench("Example_ArmsSeqSpike"),
    "tb_xport":     Bench("Example_XPortGuardSpike"),
    "tb_mars":      Bench("Example_Mars"),

    # Against the REAL secworks/sha256 core through external/glue/.
    "tb_mars_v4": Bench(
        "Example_Mars",
        sources=REAL_IP,
        defines={"CORE_DIV": 1, "IP_LAT_SHA": 140, "IP_LAT_HMAC": 275},
    ),
    "tb_mars_pcrextend": Bench("Example_MarsSeq", sources=REAL_IP),
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
    rtl = [tb, design] + bench.sources
    for f in rtl:
        shutil.copy(f, d)

    # --build-jobs 2 is required: with one job verilator bundles main into
    # Vtb__ALL.a and the linker discards it.
    cmd = [verilator, "--binary", "--main", "--timing", "-Wno-fatal",
           "--build-jobs", "2", "--top-module", name]
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
    names = [os.path.basename(a).removesuffix(".sv") for a in argv[1:]] or list(BENCHES)
    unknown = [n for n in names if n not in BENCHES]
    if unknown:
        sys.exit(f"unknown testbench(es): {', '.join(unknown)}\n"
                 f"known: {', '.join(BENCHES)}")

    verilator = find_verilator()
    status = 0
    with tempfile.TemporaryDirectory() as work:
        for name in names:
            ok, detail = run_one(name, BENCHES[name], verilator, work)
            if ok:
                print(f"{name + '.sv':<24} -> {BENCHES[name].design:<28} PASS")
            else:
                status = 1
                print(f"{name + '.sv':<24} -> {BENCHES[name].design:<28} FAIL")
                for line in detail.splitlines():
                    print(f"    {line}")
    return status


if __name__ == "__main__":
    sys.exit(main(sys.argv))
