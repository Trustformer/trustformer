#!/usr/bin/env python3
"""Reprint the MARS expected values from the TCG C reference emulator.

    scripts/regen-golden.py --emulator <dir> [--vectors <file>]
    scripts/regen-golden.py --emulator <dir> --design mars_v2 [--vectors <file>]

`sim/tb_mars_v4.sv` and `sim/tb_mars_pcrextend.sv` carry those values as
localparams so that every testbench decides its own verdict and `make test`
needs nothing but verilator.  This script is how you check they are still the
reference's, or produce new ones when the Profile or the stimulus changes.  It
prints; it does not edit the testbenches.

`--design mars_v2` prints the set for `sim/tb_mars_v2.sv` instead, from the
driver `sim/golden/mars_v2_vectors.c`.

The emulator is the TCG reference emulator (github.com/TrustedComputingGroup/BIT,
commit 63a59bed, c/) plus a vector driver; it is not vendored here, so point
--emulator at wherever you keep it.
"""
import argparse
import glob
import os
import re
import shutil
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

NAMES = ["E_EXT1", "E_EXT2", "E_EXT3", "E_PCR1", "E_SIG"]

# One line per MarsV2 observation: the localparam name, the rc, the value.
V2_LINE = re.compile(r"^(E_\w+)\s+rc=(\d+)\s+\w+=([0-9a-f]+)$", re.M)


def openssl_dirs():
    """Candidate (include, lib) pairs for libcrypto.

    The -dev and runtime store paths have different hashes, so they are
    enumerated independently rather than derived from one another.  The newer
    copies are also built against a newer glibc than the dev shell carries:
    they link cleanly and then die at runtime with
    'GLIBC_ABI_DT_X86_64_PLT not found', so every pair is tried in turn.
    """
    incs = [d for d in sorted(glob.glob("/nix/store/*openssl*/include"))
            if os.path.isfile(os.path.join(d, "openssl", "evp.h"))]
    libs = [d for d in sorted(glob.glob("/nix/store/*openssl*/lib"))
            if os.path.isfile(os.path.join(d, "libcrypto.so"))]
    for lib in libs:
        for inc in incs:
            yield inc, lib


def build_emulator(emulator, driver, work, exe="stage3", cflags=()):
    """Build the emulator in `work` with this project's Profile, link `driver`
    against it, and return (path of the executable, libcrypto dir).

    A pair counts once the bare emulator runs: its constructor, _MARS_Init,
    calls into libcrypto at load time.
    """
    for src in glob.glob(os.path.join(emulator, "*.c")) + \
               glob.glob(os.path.join(emulator, "*.h")):
        shutil.copy(src, work)
    shutil.copy(driver, work)

    # The Profile this project targets: two PCRs, and production key labels.
    hw = os.path.join(work, "hw_sha2.h")
    txt = open(hw).read().replace("#define PROFILE_COUNT_PCR  4",
                                  "#define PROFILE_COUNT_PCR  2")
    open(hw, "w").write(txt)
    mars = os.path.join(work, "mars.c")
    txt = open(mars).read().replace("bool MARS_debug = true;",
                                    "bool MARS_debug = false;")
    open(mars, "w").write(txt)
    with open(os.path.join(work, "probe.c"), "w") as f:
        f.write("int main(void) { return 0; }\n")

    def sh(*cmd):
        return subprocess.run(cmd, cwd=work, capture_output=True, text=True)

    for inc, lib in openssl_dirs():
        common = ["-I" + inc, "-Wno-deprecated-declarations"]
        if sh("gcc", "-o", "hw_sha2.o", "-c", "hw_sha2.c", *common).returncode:
            continue
        if sh("gcc", "-o", "mars_sha2.o", "-include", "hw_sha2.h", "-c",
              "mars.c", *common).returncode:
            continue
        link = ["mars_sha2.o", "hw_sha2.o", "-L" + lib, "-lcrypto",
                "-Wl,-rpath," + lib]
        if sh("gcc", "-o", "probe", "probe.c", *link).returncode \
                or sh("./probe").returncode:
            continue
        cc = sh("gcc", *cflags, "-I" + inc, "-o", exe,
                os.path.basename(driver), *link)
        if cc.returncode:
            sys.exit(f"{driver} failed to build:\n{cc.stderr}")
        return os.path.join(work, exe), lib
    sys.exit("could not build or run the emulator against any openssl in the store")


def run_driver(exe):
    run = subprocess.run([exe], cwd=os.path.dirname(exe),
                         capture_output=True, text=True)
    if run.returncode or not run.stdout:
        sys.exit(f"{os.path.basename(exe)} failed:\n{run.stderr}")
    return run.stdout


def mars(args):
    vectors = args.vectors or os.path.join(args.emulator, "stage3_vectors.c")
    if not os.path.isfile(vectors):
        sys.exit(f"no vector driver at {vectors} -- pass --vectors")

    with tempfile.TemporaryDirectory() as work:
        exe, lib = build_emulator(args.emulator, vectors, work)
        out = run_driver(exe)

    digests = re.findall(r"^RegRead.*dig=([0-9a-f]{64})$", out, re.M)
    sigs = re.findall(r"^Quote.*sig=([0-9a-f]{64})$", out, re.M)
    if len(digests) < 7 or not sigs:
        sys.exit(f"unexpected emulator output:\n{out}")

    # digests: PCR0 fresh, PCR1 fresh, extends 1..3, PCR1 after its own, PCR0 again
    values = [digests[2], digests[3], digests[4], digests[5], sigs[0]]

    print(f"// built against {lib}")
    for name, v in zip(NAMES, values):
        print(f"  localparam logic [255:0] {name:<6} = 256'h{v};")

    print("\n// paste into sim/tb_mars_v4.sv and sim/tb_mars_pcrextend.sv,",
          "\n// then run: scripts/run-sim.py tb_mars_v4 tb_mars_pcrextend")
    return 0


def mars_v2(args):
    vectors = args.vectors or os.path.join(ROOT, "sim", "golden", "mars_v2_vectors.c")
    if not os.path.isfile(vectors):
        sys.exit(f"no vector driver at {vectors} -- pass --vectors")

    with tempfile.TemporaryDirectory() as work:
        exe, lib = build_emulator(args.emulator, vectors, work, "mars_v2")
        out = run_driver(exe)

    # A name the driver prints twice is one value observed twice.
    values = {}
    for name, rc, v in V2_LINE.findall(out):
        if rc != "0":
            sys.exit(f"{name}: the emulator answered rc={rc}")
        if values.setdefault(name, v) != v:
            sys.exit(f"{name}: observed as both {values[name]} and {v}")
    if not values:
        sys.exit(f"unexpected emulator output:\n{out}")

    w = max(map(len, values))
    print(f"// built against {lib}")
    for name, v in values.items():
        if len(v) == 64:
            print(f"  localparam logic [255:0] {name:<{w}} = 256'h{v};")
        else:
            print(f"  localparam bit           {name:<{w}} = 1'b{v};")

    print("\n// paste into sim/tb_mars_v2.sv,",
          "\n// then run: scripts/run-sim.py tb_mars_v2")
    return 0


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--emulator", required=True,
                    help="directory holding the TCG reference C sources")
    ap.add_argument("--design", choices=["mars", "mars_v2"], default="mars",
                    help="mars: tb_mars_v4 and tb_mars_pcrextend (default); "
                         "mars_v2: tb_mars_v2")
    ap.add_argument("--vectors", help="the vector driver (.c); defaults to "
                    "<emulator>/stage3_vectors.c for mars, "
                    "sim/golden/mars_v2_vectors.c for mars_v2")
    args = ap.parse_args()
    return mars_v2(args) if args.design == "mars_v2" else mars(args)


if __name__ == "__main__":
    sys.exit(main())
