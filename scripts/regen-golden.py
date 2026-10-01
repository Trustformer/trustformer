#!/usr/bin/env python3
"""Reprint the MARS expected values from the TCG C reference emulator.

    scripts/regen-golden.py --emulator <dir> [--vectors <file>]

`sim/tb_mars_v4.sv` and `sim/tb_mars_pcrextend.sv` carry those values as
localparams so that every testbench decides its own verdict and `make test`
needs nothing but verilator.  This script is how you check they are still the
reference's, or produce new ones when the Profile or the stimulus changes.  It
prints; it does not edit the testbenches.

The emulator is the TCG reference C code plus the stage-3 vector driver; it is
not vendored here, so point --emulator at wherever you keep it.
"""
import argparse
import glob
import os
import re
import shutil
import subprocess
import sys
import tempfile

NAMES = ["E_EXT1", "E_EXT2", "E_EXT3", "E_PCR1", "E_SIG"]


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


def build_and_run(emulator, vectors, work):
    for src in glob.glob(os.path.join(emulator, "*.c")) + \
               glob.glob(os.path.join(emulator, "*.h")):
        shutil.copy(src, work)
    shutil.copy(vectors, work)

    # The Profile this project targets: two PCRs, and production key labels.
    hw = os.path.join(work, "hw_sha2.h")
    txt = open(hw).read().replace("#define PROFILE_COUNT_PCR  4",
                                  "#define PROFILE_COUNT_PCR  2")
    open(hw, "w").write(txt)
    mars = os.path.join(work, "mars.c")
    txt = open(mars).read().replace("bool MARS_debug = true;",
                                    "bool MARS_debug = false;")
    open(mars, "w").write(txt)

    def sh(*cmd):
        return subprocess.run(cmd, cwd=work, capture_output=True, text=True)

    for inc, lib in openssl_dirs():
        common = ["-I" + inc, "-Wno-deprecated-declarations"]
        if sh("gcc", "-o", "hw_sha2.o", "-c", "hw_sha2.c", *common).returncode:
            continue
        if sh("gcc", "-o", "mars_sha2.o", "-include", "hw_sha2.h", "-c",
              "mars.c", *common).returncode:
            continue
        if sh("gcc", "-o", "stage3", os.path.basename(vectors), "mars_sha2.o",
              "hw_sha2.o", "-L" + lib, "-lcrypto",
              "-Wl,-rpath," + lib).returncode:
            continue
        run = sh("./stage3")
        if run.returncode == 0 and run.stdout:
            return run.stdout, lib
    sys.exit("could not build or run the emulator against any openssl in the store")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--emulator", required=True,
                    help="directory holding the TCG reference C sources")
    ap.add_argument("--vectors", help="the stage-3 vector driver (.c)")
    args = ap.parse_args()

    vectors = args.vectors or os.path.join(args.emulator, "stage3_vectors.c")
    if not os.path.isfile(vectors):
        sys.exit(f"no vector driver at {vectors} -- pass --vectors")

    with tempfile.TemporaryDirectory() as work:
        out, lib = build_and_run(args.emulator, vectors, work)

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


if __name__ == "__main__":
    sys.exit(main())
