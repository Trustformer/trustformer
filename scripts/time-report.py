#!/usr/bin/env python3
"""CPU time of checking the proofs, once, and of synthesizing each example, RUNS times.

    nix develop --command python3 scripts/time-report.py     CORE=n pins to CPU n (default 2)

Everything runs on one core and is timed by user+sys CPU, so other load on the host
makes a run wait rather than count.  Writes build/report/time.txt and prints it."""
import glob
import os
import re
import resource
import statistics
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
RUNS = 16
COQC = ["coqc", "-q", "-R", f"{ROOT}/_build/default/coq", "Trustformer",
        "-R", f"{ROOT}/_build/default/external/ipr", "IPR"]
# A spec's sanity checks: nothing depends on them, so synthesis leaves them out.
EXAMPLE = re.compile(r"^[ \t]*Example\b.*?\b(?:Qed|Defined)\.[ \t]*\n", re.S | re.M)


def cpu(cmd, cwd=ROOT):
    """User+sys seconds of cmd and every process it starts."""
    before = resource.getrusage(resource.RUSAGE_CHILDREN)
    r = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True)
    if r.returncode:
        sys.exit(f"time-report: {' '.join(cmd)} failed\n{r.stdout}{r.stderr}")
    after = resource.getrusage(resource.RUSAGE_CHILDREN)
    return after.ru_utime + after.ru_stime - before.ru_utime - before.ru_stime


def proof_time(tmp):
    """CPU seconds per component of checking each framework file, its dependencies built."""
    files = sorted(f for f in glob.glob("coq/**/*.v", recursive=True) + glob.glob("external/ipr/*.v")
                   if not f.startswith(("coq/Examples/", "coq/Regressions/")))
    groups = subprocess.run(["bash", "-c", '. scripts/groups.sh; for f; do group "$f"; done', "_", *files],
                            stdout=subprocess.PIPE, text=True, check=True).stdout.splitlines()
    t = {}
    for f, g in zip(files, groups):
        out = os.path.join(tmp, os.path.basename(f) + "o")
        t[g] = t.get(g, 0) + cpu(COQC + [f"_build/default/{f}", "-o", out])
    return t


def prepare(spec, tmp):
    """A directory holding spec without its sanity checks, and the name it extracts to."""
    src = open(spec).read()
    stripped, n = EXAMPLE.subn("", src)
    if n != len(re.findall(r"^[ \t]*Example\b", src, re.M)):
        sys.exit(f"time-report: cannot strip every Example from {spec}")
    d = os.path.join(tmp, os.path.dirname(spec))
    os.makedirs(os.path.join(d, "build"))
    with open(os.path.join(d, "Spec.v"), "w") as f:
        f.write(stripped)
    return d, re.search(r'Extraction "(\w+)\.ml"', src)[1]


def synthesis_time(d, name):
    """CPU seconds of the three stages: Rocq to OCaml, OCaml to a plugin, cuttlec on it to Verilog."""
    b = os.path.join(d, "build")
    return (cpu(COQC + ["Spec.v"], cwd=d),
            # The command cuttlec runs on a .ml input, split off to time it apart.
            cpu(["ocamlfind", "ocamlopt", "-package", "koika.registry", "-I", ".", f"{name}.mli",
                 f"{name}.ml", "-shared", "-o", f"{name}.kpkg", "-w", "-3"], cwd=b),
            cpu(["cuttlec", f"{name}.kpkg", "-T", "verilog", "-o", "."], cwd=b))


def main():
    os.chdir(ROOT)
    subprocess.run(["dune", "build", "coq/"], check=True)
    os.sched_setaffinity(0, {int(os.environ.get("CORE", 2))})

    with tempfile.TemporaryDirectory() as tmp:
        proofs = proof_time(tmp)
        designs = [prepare(s, tmp) for s in sorted(glob.glob("coq/Examples/**/Spec.v", recursive=True))]
        runs = {name: [] for _, name in designs}
        # Round-robin, so a burst of load on the host spreads over every design.
        for _ in range(RUNS):
            for d, name in designs:
                runs[name].append(synthesis_time(d, name))

    lines = ["proof check, CPU s, once"]
    for g, t in sorted(proofs.items(), key=lambda x: -x[1]):
        lines.append(f"  {g:<32} {t:8.1f}")
    lines.append(f"  {'total':<32} {sum(proofs.values()):8.1f}")
    lines.append(f"synthesis, CPU s, median of {RUNS}: rocq, ocaml, cuttlec, total (min-max)")
    for name, rs in runs.items():
        rocq, ocaml, cuttlec = (statistics.median(s) for s in zip(*rs))
        totals = [sum(r) for r in rs]
        lines.append(f"  {name:<22} {rocq:6.2f} {ocaml:6.2f} {cuttlec:6.2f} "
                     f"{statistics.median(totals):7.2f} ({min(totals):.2f}-{max(totals):.2f})")

    os.makedirs("build/report", exist_ok=True)
    with open("build/report/time.txt", "w") as f:
        f.write("\n".join(lines) + "\n")
    print("\n".join(lines))


if __name__ == "__main__":
    main()
