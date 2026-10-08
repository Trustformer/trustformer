#!/usr/bin/env python3
"""Check that every headline theorem is proved, and proved without axioms.

    scripts/check-theorems.py            check them all
    scripts/check-theorems.py --list     just print the list

A headline theorem is one a reader has to be told about: it states a guarantee
the project makes, rather than a step on the way to one.  Everything below is
machine-checked by Rocq, so what needs human attention is whether this LIST is
the right one -- edit it here.

The check is `Print Assumptions`, which reports every axiom a proof rests on.
A theorem left `Admitted` shows up the same way, so that is caught too.  Needs
`dune build coq/` to have run.
"""
import argparse
import re
import subprocess
import sys
import tempfile
import os

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

# (group, why it is headline, [(module, theorem), ...])
HEADLINE = [
    ("the pipeline is correct",
     "the generated circuit computes what the specification says",
     [("Trustformer.Theorems.Synthesis", "synthesis_correct"),
      ("Trustformer.Theorems.Synthesis", "initial_state_matches"),
      ("Trustformer.Theorems.SchedulerSimulation", "variable_scheduler_correct"),
      ("Trustformer.Theorems.SchedulerSimulation", "start_rel_after_done")]),

    ("no secret leaks by value",
     "what the attacker can see never depends on a secret",
     [("Trustformer.Theorems.Confidentiality", "seq_confidential"),
      ("Trustformer.Theorems.Confidentiality", "no_direct_secret_flow")]),

    ("no secret leaks by timing",
     "the project's reason to exist: an output observer learns nothing a run "
     "keeps to itself, and the cycle it learns it on is public",
     [("Trustformer.Theorems.IPR", "emulator_correct")]),

    ("the declassification rules are sound",
     "each rule widens what may be published; unsound means a real leak",
     [("Trustformer.Declassification.Negation", "neg_packet_sound"),
      ("Trustformer.Declassification.PhiBranch", "phibranch_packet_sound"),
      ("Trustformer.Declassification.PhiConst", "phiconst_packet_sound"),
      ("Trustformer.Declassification.Widening", "widen_packet_sound"),
      ("Trustformer.Declassification.Xor", "xor_packet_sound")]),
]

CLOSED = "Closed under the global context"


def flat():
    return [(mod, thm) for _, _, pairs in HEADLINE for mod, thm in pairs]


def build_probe(pairs):
    mods = sorted({mod for mod, _ in pairs})
    lines = [f"Require {m}." for m in mods]
    # Fully qualified, so no two modules can shadow each other's names.
    lines += [f"Print Assumptions {mod}.{thm}." for mod, thm in pairs]
    return "\n".join(lines) + "\n"


def split_results(out):
    """One verdict per Print Assumptions, in order.

    Output is either the CLOSED line or an 'Axioms:'/'Assumptions:' block that
    runs until the next verdict.
    """
    results, current = [], None
    for line in out.splitlines():
        if line.strip() == CLOSED:
            if current is not None:
                results.append(current)
            results.append([])          # [] == axiom-free
            current = None
        elif re.match(r"^(Axioms|Assumptions):", line.strip()):
            if current is not None:
                results.append(current)
            current = []
        elif current is not None and line.strip():
            current.append(line.strip())
    if current is not None:
        results.append(current)
    return results


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--list", action="store_true", help="print the list and stop")
    args = ap.parse_args()

    if args.list:
        for group, why, pairs in HEADLINE:
            print(f"\n{group}  -- {why}")
            for mod, thm in pairs:
                print(f"    {mod}.{thm}")
        print(f"\n{len(flat())} headline theorems")
        return 0

    lib = os.path.join(ROOT, "_build/default/coq")
    if not os.path.isdir(lib):
        sys.exit("_build/default/coq is missing -- run 'dune build coq/' first")

    pairs = flat()
    with tempfile.TemporaryDirectory() as work:
        probe = os.path.join(work, "CheckTheorems.v")
        with open(probe, "w") as fh:
            fh.write(build_probe(pairs))
        run = subprocess.run(["coqc", "-R", lib, "Trustformer", probe],
                             capture_output=True, text=True, cwd=work)

    if run.returncode != 0:
        # A renamed or deleted theorem lands here, and coqc names it.
        print("coqc failed -- a theorem below is misnamed, moved, or missing:\n")
        print(run.stderr.strip()[-3000:])
        return 1

    results = split_results(run.stdout)
    if len(results) != len(pairs):
        print(f"expected {len(pairs)} verdicts, parsed {len(results)}; raw output:\n")
        print(run.stdout)
        return 1

    bad = 0
    i = 0
    for group, _, group_pairs in HEADLINE:
        print(f"\n{group}")
        for mod, thm in group_pairs:
            axioms = results[i]
            i += 1
            if axioms:
                bad += 1
                print(f"  AXIOMS  {thm}")
                for a in axioms:
                    print(f"            {a}")
            else:
                print(f"  ok      {thm}")

    print()
    if bad:
        print(f"FAILED: {bad} of {len(pairs)} headline theorems rest on axioms")
        return 1
    print(f"PASS: all {len(pairs)} headline theorems are proved, axiom-free")
    return 0


if __name__ == "__main__":
    sys.exit(main())
