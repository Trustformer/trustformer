#!/usr/bin/env python3
"""Fail the build when a generated Verilog net has two *different* drivers.

    scripts/check-drivers.py build/*.v

cuttlec emits one continuous assignment per call site of a non-internal
("wire interface") external function, all onto the same port -- so a function
called from N places produces N drivers on <fn>_arg.  While every call site
passes the same argument the duplicates are harmless: Verilog net resolution
yields the intended value.  The moment two call sites pass different arguments
the generated Verilog silently shorts two drivers together, and downstream
tools resolve it by aliasing the two calls into one -- wrong, with no
diagnostic from cuttlec.

Exit 0 = safe; duplicate-but-identical drivers are reported as info.
Exit 1 = a net has two different drivers.  Do not ship the file.
"""
import re
import sys
from collections import defaultdict

ASSIGN = re.compile(r"^\s*assign\s+(?P<lhs>[^=]+)=(?P<rhs>.*)$")


def drivers(path):
    """net -> list of the distinct right-hand sides assigned to it."""
    seen = defaultdict(list)
    with open(path) as fh:
        for line in fh:
            m = ASSIGN.match(line)
            if not m:
                continue
            lhs = m.group("lhs").strip()
            rhs = m.group("rhs").strip()
            seen[lhs].append(rhs)
    return seen


def main(paths):
    conflicts = 0
    for path in paths:
        for net, rhss in sorted(drivers(path).items()):
            distinct = set(rhss)
            if len(distinct) > 1:
                conflicts += 1
                print(f"CONFLICT {path}: {net} has {len(distinct)} distinct "
                      f"drivers ({len(rhss)} assignments)")
            elif len(rhss) > 1:
                print(f"redundant {path}: {net} driven {len(rhss)} times, "
                      f"all identical")

    if conflicts:
        print(f"check-drivers: FAILED -- {conflicts} net(s) have conflicting "
              f"drivers", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    if len(sys.argv) < 2:
        sys.exit("usage: check-drivers.py <generated.v> ...")
    sys.exit(main(sys.argv[1:]))
