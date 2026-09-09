#!/usr/bin/env bash
# Fail the build when a generated Verilog net has two *different* drivers.
#
# cuttlec emits one continuous assignment per call site of a non-internal
# ("wire interface") external function, all onto the same port -- so an
# external function called from N places produces N drivers on <fn>_arg.
# While every call site passes the same argument the duplicates are harmless
# (Verilog net resolution yields the intended value).  The moment two call
# sites pass different arguments the generated Verilog silently shorts two
# drivers together, and downstream tools resolve it by aliasing the two calls
# into one -- wrong, with no diagnostic from cuttlec.
#
# See agents/verilog-issues/ for the full analysis and a minimal repro.
#
#   scripts/check-drivers.sh build/*.v
#
# Exit 0 = safe.  Duplicate-but-identical drivers are reported as info.
# Exit 1 = a net has two different drivers.  Do not ship the file.
set -uo pipefail

status=0
for f in "$@"; do
    out=$(awk -v file="$f" '
        /^[[:space:]]*assign[[:space:]]/ {
            line = $0
            sub(/^[[:space:]]*assign[[:space:]]+/, "", line)
            eq = index(line, "=")
            if (eq == 0) next
            lhs = substr(line, 1, eq - 1)
            rhs = substr(line, eq + 1)
            gsub(/^[[:space:]]+|[[:space:]]+$/, "", lhs)
            gsub(/^[[:space:]]+|[[:space:]]+$/, "", rhs)
            n[lhs]++
            if (!((lhs SUBSEP rhs) in seen)) { seen[lhs SUBSEP rhs] = 1; distinct[lhs]++ }
        }
        END {
            for (lhs in n) {
                if (distinct[lhs] > 1)
                    printf "CONFLICT %s: %s has %d distinct drivers (%d assignments)\n", file, lhs, distinct[lhs], n[lhs]
                else if (n[lhs] > 1)
                    printf "redundant %s: %s driven %d times, all identical\n", file, lhs, n[lhs]
            }
        }' "$f" | sort)
    [ -n "$out" ] && printf '%s\n' "$out"
    printf '%s\n' "$out" | grep -q '^CONFLICT' && status=1
done

if [ "$status" -ne 0 ]; then
    echo "check-drivers: FAILED -- a net has conflicting drivers; see agents/verilog-issues/" >&2
fi
exit $status
