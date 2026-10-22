#!/usr/bin/env bash
# Lines of Rocq per component (tab:proof-cost in the paper), as counted by coqwc.
#
#   nix develop --command scripts/loc-report.sh
#
# Writes build/report/loc.txt and prints it.
set -euo pipefail
cd "$(dirname "$0")/.."
. scripts/groups.sh

declare -A loc
for f in $(find coq external/ipr -name '*.v' | sort); do
  g=$(group "$f")
  # Code lines: coqwc's spec and proof columns, which leave out comments and blanks.
  loc[$g]=$(( ${loc[$g]:-0} + $(coqwc "$f" | awk 'NR == 2 { print $1 + $2 }') ))
done

mkdir -p build/report
for g in "Ingot Syntax and Semantics" "Correctness and IPR definition" "Vendored IPR" \
         "Synthesis" "Proofs" "Rule Library" "Examples" "Regressions"; do
  printf '%-32s %6d\n' "$g" "${loc[$g]}"
done | tee build/report/loc.txt
