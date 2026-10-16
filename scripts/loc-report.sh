#!/usr/bin/env bash
# Lines of Rocq per component (tab:proof-cost in the paper), as counted by coqwc.
#
#   nix develop --command scripts/loc-report.sh
#
# Writes build/report/loc.txt and prints it.
set -euo pipefail
shopt -s extglob
cd "$(dirname "$0")/.."

group() {
  case $1 in
    */Internal/*) echo "Proofs" ;;
    coq/@(Syntax|Semantics|Contract|Utils).v) echo "Ingot Syntax and Semantics" ;;
    coq/Theorems/*) echo "Correctness and IPR definition" ;;
    external/ipr/*) echo "Vendored IPR" ;;
    coq/@(DFG|Macros).v|coq/Backend/*|coq/Scheduler/*) echo "Synthesis" ;;
    coq/Declassification/*) echo "Rule Library" ;;
    coq/Examples/*) echo "Examples" ;;
    coq/Regressions/*) echo "Regressions" ;;
    *) echo "loc-report: no group for $1" >&2; exit 1 ;;
  esac
}

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
