# The component a Rocq file counts toward, for loc-report.sh and time-report.py.
shopt -s extglob

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
    *) echo "groups: no group for $1" >&2; exit 1 ;;
  esac
}
