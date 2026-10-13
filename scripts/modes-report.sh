#!/usr/bin/env bash
# The three synthesis modes compared statically (tab:modes in the paper).  For every
# action of the suite in coq/Examples/Criticalities/Bounds.v, at cost limit 4: the
# latency bounds when no branch, the secret-dependent branches (taint) or every branch
# is constant time, whether the latency depends on secret data, and a witness per leak.
#
#   nix develop --command scripts/modes-report.sh
#
# Writes build/report/modes.csv and build/report/witnesses.txt and prints both.
set -euo pipefail
cd "$(dirname "$0")/.."

dune build coq/Examples/Criticalities/Report.vo
out=build/report
mkdir -p "$out"
install -m 644 _build/default/build/report/modes_report.ml _build/default/build/report/modes_report.mli "$out/"
cat > "$out/main.ml" <<'EOF'
let () =
  let write f s = let oc = open_out f in output_string oc s; close_out oc in
  write "modes.csv" Modes_report.report;
  write "witnesses.txt" Modes_report.witnesses
EOF
(cd "$out" && ocamlfind ocamlopt -w -a modes_report.mli modes_report.ml main.ml -o modes_report && ./modes_report)

cat "$out/modes.csv"
echo
cat "$out/witnesses.txt"
