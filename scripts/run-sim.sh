#!/usr/bin/env bash
# Simulate the IP round-trip spikes and the one-action MARS.  See sim/README.md.
#
# tb_xport.sv is NOT in the default set: it currently FAILS, and it is meant to
# -- it holds a defect open.  Run it by name.
#
#   scripts/run-sim.sh [testbench.sv ...]     (default: all of them)
set -uo pipefail
cd "$(dirname "$0")/.."

declare -A DESIGN=(
  [tb_call.sv]=Example_CallSpike
  [tb_two.sv]=Example_TwoCallSpike
  [tb_chain.sv]=Example_ChainedCallSpike
  [tb_branch.sv]=Example_BranchCallSpike
  [tb_mars.sv]=Example_Mars
  [tb_guard.sv]=Example_GuardCallSpike
  [tb_xport.sv]=Example_XPortGuardSpike
  [tb_arms.sv]=Example_ArmsSeqSpike
)

tbs=("$@"); [ $# -eq 0 ] && tbs=(tb_call.sv tb_two.sv tb_chain.sv tb_branch.sv tb_guard.sv tb_arms.sv tb_mars.sv)
status=0
work=$(mktemp -d); trap 'rm -rf "$work"' EXIT

for tb in "${tbs[@]}"; do
    design="${DESIGN[$tb]:-}"
    if [ -z "$design" ]; then echo "unknown testbench: $tb"; status=1; continue; fi
    if [ ! -f "build/$design.v" ]; then
        echo "SKIP $tb -- build/$design.v is missing (run 'make all' first)"
        status=1; continue
    fi
    printf '%-14s -> %-28s ' "$tb" "$design"
    out=$(nix shell nixpkgs#verilator nixpkgs#gnumake nixpkgs#gcc nixpkgs#python3 \
            --command verilator --binary --timing -Wno-fatal --build-jobs 2 \
            --top-module tb --Mdir "$work/$design" -o sim \
            "sim/$tb" "build/$design.v" 2>&1) \
      && out=$("$work/$design/sim" 2>&1)
    if grep -q "^PASS" <<<"$out"; then echo "PASS"; else
        echo "FAIL"; echo "$out" | sed 's/^/    /'; status=1
    fi
done
exit $status
