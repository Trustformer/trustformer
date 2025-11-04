#!/usr/bin/env bash

SCRIPT_DIR="$(dirname "$(readlink -f "${BASH_SOURCE[0]}")")"
VSCOQ_BIN="vscoqtop"

CMD="$VSCOQ_BIN $@"

cd "$SCRIPT_DIR/.."
nix develop --override-input koika ../koika -c $CMD
