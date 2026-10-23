#!/usr/bin/env bash
set -euo pipefail

project_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$project_dir"

local_lean="$project_dir/.toolchains/lean-4.35.0-darwin_aarch64/bin"
if [[ -x "$local_lean/lake" ]]; then
  export PATH="$local_lean:$PATH"
fi

lake build
lake env lean Hypernets/Audit.lean
lake env lean Hypernets/Graph/Audit.lean
