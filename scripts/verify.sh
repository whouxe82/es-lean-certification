#!/usr/bin/env bash
# Rebuild only this project's proofs, preserving pinned dependency caches.
set -euo pipefail
es_round_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$es_round_dir/lean"
if [[ -x "$es_round_dir/toolchain/lean-4.19.0-linux/bin/lean" ]]; then
  export PATH="$es_round_dir/toolchain/lean-4.19.0-linux/bin:$PATH"
  if [[ -f "$es_round_dir/toolchain/proc_self_compat.so" ]]; then
    export LD_PRELOAD="$es_round_dir/toolchain/proc_self_compat.so"
  fi
  export TAR_OPTIONS=--no-same-owner
fi
mkdir -p "$es_round_dir/logs"
python3 "$es_round_dir/scripts/check_dependencies.py" > "$es_round_dir/logs/dependency-manifest-audit.json"
lake clean es_certification
lake build ES > "$es_round_dir/logs/clean-build.log" 2>&1
lake env lean Audit.lean > "$es_round_dir/logs/axioms-all.log" 2>&1
python3 "$es_round_dir/scripts/audit_sources.py" > "$es_round_dir/logs/source-audit.json"
