#!/usr/bin/env bash
set -euo pipefail

repo_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-2}"
cd "$repo_dir/proofs"

# Local integration can name an explicit override file. With no override,
# Lake uses the submission's pinned dependencies.
run_lake() {
  if [[ -n "${LAKE_PACKAGES:-}" ]]; then
    lake "--packages=$LAKE_PACKAGES" "$@"
  else
    lake "$@"
  fi
}

run_lake build
for test_file in ../tests/*.lean; do
  run_lake env lean "$test_file"
done
