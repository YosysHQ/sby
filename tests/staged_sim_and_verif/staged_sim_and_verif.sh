#!/bin/bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
cd "$SCRIPT_DIR"

FLOW_FILE="staged_sim_and_verif.sby"

# Clean previous runs so we always exercise the full staged flow.
rm -rf staged_sim_and_verif_stage_1_init staged_sim_and_verif_stage_1_fv staged_sim_and_verif_stage_2_init staged_sim_and_verif_stage_2_fv

run_task() {
    python3 "$SBY_MAIN" -f "$FLOW_FILE" "$1"
}

run_task stage_1_init
run_task stage_1_fv
run_task stage_2_init
run_task stage_2_fv
