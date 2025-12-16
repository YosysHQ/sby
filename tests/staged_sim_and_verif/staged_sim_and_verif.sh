#!/bin/bash
set -euo pipefail

FLOW_FILE="skip_staged_flow.sby"

# Clean previous runs so we always exercise the full staged flow.
rm -rf skip_staged_flow_stage_1_init skip_staged_flow_stage_1_fv skip_staged_flow_stage_2_init skip_staged_flow_stage_2_fv

run_task() {
    python3 "$SBY_MAIN" -f "$FLOW_FILE" "$1"
}

run_task stage_1_init
run_task stage_1_fv
run_task stage_2_init
run_task stage_2_fv
