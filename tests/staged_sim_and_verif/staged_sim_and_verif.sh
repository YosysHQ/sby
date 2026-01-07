#!/bin/bash
set -euo pipefail

FLOW_FILE="skip_staged_flow.sby"

run_task() {
    python3 "$SBY_MAIN" -f "$FLOW_FILE" "$1"
}

run_task stage_1_init
run_task stage_1_cover
run_task stage_2_init
run_task stage_2a_cover
run_task stage_2b_assert
