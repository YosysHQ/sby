#!/bin/bash
set -euo pipefail

FLOW_FILE="skip_staged_flow.sby"

run_task() {
    python3 "$SBY_MAIN" -f "$FLOW_FILE" "$1"
}

run_task stage_1
run_task stage_2
run_task stage_3_init
run_task stage_3a_cover
run_task stage_3b_assert
