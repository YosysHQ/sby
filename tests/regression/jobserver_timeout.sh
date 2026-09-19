#!/bin/bash
set -e

# Hold the only slot so induction is still waiting when the timeout fires.
env -u MAKEFLAGS timeout 10s python3 "$SBY_MAIN" -j 1 \
    --smtbmc "bash -c 'sleep 60' --" -f "$SBY_FILE"
grep -q '^TIMEOUT ' "$WORKDIR/status"
