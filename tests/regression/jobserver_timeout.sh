#!/bin/bash
set -e

# Ignore make's jobserver and use one slot: the sleeping fake solver holds it
# while induction waits. SBY must exit after its 1s timeout; the outer 10s
# deadline fails the test if canceled job leases keep it alive.
env -u MAKEFLAGS timeout 10s python3 "$SBY_MAIN" -j 1 \
    --smtbmc "bash -c 'sleep 60' --" -f "$SBY_FILE"
grep -q '^TIMEOUT ' "$WORKDIR/status"
