#!/bin/bash
set -e

if [[ $TASK == bmc ]]; then
    python3 $SBY_MAIN --prefix $WORKDIR -f $SBY_FILE prove bmc
else
    python3 $SBY_MAIN --prefix $WORKDIR -f $SBY_FILE --statusreset || true
    python3 $SBY_MAIN --prefix $WORKDIR -f $SBY_FILE bmc --statuscancels & bmc_pid="$!"
    # make sure we don't leave the background task running
    trap 'kill "$bmc_pid" 2>/dev/null || true' EXIT
    python3 $SBY_MAIN --prefix $WORKDIR -f $SBY_FILE prove
    sleep 10
    test -e ${WORKDIR}_bmc/CANCELLED
fi
