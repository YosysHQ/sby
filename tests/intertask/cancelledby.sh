#!/bin/bash
set -e

if [[ $TASK == a ]]; then
    # different process, no cancellations
    python3 $SBY_MAIN --prefix $WORKDIR -f $SBY_FILE a
    python3 $SBY_MAIN --prefix $WORKDIR -f $SBY_FILE b
    python3 $SBY_MAIN --prefix $WORKDIR -f $SBY_FILE c
    test -e ${WORKDIR}_a/PASS -a -e ${WORKDIR}_b/FAIL -a -e ${WORKDIR}_c/FAIL
elif [[ $TASK == b ]]; then
    # same process, a cancels c cancels b
    # use statusdb so that the different taskloops from using --sequential doesn't matter
    python3 $SBY_MAIN --prefix $WORKDIR -f $SBY_FILE --statusreset || true
    python3 $SBY_MAIN --prefix $WORKDIR -f $SBY_FILE a c b --sequential --statuscancels
    test -e ${WORKDIR}_a/PASS -a -e ${WORKDIR}_b/CANCELLED -a -e ${WORKDIR}_c/CANCELLED
else
    # different process, b cancels a, c completes before a
    python3 $SBY_MAIN --prefix $WORKDIR -f $SBY_FILE --statusreset || true
    python3 $SBY_MAIN --prefix $WORKDIR -f $SBY_FILE b --statuscancels
    python3 $SBY_MAIN --prefix $WORKDIR -f $SBY_FILE c --statuscancels
    python3 $SBY_MAIN --prefix $WORKDIR -f $SBY_FILE a --statuscancels
    echo test -e ${WORKDIR}_a/CANCELLED -a -e ${WORKDIR}_b/FAIL -a -e ${WORKDIR}_c/FAIL
fi
