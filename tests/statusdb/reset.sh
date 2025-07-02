#!/bin/bash
set -e

# run task
python3 $SBY_MAIN -f $SBY_FILE $TASK
# task has 3 properties
python3 $SBY_MAIN -f $SBY_FILE --status | wc -l | grep -q '3'
# resetting task should work
python3 $SBY_MAIN -f $SBY_FILE --statusreset
# clean database should have no properties
python3 $SBY_MAIN -f $SBY_FILE --status | wc -l | grep -q '0'
