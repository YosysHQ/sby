#!/bin/bash
set -e
python3 $SBY_MAIN -f $SBY_FILE $TASK

STATUS_CSV=${WORKDIR}/status.csv
python3 $SBY_MAIN -f $SBY_FILE $TASK --statuscsv --latest | tee $STATUS_CSV

if [[ $TASK =~ "_cover" ]]; then
    wc -l $STATUS_CSV | grep -q '6'
    grep "COVER" $STATUS_CSV | wc -l | grep -q '5'
elif [[ $TASK =~ "_fail" ]]; then
    wc -l $STATUS_CSV | grep -q '6'
    grep "ASSERT" $STATUS_CSV | wc -l | grep -q '5'
    grep "FAIL" $STATUS_CSV | wc -l | grep -q '1'
else
    wc -l $STATUS_CSV | grep -q '5'
    grep "ASSERT" $STATUS_CSV | wc -l | grep -q '4'
fi

if [[ $TASK == "smt_cover" ]]; then
    grep "PASS" $STATUS_CSV | wc -l | grep -q '4'
fi
