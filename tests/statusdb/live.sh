#!/bin/bash
set -e
python3 $SBY_MAIN -f $SBY_FILE $TASK
python3 $SBY_MAIN $SBY_FILE --status | grep -q 'test.fail FAIL'
python3 $SBY_MAIN $SBY_FILE --status | grep -q 'test.pass PASS'
