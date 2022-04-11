#!/bin/bash
set -e
python3 $SBY_MAIN -f $SBY_FILE $TASK
python3 validate_junit.py $WORKDIR/$WORKDIR.xml
