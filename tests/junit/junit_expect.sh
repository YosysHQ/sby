#!/bin/bash
set -e
! python3 $SBY_MAIN -f $SBY_FILE $TASK
grep '<failure type="EXPECT" message="Task returned status PASS. Expected values were: FAIL TIMEOUT" />' $WORKDIR/$WORKDIR.xml
