#!/bin/bash
set -e
python3 $SBY_MAIN -f $SBY_FILE $TASK
python3 ${SBY_FILE%.sby}.py $WORKDIR
