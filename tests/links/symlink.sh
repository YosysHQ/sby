#!/bin/bash
set -e
if [[ $TASK == link ]]; then
    flags="--setup --link"
else
    flags="--setup"
fi
python3 $SBY_MAIN -f $SBY_FILE $TASK $flags
python3 ${SBY_FILE%.sby}.py $WORKDIR $TASK
