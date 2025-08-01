#!/bin/bash
set -e
if [[ $TASK == link ]]; then
    flags="--setup --link"
else
    flags="--setup"
fi
python3 $SBY_MAIN -f $SBY_FILE $TASK $flags

test -e ${WORKDIR}/src/here/dir -a -e ${WORKDIR}/src/a/b/c.v
