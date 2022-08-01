#!/bin/bash

python3 $SBY_MAIN -f fifo.sby && python3 $SBY_MAIN -f fifo.sby nofullskip

if [[ $? -ne 2 ]] ; then
    echo "Unexpected result"
    exit 1
fi
