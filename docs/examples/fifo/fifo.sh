#!/bin/bash

python3 $SBY_MAIN -f fifo.sby basic cover noverific

if [[ $? -ne 0 ]] ; then
    exit 1
fi

python3 $SBY_MAIN -f fifo.sby nofullskip

if [[ $? -ne 2 ]] ; then
    exit 1
fi
