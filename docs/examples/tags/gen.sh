#!/usr/bin/env bash
set -eu

sby="sby"
script="example"
task="task1"

while getopts :S:s:t: opt; do
    case "$opt" in
        S)
            sby=$OPTARG
            ;;
        s)
            script=$OPTARG
            ;;
        t)
            task=$OPTARG
            ;;
        *)
            echo "Usage: $0 [-s SBY command] [-s .sby file] [-t task]\n" >&2
            exit 1
            ;;
    esac
done


# log our commands and output
echo "$0 $@" > ${script}.log
PS4="$ "
exec > >(tee -a ${script}.log) 2>&1
set -x

$sby --dumptasks ${script}.sby
$sby --dumptags ${script}.sby
$sby --dumptags ${script}.sby $task
$sby --dumpcfg ${script}.sby $task
