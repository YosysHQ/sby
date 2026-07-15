#!/usr/bin/env bash
set -eu

sby="sby"
script="example.sby"
task="task1"

while getopts :s: opt; do
    case "$opt" in
        s)
            sby=$OPTARG
            ;;
        *)
            echo "Usage: $0 [-s SBY command]\n" >&2
            exit 1
            ;;
    esac
done

# log our commands and output
PS4="$ "
exec > >(tee example.log) 2>&1
set -x

$sby --dumptasks $script
$sby --dumptags $script
$sby --dumptags $script $task
$sby --dumpcfg $script $task
