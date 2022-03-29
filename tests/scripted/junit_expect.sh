#!/bin/bash

# this is expected to return 1 so don't use 'set -e'
python3 ../../sbysrc/sby.py -f junit_expect.sby
grep '<failure type="EXPECT" message="Task returned status PASS. Expected values were: FAIL TIMEOUT" />' junit_expect/junit_expect.xml
