#!/usr/bin/env bash

# This is the script to process the complexity tests, adapted from the original
# test-suite makefile.

ERROR="Error in complexity.sh:"

# First we check for the BOGOMIPS value which is passed via an environment
# variable. If it is not present we fail, since this script should not have run
# otherwise.
bogomips=$BOGOMIPS
if [[ -z "$BOGOMIPS" ]]; then
  >&2 echo "$ERROR BOGOMIPS not found, script should not have been run."
  exit 1
fi

# Next we check our first argument which should be the .v file. This contains
# the expected time which we will later parse.
vfile=$1
if [[ -z "$vfile" ]]; then
  >&2 echo "$ERROR .v file not provided."
  exit 1
fi

# Afterwards we check our log file. This will contain the outputted timing data
# during compilation.
logfile=$2
if [[ -z "$logfile" ]]; then
  >&2 echo "$ERROR .log file not provided."
  exit 1
fi

# result
res=$(cat $logfile | sed -n -e "s/Finished .*transaction in .*(\([0-9]*\.[0-9]*\)u.*)/\1/p" | head -1 | sed "s/\r//g")

if [[ -z "$res" ]]; then
  >&2 echo "$ERROR couldn't find a time measure."
  exit 1
fi

# express effective time in centiseconds
resorig="$res"
res=$(echo "$res"00 | sed -n -e "s/\([0-9]*\)\.\([0-9][0-9]\).*/\1\2/p")

if [[ -z "$res" ]]; then
  >&2 echo "$ERROR invalid time measure: $resorig"
fi

# find expected time in centiseconds
exp=$(cat $vfile | sed -n -e "s/(\*.*Expected time < \([0-9]\).\([0-9][0-9]\)s.*\*)/\1\2/p")

# compute corrected effective time, rounded up

rescorrected=$(expr \( $res \* $bogomips + 6120 - 1 \) / 6120)

# We now check that the result is less than the expected time upto a scaling
# factor.

result=$(expr \( $res \* $bogomips \))
expected=$(expr \( $exp \* 6120 \))

ok=$(expr $result "<" $expected)

if [ "$ok" -eq "1" ]; then
  # echo "Success! Complexity test: $vfile"
  exit 0
fi

>&2 echo "*** Failure! Complexity test: $vfile"

>&2 echo "result = $result"
>&2 echo "expected = $expected"
>&2 echo "bogomips = $bogomips"

exit 1
