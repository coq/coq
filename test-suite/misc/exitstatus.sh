#!/bin/sh
$coqtop -load-vernac-source misc/exitstatus/illtyped.v
N=$?
$coqc misc/exitstatus/illtyped.v
P=$?
printf "On ill-typed input, coqtop returned %s.\n" "$N"
printf "On ill-typed input, coqc returned %s.\n" "$P"
if [ $N = 1 ] && [ $P = 1 ]; then exit 0; else exit 1; fi
