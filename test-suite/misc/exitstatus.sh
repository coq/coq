#!/bin/sh
$coqc misc/exitstatus/illtyped.v
P=$?
printf "On ill-typed input, coqc returned %s.\n" "$P"
if [ $P = 1 ]; then exit 0; else exit 1; fi
