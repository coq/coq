#!/bin/sh

before=$1
after=$2

# https://unix.stackexchange.com/questions/418429/find-intersection-of-lines-in-two-files
awk 'BEGIN{while( (getline k < "'"$before"'")>0 ){a[k]}} $0 in a' "$after" > removed_artifacts.txt

xargs -a removed_artifacts.txt rm

d=_build_ci
if [ -d $d ]; then
  find $d -type d -empty -delete
fi
