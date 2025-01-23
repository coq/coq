#!/bin/sh

d=_build_ci
if [ -d $d ]; then
  find $d -type f -o -type l | sort
fi
