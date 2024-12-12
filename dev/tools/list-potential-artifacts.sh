#!/bin/sh

for d in _build_ci stdlib/_build; do
  if [ -d $d ]; then
    find $d -type f -o -type l | sort
  fi
done
