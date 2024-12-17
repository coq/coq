#!/bin/sh

for d in _install_ci saved_build_ci; do
  if [ -d $d ]; then
    find $d -type f -o -type l | sort
  fi
done
