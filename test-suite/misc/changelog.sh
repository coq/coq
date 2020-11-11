#!/usr/bin/env bash

config=../../config/coq_config.py
# config=
# if [ -f "$../../config/coq_config.py" ]
# then
#   config=../../config/coq_config.py
# else
#   echo "Could not find coq_config.py"
#   exit 1
# fi

if grep -q -F "is_a_released_version = False" "$config"; then
    echo "This is not a released version: nothing to test."
    exit 0
fi

for d in ../doc/changelog/*; do
  if [ -d "$d" ]; then
    files=("$d"/*.rst)
    if [ "${#files[@]}" != 1 ]; then
      echo "Fatal: unreleased changelog entries remain in ${d#../}/"
      echo "Include them in doc/sphinx/changes.rst and remove them from doc/changelog/"
      exit 1
    fi
  fi
done
