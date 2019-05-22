#!/bin/sh

if grep -q -F "is_a_released_version = False" ../config/coq_config.py; then
    echo "This is not a released version: nothing to test."
    exit 0
fi

for d in ../doc/changelog/*; do
  if [ -d "$d" ]; then
    if [ "$(ls $d/*.rst | wc -l)" != "1" ]; then
      echo "Fatal: unreleased changelog entries remain in ${d#../}/"
      echo "Include them in doc/sphinx/changes.rst and remove them from doc/changelog/"
      exit 1
    fi
  fi
done
