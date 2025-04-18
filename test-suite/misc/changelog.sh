#!/usr/bin/env bash

config=../tools/configure/configure.ml
if ! [ -e "$config" ]; then
    echo "Could not find configure.ml"
    exit 1
fi

if grep -q -F "is_a_released_version = true" "$config"; then
  :
elif grep -q -F "is_a_released_version = false" "$config"; then
    echo "This is not a released version: nothing to test."
    exit 0
else
  echo "Could not find is_a_released_version setting"
  exit 1
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
