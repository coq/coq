#!/usr/bin/env bash

set -e

conf_err="Error: Lazy profiler was disabled when Rocq was compiled (configure time)."

if ! msg=$($coqc -profile-lazy 2>&1); then
  if [ "$msg" = "$conf_err" ]; then
    echo "Skipping test: lazy profiler disabled at configure time."
    exit 0
  else
    >&2 echo "Unknown rocq error:"
    >&2 cat misc/lazyprof/conftest
    exit 1
  fi
fi

$coqc misc/lazyprof/LazyProf.v >misc/lazyprof/LazyProf.real 2>&1

diff -u --strip-trailing-cr misc/lazyprof/LazyProf.expected misc/lazyprof/LazyProf.real
