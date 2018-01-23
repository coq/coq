#!/usr/bin/env bash

(sudo apt-get update "$@" 2>&1 || echo 'E: update failed') | tee /tmp/apt.err
! grep -q '^\(E:\|W: Failed to fetch\)' /tmp/apt.err || exit $?
