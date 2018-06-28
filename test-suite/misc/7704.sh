#!/usr/bin/env bash

set -e

export PATH=$BIN:$PATH

${coqtop#"$BIN"} -compile misc/aux7704.v
