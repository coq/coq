#!/usr/bin/env bash

set -e

export PATH=$BIN:$PATH

${coqc#"$BIN"} misc/aux7704.v
