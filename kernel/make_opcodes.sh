#!/usr/bin/env bash

script_dir="$(dirname "$0")"
tr -d "\r" < "${1}" | sed -n -e '/^enum/p' -e 's/,//g' -e '/^  /p' | awk -f "$script_dir"/make-opcodes > "${2}"
