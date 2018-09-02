#!/usr/bin/env bash

# allow running this script from any directory by basing things on where the script lives
SCRIPT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null && pwd )"

# we assume that the script lives in test-suite/tools/update-compat/,
# and that update-compat.py lives in dev/tools/
cd "${SCRIPT_DIR}/../../.."
dev/tools/update-compat.py --assert-unchanged --cur-version=8.9 || exit $?
