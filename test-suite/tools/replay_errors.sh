#!/bin/sh

# This script is used to replay the errors from the test suite.

# It works by running the output of _build/log after having been run a second
# time.

# First we replay make test to get only the errors since they will be rebuilt.
dune build @runtest

# Next we keep only the lines begining with '$' stripping the '$' character.
# Also we remove any binary files being called directly, i.e. starting with '/'.
# We also remove any log redirects '&>':

sed -n '/^\$/p' _build/log | sed 's/^\$ //' | grep -v '^/' \
| sed -e 's/) &>.*$/)/' | sed -e 's/ &>.*$/)/' > _build/errors

echo 'set -x' > _build/error_commands.sh
cat _build/errors >> _build/error_commands.sh

echo "Commands leading to errors:\n"
cat _build/errors

echo "Replaying errors:\n"
sh _build/error_commands.sh
