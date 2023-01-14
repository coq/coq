#!/bin/sh

# This is the script to process the output-modulo-time tests, adapted from the
# original test-suite makefile.

# Strip the timing data from the output file
cat $1 \
| grep -v "Welcome to Coq" \
| grep -v "\[Loading ML file" \
| grep -v "Skipping rcfile loading" \
| grep -v "^<W>" \
| sed -e 's/\s*[-+0-9]*\.[0-9][0-9]*\s*//g' \
      -e 's/\s*0\.\s*//g' \
      -e 's/\s*[-+]nan\s*//g' \
      -e 's/\s*[-+]inf\s*//g' \
      -e 's/^[^a-zA-Z]*//' \
| sort
