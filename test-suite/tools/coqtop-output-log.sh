#!/bin/sh

# Strip the coqtop messages from the output file
cat $1 \
| grep -v "Welcome to Coq" \
| grep -v "\[Loading ML file" \
| grep -v "Skipping rcfile loading" \
| grep -v "^<W>"
