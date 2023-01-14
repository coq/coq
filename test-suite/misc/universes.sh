#!/bin/sh
# Sort universes for the whole standard library
EXPECTED_UNIVERSES=4 # Prop is not counted
coqc -R universes Universes universes/all_stdlib.v 2>&1
coqc -R universes Universes universes/universes.v 2>&1
mv universes.txt universes
N=$(awk '{print $3}' universes/universes.txt | sort -u | wc -l)
printf "Found %s/%s universes\n" "$N" "$EXPECTED_UNIVERSES"
if [ "$N" -eq $EXPECTED_UNIVERSES ]; then exit 0; else exit 1; fi
