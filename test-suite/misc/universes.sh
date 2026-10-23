#!/bin/sh
# Sort universes for the whole core library
EXPECTED_UNIVERSES=1 # Prop is not counted.
# If ssr is univ poly we don't see the high universes involved in ssr_congr_arrow for example.
$coqc -R misc/universes Universes misc/universes/all_stdlib 2>&1
$coqc -R misc/universes Universes misc/universes/universes 2>&1
mv universes.txt misc/universes
N=$(awk '{print $3}' misc/universes/universes.txt | sort -u | grep "Type" | wc -l)
printf "Found %s/%s universes\n" "$N" "$EXPECTED_UNIVERSES"
if [ "$N" -eq $EXPECTED_UNIVERSES ]; then exit 0; else exit 1; fi
