#!/usr/bin/env bash

echo "Require $(find ../../../theories ../../../plugins -type f -name "*.v" | \
        sed 's/^.*\/theories\///' | sed 's/^.*\/plugins\///' | sed 's/\.v$//' | sed 's/\//./g') ."
