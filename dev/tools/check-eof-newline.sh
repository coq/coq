#!/usr/bin/env bash

if [ -z "$(tail -c 1 "$1")" ]
then
    exit 0
else
    echo "No newline at end of file $1!"
    exit 1
fi
