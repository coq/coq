#!/usr/bin/env bash

# determine if a file has whitespace checking enabled in .gitattributes

git check-attr whitespace -- "$1" | grep -q -v 'unspecified$'
