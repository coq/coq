#!/usr/bin/env bash

# determine if a file has whitespace checking enabled in .gitattributes

git ls-files --error-unmatch "$1" >/dev/null 2>&1 &&
git check-attr whitespace -- "$1" | grep -q -v -e 'unset$' -e 'unspecified$'
