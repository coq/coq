#!/usr/bin/env bash

# A script to check prettyness over the repository.

# lint-commits.sh seeks to prevent the worsening of already present
# problems, such as tab indentation in ml files. lint-repository.sh
# also seeks to prevent the (re-)introduction of solved problems, such
# as newlines at the end of .v files.

CODE=0

# if COQ_CI_COLOR is set (from the environment) keep it intact (even when it's the empty string)'
if ! [ "${COQ_CI_COLOR+1}" ]; then
  # NB: in CI TERM is unset in the environment
  # when TERM is unset, bash sets it to "dumb" as a bash variable (not exported?)
  if { [ -t 1 ] && ! [ "$TERM" = dumb ]; } || [ "$CI" ]
  then export COQ_CI_COLOR=1
  else export COQ_CI_COLOR=
  fi
fi

if [[ $(git log -n 1 --pretty='format:%s') == "[CI merge]"* ]]; then
    # The second parent of bot merges is from the PR, the first is
    # current master
    head=$(git rev-parse HEAD^2)
else
    head=$(git rev-parse HEAD)
fi

# We assume that all non-bot merge commits are from the main branch
# For Coq it is extremely rare for this assumption to be broken
read -r base < <(git log -n 1 --merges --pretty='format:%H' "$head")

dev/lint-commits.sh "$base" "$head" || CODE=1

# Check that the files with 'whitespace' gitattribute end in a newline.
# xargs exit status is 123 if any file failed the test
echo Checking end of file newlines
find . "(" -path ./.git -prune ")" -o -type f -print0 |
    xargs -0 dev/tools/check-eof-newline.sh || CODE=1

echo Checking overlays
dev/tools/check-overlays.sh || CODE=1

echo Checking CACHEKEY
dev/tools/check-cachekey.sh || CODE=1

# Check that doc/tools/docgram/fullGrammar is up-to-date
echo Checking grammar files
make SHOW='@true ""' doc_gram_verify || CODE=1

exit $CODE
