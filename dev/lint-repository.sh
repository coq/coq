#!/usr/bin/env bash

# A script to check prettyness over the repository.

# lint-commits.sh seeks to prevent the worsening of already present
# problems, such as tab indentation in ml files. lint-repository.sh
# seeks to prevent the (re-)introduction of solved problems, such as
# newlines at the end of .v files.

CODE=0

if [ -n "${TRAVIS_PULL_REQUEST}" ] && [ "${TRAVIS_PULL_REQUEST}" != false ];
then
    # skip PRs from before the linter existed
    if [ -z "$(git ls-tree --name-only "${TRAVIS_PULL_REQUEST_SHA}" dev/lint-commits.sh)" ];
    then
        1>&2 echo "Linting skipped: pull request older than the linter."
        exit 0
    fi

    # Some problems are too widespread to fix in one commit, but we
    # can still check that they don't worsen.
    CUR_HEAD=${TRAVIS_COMMIT_RANGE%%...*}
    PR_HEAD=${TRAVIS_COMMIT_RANGE##*...}
    MERGE_BASE=$(git merge-base "$CUR_HEAD" "$PR_HEAD")
    dev/lint-commits.sh "$MERGE_BASE" "$PR_HEAD" || CODE=1
fi

# Check that the files with 'whitespace' gitattribute end in a newline.
# xargs exit status is 123 if any file failed the test
find . "(" -path ./.git -prune ")" -o -type f -print0 |
    xargs -0 dev/tools/check-eof-newline.sh || CODE=1

dev/tools/check-overlays.sh || CODE=1

exit $CODE
