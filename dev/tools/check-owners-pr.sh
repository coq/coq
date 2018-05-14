#!/usr/bin/env sh

usage() {
    { echo "usage: $0 PR [ARGS]..."
      echo "A wrapper around check-owners.sh to check owners for a PR."
      echo "Assumes upstream is the canonical Coq repository."
      echo "Assumes the PR is against master."
      echo
      echo "  PR: PR number"
      echo "  ARGS: passed through to check-owners.sh"
    } >&2
}

case "$1" in
    "--help"|"-h")
        usage
        if [ $# = 1 ]; then exit 0; else exit 1; fi;;
    "")
        usage
        exit 1;;
esac

PR="$1"
shift

# this puts both refs in the FETCH_HEAD file but git rev-parse will use the first
git fetch upstream "+refs/pull/$PR/head" master

head=$(git rev-parse FETCH_HEAD)
base=$(git merge-base upstream/master "$head")

git diff --name-only -z "$base" "$head" | xargs -0 dev/tools/check-owners.sh "$@"
