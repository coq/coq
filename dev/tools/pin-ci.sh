#!/usr/bin/env bash

# Use this script to pin the commit used by the developments tracked by the CI

OVERLAYS="./dev/ci/ci-basic-overlay.sh"

process_development() {
  local DEV=$1
  local REPO_VAR="${DEV}_CI_GITURL"
  local REPO=${!REPO_VAR}
  local BRANCH_VAR="${DEV}_CI_REF"
  local BRANCH=${!BRANCH_VAR}
  if [[ -z "$BRANCH" ]]
  then
    echo "$DEV has no branch set, skipping"
    return 0
  fi
  if [[ $BRANCH =~ ^[a-f0-9]{40}$ ]]
  then
    echo "$DEV is already set to hash $BRANCH, skipping"
    return 0
  fi
  echo "Resolving $DEV as $BRANCH from $REPO"
  local HASH=$(git ls-remote --heads $REPO $BRANCH | cut -f 1)
  if [[ -z "$HASH" ]]
  then
    echo "Could not resolve reference $BRANCH for $DEV (something went wrong), skipping"
    return 0
  fi
  read -p "Expand $DEV from $BRANCH to $HASH? [y/N] " -n 1 -r
  echo
  if [[ $REPLY =~ ^[Yy]$ ]]; then
    # use -i.bak to be compatible with MacOS; see, e.g., https://stackoverflow.com/a/7573438/377022
    sed -i.bak -E "s|project +$DEV +.*|project $DEV '$REPO' '$HASH'|" $OVERLAYS
  fi
}

# Execute the script to set the overlay variables
. $OVERLAYS

for project in ${projects[@]}
do
  process_development $project
done
