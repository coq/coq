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
    sed -i.bak -e "s/$BRANCH_VAR:=$BRANCH/$BRANCH_VAR:=$HASH/" $OVERLAYS
  fi
}

# Execute the script to set the overlay variables
. $OVERLAYS

# Find all variables declared in the base overlay of the form *_CI_GITURL
for REPO_VAR in $(compgen -A variable | grep _CI_GITURL)
do
  DEV=${REPO_VAR%_CI_GITURL}
  process_development $DEV
done
