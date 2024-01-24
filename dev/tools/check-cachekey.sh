#!/bin/sh

RED="\033[31m"
RESET="\033[0m"

function redprint
{
  if [ -t 1 ] && ! [ "$TERM" = dumb ]; then
    printf "$RED%s$RESET\n" "$1"
  else
    printf '%s\n' "$1"
  fi
}

base_hash=$(md5sum dev/ci/docker/old_ubuntu_lts/Dockerfile | head -c 10)
base_key=$(grep BASE_CACHEKEY: .gitlab-ci.yml)
base_keyhash=${base_key%\"}
base_keyhash=${base_keyhash##*-}

if ! [ "$base_hash" = "$base_keyhash" ]; then
    >&2 redprint "Bad BASE_CACHEKEY: expected '$base_hash' but got '$base_keyhash'"
    exit 1
fi

edge_hash=$(md5sum dev/ci/docker/edge_ubuntu/Dockerfile | head -c 10)
edge_key=$(grep EDGE_CACHEKEY: .gitlab-ci.yml)
edge_keyhash=${edge_key%\"}
edge_keyhash=${edge_keyhash##*-}

if ! [ "$edge_hash" = "$edge_keyhash" ]; then
    >&2 redprint "Bad EDGE_CACHEKEY: expected '$edge_hash' but got '$edge_keyhash'"
    exit 1
fi
