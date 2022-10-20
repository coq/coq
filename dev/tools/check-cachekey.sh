#!/bin/sh

hash=$(md5sum dev/ci/docker/jammy_coq/Dockerfile | head -c 10)
key=$(grep CACHEKEY: .gitlab-ci.yml)
keyhash=${key%\"}
keyhash=${keyhash##*-}
if ! [ "$hash" = "$keyhash" ]; then
    >&2 echo "Bad CACHEKEY: expected '$hash' but got '$keyhash'"
    exit 1
fi
