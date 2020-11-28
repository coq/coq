#!/usr/bin/env bash

hash=$(md5sum dev/ci/docker/bionic_coq/Dockerfile | head -c 10)
key=$(grep CACHEKEY: .gitlab-ci.yml)
keyhash=${key%\"}
keyhash=${keyhash##*-}
if ! [ "$hash" = "$keyhash" ]; then
    echo "Bad CACHEKEY: expected '$hash' but got '$keyhash'"
    exit 1
fi
