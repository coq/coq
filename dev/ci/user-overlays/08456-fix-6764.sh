#!/bin/sh

if [ "$CI_PULL_REQUEST" = "8456" ] || [ "$CI_BRANCH" = "fix-6764" ]; then
    Elpi_CI_REF=overlay/8456
fi
