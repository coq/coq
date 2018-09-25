#!/bin/sh

if [ "$CI_PULL_REQUEST" = "8552" ] || [ "$CI_BRANCH" = "elpi-1.1" ]; then
    Elpi_CI_REF=coq-master-elpi-1.1
fi
