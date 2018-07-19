#!/bin/sh

if [ "$CI_PULL_REQUEST" = "7941" ] || [ "$CI_BRANCH" = "jun-27-missing-record-field-error-message-quickfix" ]; then
    Equations_CI_BRANCH=overlay-question-mark-extended-for-missing-record-field
    Equations_CI_GITURL=https://github.com/bollu/Coq-Equations
fi
