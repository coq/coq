#!/usr/bin/env bash

# Add user overlays here. You can use some logic to detect if you are
# in your travis branch and conditionally enable the overlay.

# Some useful Travis variables:
# (https://docs.travis-ci.com/user/environment-variables/#Default-Environment-Variables)
#
# - TRAVIS_BRANCH: For builds not triggered by a pull request this is
#   the name of the branch currently being built; whereas for builds
#   triggered by a pull request this is the name of the branch
#   targeted by the pull request (in many cases this will be master).
#
# - TRAVIS_COMMIT: The commit that the current build is testing.
#
# - TRAVIS_PULL_REQUEST: The pull request number if the current job is
#   a pull request, “false” if it’s not a pull request.
#
# - TRAVIS_PULL_REQUEST_BRANCH: If the current job is a pull request,
#   the name of the branch from which the PR originated. "" if the
#   current job is a push build.

echo $TRAVIS_PULL_REQUEST_BRANCH
echo $TRAVIS_PULL_REQUEST
echo $TRAVIS_BRANCH
echo $TRAVIS_COMMIT

if [ $TRAVIS_PULL_REQUEST == "669" ] || [ $TRAVIS_BRANCH == "ssr-merge" ]; then
    mathcomp_CI_BRANCH=ssr-merge
    mathcomp_CI_GITURL=https://github.com/maximedenes/math-comp.git
fi

echo "DEBUG: ci-user-overlay.sh 0"
if [ $TRAVIS_PULL_REQUEST = "707" ] || [ $TRAVIS_BRANCH == "trunk__API__coq_makefile" ]; then
    echo "DEBUG: ci-user-overlay.sh 1"
    bedrock_src_CI_BRANCH=trunk__API
    bedrock_src_CI_GITURL=https://github.com/matejkosik/bedrock.git
    bedrock_facade_CI_BRANCH=trunk__API
    bedrock_facade_CI_GITURL=https://github.com/matejkosik/bedrock.git
    fiat_parsers_CI_BRANCH=trunk__API
    fiat_parsers_CI_GITURL=https://github.com/matejkosik/fiat.git
fi

if [ $TRAVIS_PULL_REQUEST == "498" ] || [ $TRAVIS_BRANCH == "outsource-bignums" ]; then
    math_classes_CI_BRANCH=external-bignums
    math_classes_CI_GITURL=https://github.com/letouzey/math-classes.git
    Corn_CI_BRANCH=external-bignums
    Corn_CI_GITURL=https://github.com/letouzey/corn.git
fi
