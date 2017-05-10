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

if [ $TRAVIS_PULL_REQUEST == "590" ] || [ $TRAVIS_BRANCH == "trunk+algebraic-matchingvar" ]; then
    mathcomp_CI_BRANCH=trunk+pr590-patvar
    mathcomp_CI_GITURL=https://github.com/herbelin/math-comp.git
fi

if [ $TRAVIS_PULL_REQUEST == "623" ] || [ $TRAVIS_BRANCH == "remove-sigma" ]; then
    mathcomp_CI_BRANCH=remove-sigma
    mathcomp_CI_GITURL=https://github.com/maximedenes/math-comp.git
    fiat_parsers_CI_BRANCH=remove-sigma
    fiat_parsers_CI_GITURL=https://github.com/maximedenes/fiat.git
    bedrock_src_CI_BRANCH=remove-sigma
    bedrock_src_CI_GITURL=https://github.com/maximedenes/bedrock.git
    bedrock_facade_CI_BRANCH=remove-sigma
    bedrock_facade_CI_GITURL=https://github.com/maximedenes/bedrock.git
fi

