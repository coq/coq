if [ "$TRAVIS_PULL_REQUEST" = "6133" ] || [ "$TRAVIS_BRANCH" = "master+ssreflect-notation-cast-fix" ]; then
    mathcomp_CI_BRANCH=master+cast-notation-rule
    mathcomp_CI_GITURL=https://github.com/herbelin/math-comp.git
fi
