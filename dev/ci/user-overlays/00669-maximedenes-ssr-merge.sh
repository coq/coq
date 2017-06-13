if [ "$TRAVIS_PULL_REQUEST" = "669" ] || [ "$TRAVIS_BRANCH" = "ssr-merge" ]; then
    mathcomp_CI_BRANCH=ssr-merge
    mathcomp_CI_GITURL=https://github.com/maximedenes/math-comp.git
fi
