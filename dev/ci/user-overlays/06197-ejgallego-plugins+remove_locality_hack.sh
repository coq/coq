if [ "$TRAVIS_PULL_REQUEST" = "6197" ] || [ "$TRAVIS_BRANCH" = "plugins+remove_locality_hack" ]; then
    ltac2_CI_BRANCH=localityfixyou
    ltac2_CI_GITURL=https://github.com/ejgallego/ltac2.git
fi
