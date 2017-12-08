if [ "$TRAVIS_PULL_REQUEST" = "6158" ] || [ "$TRAVIS_BRANCH" = "master+some-fix-ltac-printing+refined-printers" ]; then
    ltac2_CI_BRANCH=master+fix-pr6158-ltac-value-printer
    ltac2_CI_GITURL=https://github.com/herbelin/ltac2.git
fi
