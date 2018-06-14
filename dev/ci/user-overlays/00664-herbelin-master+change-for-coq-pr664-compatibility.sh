 if [ "$CI_PULL_REQUEST" = "664" ] || [ "$CI_BRANCH" = "trunk+fix-5500-too-weak-test-return-clause" ]; then
    fiat_parsers_CI_BRANCH=master+change-for-coq-pr664-compatibility
    fiat_parsers_CI_GITURL=https://github.com/herbelin/fiat
fi
