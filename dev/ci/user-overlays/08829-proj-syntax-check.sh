if [ "$CI_PULL_REQUEST" = "8829" ] || [ "$CI_BRANCH" = "proj-syntax-check" ]; then
    lambdaRust_CI_REF=proj-syntax-check
    lambdaRust_CI_GITURL=https://github.com/SkySkimmer/lambda-rust
    lambdaRust_CI_ARCHIVEURL=$lambdaRust_CI_GITURL/archive
fi
