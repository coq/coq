_OVERLAY_BRANCH=omega-lia

if [ "$CI_PULL_REQUEST" = "7878" ] || [ "$CI_BRANCH" = "_OVERLAY_BRANCH" ]; then

    CompCert_CI_BRANCH="$_OVERLAY_BRANCH"
    CompCert_CI_GITURL=https://github.com/maximedenes/CompCert.git

    bignums_CI_BRANCH="$_OVERLAY_BRANCH"
    bignums_CI_GITURL=https://github.com/maximedenes/bignums.git

fi
