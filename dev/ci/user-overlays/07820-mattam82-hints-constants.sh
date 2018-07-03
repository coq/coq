_OVERLAY_BRANCH=hints-variables-overlay

if [ "$CI_PULL_REQUEST" = "7820" ] || [ "$CI_BRANCH" = "_OVERLAY_BRANCH" ]; then

    Equations_CI_BRANCH="$_OVERLAY_BRANCH"
fi
