if [ "$CI_PULL_REQUEST" = "13537" ] || [ "$CI_BRANCH" = "lazy-subst-kernel" ]; then

    overlay mtac2 https://github.com/ppedrot/Mtac2 lazy-subst-kernel

fi
