if [ "$CI_PULL_REQUEST" = "8554" ] || [ "$CI_BRANCH" = "master+fix8553-change-under-binders" ]; then

    ltac2_CI_BRANCH=master+fix-pr8554-change-takes-env
    ltac2_CI_REF=master+fix-pr8554-change-takes-env
    ltac2_CI_GITURL=https://github.com/herbelin/ltac2

    Equations_CI_BRANCH=master+fix-pr8554-change-takes-env
    Equations_CI_REF=master+fix-pr8554-change-takes-env
    Equations_CI_GITURL=https://github.com/herbelin/Coq-Equations

fi
