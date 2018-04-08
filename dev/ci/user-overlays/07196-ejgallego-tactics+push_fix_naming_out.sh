if [ "$CI_PULL_REQUEST" = "7196" ] || [ "$CI_BRANCH" = "tactics+push_fix_naming_out" ] || [ "$CI_BRANCH" = "pr-7196" ]; then

    # Needed overlays: https://gitlab.com/coq/coq/pipelines/21244550
    #
    # equations
    # ltac2

    # The below developments should instead use a backwards compatible fix.
    #
    # color
    # iris-lambda-rust
    # math-classes
    # formal-topology

    ltac2_CI_BRANCH=tactics+push_fix_naming_out
    ltac2_CI_GITURL=https://github.com/ejgallego/ltac2

    Equations_CI_BRANCH=tactics+push_fix_naming_out
    Equations_CI_GITURL=https://github.com/ejgallego/Coq-Equations

fi
