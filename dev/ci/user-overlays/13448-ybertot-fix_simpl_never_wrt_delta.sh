if [ "$CI_PULL_REQUEST" = "13448" ] || [ "$CI_BRANCH" = "fix_simpl_never_wrt_delta" ]; then

    overlay hott https://github.com/ybertot/HoTT respect_simpl_never_flags
    overlay stdpp https://gitlab.inria.fr/bertot/stdpp respect_simpl_never_flags

fi
