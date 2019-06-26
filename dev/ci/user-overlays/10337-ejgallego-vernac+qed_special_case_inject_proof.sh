if [ "$CI_PULL_REQUEST" = "10337" ] || [ "$CI_BRANCH" = "vernac+qed_special_case_inject_proof" ]; then

    paramcoq_CI_REF=vernac+qed_special_case_inject_proof
    paramcoq_CI_GITURL=https://github.com/ejgallego/paramcoq

    equations_CI_REF=vernac+qed_special_case_inject_proof
    equations_CI_GITURL=https://github.com/ejgallego/Coq-Equations

fi
