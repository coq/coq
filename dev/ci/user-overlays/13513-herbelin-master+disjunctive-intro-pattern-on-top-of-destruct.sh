if [ "$CI_PULL_REQUEST" = "13513" ] || [ "$CI_BRANCH" = "master+disjunctive-intro-pattern-on-top-of-destruct" ]; then

    overlay flocq git@gitlab.inria.fr:herbelin/flocq.git master+adapt-coq-pr13513-disjunctive-intro-pattern-is-destruct
    overlay hott https://github.com/herbelin/HoTT master+adapt-coq-pr13513-disjunctive-intro-pattern-is-destruct
    overlay unimath https://github.com/herbelin/UniMath master+adapt-coq-pr13513-disjunctive-intro-pattern-is-destruct

fi
