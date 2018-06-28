# Add overlays for your pull requests in this directory

An overlay is a file containing very simple logic to test whether we are currently building a specific pull request or git branch (useful so that overlays work on your own fork) and which changes some of the variables whose default can be found in [`ci-basic-overlay.sh`](/dev/ci/ci-basic-overlay.sh).

The name of your overlay file should be of the form `five_digit_PR_number-GitHub_handle-branch_name.sh`.

Example: `00669-maximedenes-ssr-merge.sh` containing

```
if [ "$CI_PULL_REQUEST" = "669" ] || [ "$CI_BRANCH" = "ssr-merge" ]; then
    mathcomp_CI_BRANCH=ssr-merge
    mathcomp_CI_GITURL=https://github.com/maximedenes/math-comp
fi
```

(`CI_PULL_REQUEST` and `CI_BRANCH` are set in [`ci-common.sh`](/dev/ci/ci-common.sh))
