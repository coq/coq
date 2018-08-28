# Add overlays for your pull requests in this directory

When your pull request breaks an external project we test in our CI and you
have prepared a branch with the fix, you can add an "overlay" to your pull
request to test it with the adapted version of the external project.

An overlay is a file which defines where to look for the patched version so that
testing is possible. It redefines some variables from
[`ci-basic-overlay.sh`](../ci-basic-overlay.sh):
give the name of your branch / commit using a `_CI_REF` variable and the
location of your fork using a `_CI_GITURL` variable.
The `_CI_GITURL` variable should be the URL of the repository without a
trailing `.git`.
If the fork is not on the same platform (e.g. GitHub instead of GitLab), it is
necessary to redefine the `_CI_ARCHIVEURL` variable as well.

Moreover, the file contains very simple logic to test the pull request number
or branch name and apply it only in this case.

The name of your overlay file should start with a five-digit pull request
number, followed by a dash, anything (for instance your GitHub nickname
and the branch name), then a `.sh` extension (`[0-9]{5}-[a-zA-Z0-9-_]+.sh`).

Example: `00669-maximedenes-ssr-merge.sh` containing

```
#!/bin/sh

if [ "$CI_PULL_REQUEST" = "669" ] || [ "$CI_BRANCH" = "ssr-merge" ]; then
    mathcomp_CI_REF=ssr-merge
    mathcomp_CI_GITURL=https://github.com/maximedenes/math-comp
fi
```

(`CI_PULL_REQUEST` and `CI_BRANCH` are set in [`ci-common.sh`](../ci-common.sh))
