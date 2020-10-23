# Add overlays for your pull requests in this directory

When your pull request breaks an external project we test in our CI and you
have prepared a branch with the fix, you can add an "overlay" to your pull
request to test it with the adapted version of the external project.

An overlay is a file which defines where to look for the patched
version so that testing is possible. This is done by calling the
`overlay` command for each project with the project name (as used in
the variables in [`ci-basic-overlay.sh`](../ci-basic-overlay.sh)), the
location of your fork and the branch containing the patch on your
fork.

Moreover, the file contains very simple logic to test the pull request number
or branch name and apply it only in this case.

The name of your overlay file should start with a five-digit pull request
number, followed by a dash, anything (for instance your GitHub nickname
and the branch name), then a `.sh` extension (`[0-9]{5}-[a-zA-Z0-9-_]+.sh`).

Example: `13128-SkySkimmer-noinstance.sh` containing

```
if [ "$CI_PULL_REQUEST" = "13128" ] || [ "$CI_BRANCH" = "noinstance" ]; then

    overlay elpi https://github.com/SkySkimmer/coq-elpi noinstance

fi
```

(`CI_PULL_REQUEST` and `CI_BRANCH` are set in [`ci-common.sh`](../ci-common.sh))

### Branching conventions

We suggest you use the convention of identical branch names for the
Coq branch and the CI project branch used in the overlay. For example,
if your Coq PR is coming from the branch `more_efficient_tc`, and that
breaks `ltac2`, we suggest you create a `ltac2` overlay with a branch
named `more_efficient_tc`.
