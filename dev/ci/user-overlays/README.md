# Add overlays for your pull requests in this directory

When your pull request breaks an external development we test in our CI, you
must prepare a patch (or ask someone to prepare a patch) to fix this development.
Backward compatible patches are to be preferred, especially on libraries (it is
harder to make backward compatible patches for plugins).

Once you have a patched version, you can add an overlay to your pull request:
this is a file which defines where to look for the patched version so that
testing is possible. It changes the value of some variables from
[`ci-basic-overlay.sh`](/dev/ci/ci-basic-overlay.sh) (generally both the
`_CI_BRANCH` and the `_CI_GITURL` variables of a given development at once).

The file contains very simple logic to test the pull request number or branch
name and apply it only in this case.

The name of your overlay file should start with a five-digit pull request
number, followed by a dash, anything (for instance your GitHub nickname
and the branch name), then a `.sh` extension (`[0-9]{5}-[a-zA-Z0-9-_]+.sh`).

Example: `00669-maximedenes-ssr-merge.sh` containing

```
#!/bin/sh

if [ "$CI_PULL_REQUEST" = "669" ] || [ "$CI_BRANCH" = "ssr-merge" ]; then
    mathcomp_CI_BRANCH=ssr-merge
    mathcomp_CI_GITURL=https://github.com/maximedenes/math-comp.git
fi
```

(`CI_PULL_REQUEST` and `CI_BRANCH` are set in [`ci-common.sh`](/dev/ci/ci-common.sh))
