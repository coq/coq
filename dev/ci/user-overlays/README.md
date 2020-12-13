# Add overlays for your pull requests in this directory

When your pull request breaks an external project we test in our CI and you
have prepared a branch with the fix, you can add an "overlay" to your pull
request to test it with the adapted version of the external project.

An overlay is a file which defines where to look for the patched
version so that testing is possible.
The name of your overlay file should start with a five-digit pull request
number, followed by a dash, anything (for instance your GitHub nickname
and the branch name), then a `.sh` extension (`[0-9]{5}-[a-zA-Z0-9-_]+.sh`).

This file must contain one or more invocation of the `overlay` function:
```
overlay <project> <giturl> <ref> <prnumber> [<prbranch>]
```
Each call creates an overlay for `project` using a given `giturl` and
`ref` which is active for `prnumber` or `prbranch` (`prbranch` defaults
to `ref`).

Example of an overlay for the project `elpi` that uses the branch `noinstance`
from the fork of `SkySkimmer` and is active for pull request `13128`
```
overlay elpi https://github.com/SkySkimmer/coq-elpi noinstance 13128
```

Such a file can be created automatically using the scripts
[`create_overlays.sh`](../../dev/tools/create_overlays.sh).
See also the list of projects for which one can write an overlay in
the file [`ci-basic-overlay.sh`](../ci-basic-overlay.sh).

### Branching conventions

We suggest you use the convention of identical branch names for the
Coq branch and the CI project branch used in the overlay. For example,
if your Coq PR is coming from the branch `more_efficient_tc`, and that
breaks `ltac2`, we suggest you create a `ltac2` overlay with a branch
named `more_efficient_tc`.
