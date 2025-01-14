# Add overlays for your pull requests in this directory

_Overlays_ let you test pull requests that break the base version of
external projects by applying PRs of the external project during CI
testing (1 PR per broken external project).  Once Rocq CI's tests of the
external projects pass, the Rocq PR can be merged, then the assignee must
ask the external projects to merge their PRs (for example by commenting
in the external PRs).  External projects are then expected to merge their
PRs promptly.

An overlay file specifies the external PRs that should be applied during CI.
A single file can cover multiple external projects.  Create your
overlay file in the `dev/ci/user-overlays` directory.
The name of the overlay file should start with a five-digit pull request
number, followed by a dash, anything (by convention, your GitHub nickname
and the branch name), then an `.sh` extension (`[0-9]{5}-[a-zA-Z0-9-_]+.sh`).

The file must contain a call to the `overlay` function for each
affected external project:
```
overlay <project> <giturl> <ref> <prnumber> [<prbranch>]
```
Each call creates an overlay for `project` using a given `giturl` and
`ref` which is active for `prnumber` or `prbranch` (`prbranch` defaults
to `ref`).

For example, an overlay for the project `elpi` that uses the branch `noinstance`
from the fork of `SkySkimmer` and is active for pull request `13128`:
```
overlay elpi https://github.com/SkySkimmer/coq-elpi noinstance 13128
```

The github URL and base branch name for each external project are listed in
[`ci-basic-overlay.sh`](../ci-basic-overlay.sh).  For example, the entry for
`elpi` is
```
project elpi "https://github.com/LPCIC/coq-elpi" "master"
```
But substitute the name of your fork into the URL, e.g. `SkySkimmer/coq-elpi`
rather than `LPCIC/coq-elpi`.  Use `#` to mark any comments.

If the branch name in the external project differs from the Rocq branch name,
include the external branch name as `[prbranch]` to apply it when you run
the test suite locally, e.g. `make ci-elpi`.

Overlay files can be created automatically using the script
[`create_overlays.sh`](../../tools/create_overlays.sh).

### Branching conventions

We suggest you use the convention of identical branch names for the
Rocq branch and the CI project branch used in the overlay. For example,
if your Rocq PR is in your branch `more_efficient_tc` and
breaks `ltac2`, we suggest you create an `ltac2` overlay with a branch
named `more_efficient_tc`.

### Typical workflow

- Observe that your changes breaks some external projects in CI
- Compile your PR.
- For each broken project, run `make <job name>`, e.g. `make ci-elpi`,
  which checks out, builds and runs the project in the
  `_build_ci/<job name>` directory.
- Make necessary changes, then rerun the script to verify they work.
- From the `<job name>` subdirectory, commit your changes to a new
  branch, based on the base branch name listed in `ci-basic-overlay.sh`,
  for example `master` for elpi.
- If necessary, fork the external project from the project's github page.
  (Only needs to be done once, ever.)
- Push to the external project and create a new PR.  Make sure you pick
  the correct base branch in the github GUI for the comparison
  (e.g. `master` for elpi).
- Create the overlay file, add to your Rocq PR, push the updated version and
  verify that the external projects now pass.
- When your PR is merged, the assignee notifies the maintainers of the
  external project to merge the changes you submitted.  This should happen
  promptly; the external project's CI will fail until the change is merged.
- Beer.
