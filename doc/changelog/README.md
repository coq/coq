# Unreleased changelog #

## When to add an entry? ##

All new features, user-visible changes to features, user-visible or
otherwise important infrastructure changes, and important bug fixes
should get a changelog entry.

Compatibility-breaking changes should always get a changelog entry,
which should explain what compatibility breakage is to expect.

Pull requests changing the ML API in significant ways should add an
entry in [`dev/doc/changes.md`](../../dev/doc/changes.md).

## How to add an entry? ##

Run `./dev/tools/make-changelog.sh`: it will ask you for your PR
number, and to choose among the predefined categories, and the
predefined types of changes.  Afterward, fill in the automatically
generated entry with a short description of your change (which should
describe any compatibility issues in particular).  You may also add a
reference to the relevant fixed issue, and credit reviewers,
co-authors, and anyone who helped advance the PR.

The format for changelog entries is the same as in the reference
manual.  In particular, you may reference the documentation you just
added with `:ref:`, `:tacn:`, `:cmd:`, `:opt:`, `:token:`, etc.  See
the [documentation of the Sphinx format](../sphinx/README.rst) of the
manual for details.

Here is a summary of the structure of a changelog entry:

``` rst
- **Added / Changed / Deprecated / Fixed / Removed:**
  Description of the changes, with possible link to
  :ref:`relevant-section` of the updated documentation
  (`#PRNUM <https://github.com/coq/coq/pull/PRNUM>`_,
  [fixes `#ISSUE1 <https://github.com/coq/coq/issues/ISSUE1>`_
  [ and `#ISSUE2 <https://github.com/coq/coq/issues/ISSUE2>`_],]
  by Full Name[, with help / review of Full Name]).
```

The first line indicates the type of change.  Available types come
from the [Keep a Changelog
1.0.0](https://keepachangelog.com/en/1.0.0/) specification.  We
exclude the "Security" type for now because of the absence of a
process for handling critical bugs (proof of False) as security
vulnerabilities.
