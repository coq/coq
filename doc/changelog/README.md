# Unreleased changelog #

## When to add an entry? ##

All new features, user-visible changes to features, user-visible or
otherwise important infrastructure changes, and important bug fixes
should get a changelog entry.

Compatibility-breaking changes should always get a changelog entry,
which should explain what compatibility-breakage is to expect.

Pull requests changing the ML API in significant ways should add an
entry in [`dev/doc/changes.md`](../../dev/doc/changes.md).

## How to add an entry? ##

You should create a file in one of the sub-directories. The name of
the file should be `NNNNN-identifier.rst` where `NNNNN` is the number
of the pull request on five digits and `identifier` is whatever you
want.

This file should use the same format as the reference manual (as it
will be copied in there). You may reference the documentation you just
added with `:ref:`, `:tacn:`, `:cmd:`, `:opt:`, `:token:`, etc. See
the [documentation of the Sphinx format](../sphinx/README.rst) of the
manual for details.

The entry should be written using the following structure:

``` rst
- Description of the changes, with possible link to
  :ref:`relevant-section` of the updated documentation
  (`#PRNUM <https://github.com/coq/coq/pull/PRNUM>`_,
  [fixes `#ISSUE1 <https://github.com/coq/coq/issues/ISSUE1>`_
  [ and `#ISSUE2 <https://github.com/coq/coq/issues/ISSUE2>`_],]
  by Full Name[, with help / review of Full Name]).
```

The description should be kept rather short and the only additional
required meta-information are the link to the pull request and the
full name of the author.
