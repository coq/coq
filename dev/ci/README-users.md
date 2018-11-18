Information for external library / Coq plugin authors
-----------------------------------------------------

You are encouraged to consider submitting your development for addition to
Coq's CI. This means that:

- Any time that a proposed change is breaking your development, Coq developers
  will send you patches to adapt it or, at the very least, will work with you
  to see how to adapt it.

On the condition that:

- At the time of the submission, your development works with Coq's
  `master` branch.

- Your development is publicly available in a git repository and we can easily
  send patches to you (e.g. through pull / merge requests).

- You react in a timely manner to discuss / integrate those patches.

- You do not push, to the branches that we test, commits that haven't been
  first tested to compile with the corresponding branch(es) of Coq.

  For that, we recommend setting a CI system for you development, see
  [supported CI images for Coq](#supported-ci-images-for-coq) below.

- You maintain a reasonable build time for your development, or you provide
  a "lite" target that we can use.

In case you forget to comply with these last three conditions, we would reach
out to you and give you a 30-day grace period during which your development
would be moved into our "allow failure" category. At the end of the grace
period, in the absence of progress, the development would be removed from our
CI.

### Add your development by submitting a pull request

Add a new `ci-mydev.sh` script to [`dev/ci`](.); set the corresponding
variables in [`ci-basic-overlay.sh`](ci-basic-overlay.sh); add the
corresponding target to [`Makefile.ci`](../../Makefile.ci) and a new job to
[`.gitlab-ci.yml`](../../.gitlab-ci.yml) so that this new target is run.
Have a look at [#7656](https://github.com/coq/coq/pull/7656/files) for an
example. **Do not hesitate to submit an incomplete pull request if you need
help to finish it.**

You may also be interested in having your development tested in our
performance benchmark. Currently this is done by providing an OPAM package
in https://github.com/coq/opam-coq-archive and opening an issue at
https://github.com/coq/coq-bench/issues.

### Recommended branching policy.

It is sometimes the case that you will need to maintain a branch of
your development for particular Coq versions. This is in fact very
likely if your development includes a Coq ML plugin.

We thus recommend a branching convention that mirrors Coq's branching
policy. Then, you would have a `master` branch that follows Coq's
`master`, a `v8.8` branch that works with Coq's `v8.8` branch and so
on.

This convention will be supported by tools in the future to make some
developer commands work more seamlessly.

### Supported CI images for Coq

The Coq developers and contributors do provide official Docker and Nix
images for testing against Coq master. Using these images is highly
recommended:

- For Docker, see: https://github.com/coq-community/docker-coq
- For Nix, see the setup at
  https://github.com/coq-community/manifesto/wiki/Continuous-Integration-with-Nix
