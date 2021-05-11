- **Changed:**
  `coq_makefile` now uses the `coqnative` binary to generate
  native compilation files. Project files also understand directly the
  `-native-compiler` flag without having to wrap it with `-arg`
  (`#14265 <https://github.com/coq/coq/pull/14265>`_,
  by Pierre-Marie Pédrot).
