- **Changed:**
  the requirement prefix of the standard library from ``Coq`` to
  ``Stdlib`` and made it mandatory. As a temporary measure, for
  backward compatibility with older versions, ``Coq``, or a missing
  `From Stdlib`, is immediatly translated to ``Stdlib`` with a
  warning. It is thus not recommended to name anything ``Coq`` or
  ``Coq.*``.
  The recommended transition path is to first potentially silence
  the warnings, adding the lines
  ``-arg -w -arg -deprecated-from-Coq``,
  ``-arg -w -arg -deprecated-dirpath-Coq`` and
  ``-arg -w -arg -deprecated-missing-stdlib``
  or simply the more generic
  ``-arg -compat -arg 8.20`` to your ``_CoqProject``.
  Then, when droping support for Coq <= 8.20, replacing requirement of
  Stdlib modules by `From Stdlib Require {Import,Export,} <LibraryModules>.`.
  Beware that the Stdlib still has a handful redundant names, that is
  for modules `Byte`, you still have to use `From Stdlib.Strings` or
  `From Stdlib.Init`, for `Tactics` use `From Stdlib.Program` or `From
  Stdlib.Init`, for `Tauto` use `From Stdlib.micromega` of `From
  Stdlib.Init` and for `Wf`, use `From Stdlib.Program` or `From
  Stdlib.Init`
  (`#19310 <https://github.com/coq/coq/pull/19310>`_
  and `#19530 <https://github.com/coq/coq/pull/19530>`_,
  the latter starting to implement `CEP#83 <https://github.com/coq/ceps/pull/83>`_
  by Pierre Roux).
