- **Changed:**
  ``apply with`` does not rename arguments unless using compatibility flag :flag:`Apply With Renaming`
  (`#13837 <https://github.com/coq/coq/pull/13837>`_,
  fixes `#13759 <https://github.com/coq/coq/issues/13759>`_,
  by Gaëtan Gilbert).

  Porting hint: if the renaming is because of a goal variable (eg
  ``intros x; apply foo with (x0 := bar)`` where ``About foo.`` says
  the argument is called ``x``) it is probably caused by an
  interaction with implicit arguments and ``apply @foo with (x :=
  bar)`` will usually be a backwards compatible fix.
