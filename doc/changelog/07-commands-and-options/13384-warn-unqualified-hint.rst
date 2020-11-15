- **Deprecated:**
  The default value for hint locality is currently :attr:`local` in a section and
  :attr:`global` otherwise, but is scheduled to change in a future release. For the
  time being, adding hints outside of sections without specifying an explicit
  locality is therefore triggering a deprecation warning. It is recommended to
  use :attr:`export` whenever possible
  (`#13384 <https://github.com/coq/coq/pull/13384>`_,
  by Pierre-Marie Pédrot).
