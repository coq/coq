- **Fixed:**
  Setoid rewriting now remembers the (invisible) binder names of non-dependent product types. SSReflect's rewrite tactic expects these names to be retained when using ``rewrite foo in H``.
  This also fixes SSR ``rewrite foo in H *`` erroneously reverting ``H``.
  (`#13882 <https://github.com/coq/coq/pull/13882>`_,
  fixes `#12011 <https://github.com/coq/coq/issues/12011>`_,
  by Gaëtan Gilbert).
