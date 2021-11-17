- **Changed:**
  The :tacn:`exact` tactic now takes a :g:`uconstr` as argument
  instead of an ad-hoc one. In very rare cases, this can change
  the order of resolution of dependent evars when used over
  several goals at once
  (`#15171 <https://github.com/coq/coq/pull/15171>`_,
  by Pierre-Marie Pédrot).
