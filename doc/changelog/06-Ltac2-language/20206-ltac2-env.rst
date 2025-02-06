- **Added:**
  APIs to manipulate local environments: local environments can be obtained
  from the global or goal environment using `Ltac2.Env.current_env`
  (or `global_env` or `goal_env` depending on your usage),
  extended using `Ltac2.Env.push_named_assum` and `Ltac2.Env.Unsafe.push_named_def`,
  then used with various functions such as `Ltac2.Constr.pretype_in`
  (for each API operating on an implicit environment,
  a `_in` variant has been added operating on an explicitly provided environment)
  (`#20206 <https://github.com/coq/coq/pull/20206>`_,
  by Gaëtan Gilbert).
