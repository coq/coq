- **Changed:**
  Ltac2 `exact` and `eexact` elaborate their argument using the type of the goal as expected type,
  instead of elaborating with no expected type then unifying the resulting type with the goal
  (`#18157 <https://github.com/coq/coq/pull/18157>`_,
  fixes `#12827 <https://github.com/coq/coq/issues/12827>`_,
  by Gaëtan Gilbert).
