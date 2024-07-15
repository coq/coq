- **Fixed:**
  :cmd:`Search` with modifier `is:Scheme` restricted the search to inductive types
  which have schemes instead of the schemes themselves.
  For instance `Search nat is:Scheme` with just the prelude loaded would return `le`
  i.e. the only inductive type whose type mentions `nat`
  (`#18537 <https://github.com/coq/coq/pull/18537>`_,
  fixes `#18298 <https://github.com/coq/coq/issues/18298>`_,
  by Gaëtan Gilbert).
