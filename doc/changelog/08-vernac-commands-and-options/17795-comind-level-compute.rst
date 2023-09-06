- **Changed:**
  automatic lowering of record types to `Prop` now matches the behavior for inductives:
  no lowering when universe polymorphism is on, more lowering with recursive records
  (`#17795 <https://github.com/coq/coq/pull/17795>`_,
  fixes `#17801 <https://github.com/coq/coq/issues/17801>`_
  and `#17796 <https://github.com/coq/coq/issues/17796>`_
  and `#17801 <https://github.com/coq/coq/issues/17801>`_
  and `#17805 <https://github.com/coq/coq/issues/17805>`_,
  by Gaëtan Gilbert).
