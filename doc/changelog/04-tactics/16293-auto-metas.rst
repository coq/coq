- **Changed:**
  less discrepancies between :tacn:`auto` hint evaluation and :tacn:`simple apply`, :tacn:`exact` tactics
  (`#16293 <https://github.com/coq/coq/pull/16293>`_,
  fixes `#16062 <https://github.com/coq/coq/issues/16062>`_
  and `#16323 <https://github.com/coq/coq/issues/16323>`_,
  by Andrej Dudenhefner).

  .. warning:: :tacn:`auto` may solve more goals.
     As a result, non-monotone use of :tacn:`auto` such as :g:`tac1; auto. tac2.` may break.
     For backwards compatibility use explicit goal management.
