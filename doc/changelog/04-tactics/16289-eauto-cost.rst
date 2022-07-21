- **Changed:**
  :tacn:`eauto` respects priorities of ``Extern`` hints
  (`#16289 <https://github.com/coq/coq/pull/16289>`_,
  fixes `#5163 <https://github.com/coq/coq/issues/5163>`_
  and `#16282 <https://github.com/coq/coq/issues/16282>`_,
  by Andrej Dudenhefner).

  .. warning:: Code that relies on eager evaluation of ``Extern`` hints
     with high assigned cost by :tacn:`eauto` will change its performance
     profile or potentially break.
     To approximate prior behavior, set to zero the cost of ``Extern`` hints,
     which may solve the goal in one step.
