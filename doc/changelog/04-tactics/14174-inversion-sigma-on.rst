- **Added:**
  :tacn:`inversion_sigma` can now be applied to a specified hypothesis
  and additionally supports intropatterns, so it can be used much like
  :tacn:`induction` and :tacn:`inversion`.  Additionally,
  :tacn:`inversion_sigma` now supports the types :n:`ex` (:n:`exists x
  : A, P x`) and :n:`ex2` (:n:`exists2 x : A, P x & Q x`) in cases
  where the first argument :n:`A` is a :n:`Prop` (`#14174
  <https://github.com/coq/coq/pull/14174>`_, by Jason Gross).
