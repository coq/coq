- The :tacn:`under` and :tacn:`over` tactics can handle any registered
  setoid equality (beyond mere double implications).  See also Section
  :ref:`under_ssr`. This generalized support for setoid equalities is
  enabled as soon as we do both ``Require Import ssreflect.`` and
  ``Require Setoid.`` (`#10022 <https://github.com/coq/coq/pull/10022>`_,
  by Erik Martin-Dorel, with suggestions and review by Enrico Tassi).
