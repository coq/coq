- Generalize tactics :tacn:`under` and :tacn:`over` for any registered
  setoid equality. More precisely, assume the given context lemma has
  type `forall f1 f2, .. -> (forall i, R1 (f1 i) (f2 i)) -> R2 f1 f2`.
  The first step performed by :tacn:`under` (since Coq 8.10) amounts
  to calling the tactic :tacn:`rewrite <rewrite (ssreflect)>`, which
  itself relies on :tacn:`setoid_rewrite` if need be. So this step was
  already compatible with a double implication or setoid equality for
  the conclusion head symbol `R2`. But a further step consists in
  tagging the generated subgoal `R1 (f1 i) (?f2 i)` to protect it from
  unwanted evar instantiation, and obtain a subgoal displayed as
  ``'Under[ f1 i ]``. In Coq 8.10, this second (convenience) step was
  only performed when `R1` was Leibniz' `eq` or `iff`. Now, it is also
  performed for any relation `R1` which has a ``RewriteRelation``
  instance as well as a ``RelationClasses.Reflexive`` instance. This
  generalized support for setoid relations is enabled as soon as we do
  both ``Require Import ssreflect.`` and ``Require Setoid.`` Finally,
  a rewrite rule ``UnderE`` has been added if one wants to "unprotect"
  the evar, and instantiate it manually with another rule than
  reflexivity (i.e., without using :tacn:`over`). See also Section
  :ref:`under_ssr` (`#10022 <https://github.com/coq/coq/pull/10022>`_,
  by Erik Martin-Dorel, with suggestions and review by Enrico Tassi).
