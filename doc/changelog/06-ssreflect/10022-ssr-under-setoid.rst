- Generalize tactics :tacn:`under` and :tacn:`over` for any registered
  relation. More precisely, assume the given context lemma has type
  `forall f1 f2, .. -> (forall i, R1 (f1 i) (f2 i)) -> R2 f1 f2`.  The
  first step performed by :tacn:`under` (since Coq 8.10) amounts to
  calling the tactic :tacn:`rewrite <rewrite (ssreflect)>`, which
  itself relies on :tacn:`setoid_rewrite` if need be. So this step was
  already compatible with a double implication or setoid equality for
  the conclusion head symbol `R2`. But a further step consists in
  tagging the generated subgoal `R1 (f1 i) (?f2 i)` to protect it from
  unwanted evar instantiation, and get `Under_rel _ R1 (f1 i) (?f2 i)`
  that is displayed as ``'Under[ f1 i ]``. In Coq 8.10, this second
  (convenience) step was only performed when `R1` was Leibniz' `eq` or
  `iff`. Now, it is also performed for any relation `R1` which has a
  ``RewriteRelation`` instance (a `RelationClasses.Reflexive` instance
  being also needed so :tacn:`over` can discharge the ``'Under[ _ ]``
  goal by instantiating the hidden evar.) Also, it is now possible to
  manipulate `Under_rel _ R1 (f1 i) (?f2 i)` subgoals directly if `R1`
  is a `PreOrder` relation or so, thanks to extra instances proving
  that `Under_rel` preserves the properties of the `R1` relation.
  These two features generalizing support for setoid-like relations is
  enabled as soon as we do both ``Require Import ssreflect.`` and
  ``Require Setoid.`` Finally, a rewrite rule ``UnderE`` has been
  added if one wants to "unprotect" the evar, and instantiate it
  manually with another rule than reflexivity (i.e., without using the
  :tacn:`over` tactic nor the ``over`` rewrite rule). See also Section
  :ref:`under_ssr` (`#10022 <https://github.com/coq/coq/pull/10022>`_,
  by Erik Martin-Dorel, with suggestions and review by Enrico Tassi
  and Cyril Cohen).
