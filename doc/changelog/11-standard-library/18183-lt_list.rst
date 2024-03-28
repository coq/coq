- **Added:**
  well-founded list extension ``list_ext`` of a well-founded relation in ``Coq.Wellfounded.List_Extension``, including infrastructure lemmas.
  It can be used for well-foundedness proofs such as ``wf_lex_exp`` in ``Coq.Wellfounded.Lexicographic_Exponentiation``.
  Also added lemma ``wf_clos_trans_inverse_rel`` to ``Coq.Wellfounded.Transitive_Closure`` and lemma ``clos_t_clos_rt`` to ``Coq.Relations.Operators_Properties``
  (`#18183 <https://github.com/coq/coq/pull/18183>`_,
  by Andrej Dudenhefner).
