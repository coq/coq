- **Changed:**
  The standard library now contains a more complete theory of equality
  on types of the form :g:`exists x : A, P x` and :g:`exists2 x : A, P
  x & Q x` when we have :g:`A : Prop`.  To bring this theory more in
  line with the existing theory about sigma types,
  :g:`eq_ex_uncurried`, :g:`eq_ex2_uncurried`, :g:`eq_ex`,
  :g:`eq_ex2`, :g:`eq_ex_hprop`, :g:`eq_ex2_hprop` have been renamed
  into :g:`eq_ex_intro_uncurried`, :g:`eq_ex_intro2_uncurried`,
  :g:`eq_ex_intro`, :g:`eq_ex_intro2`, :g:`eq_ex_intro_hprop`,
  :g:`eq_ex_intro2_hprop` respectively and the implicit status of
  these lemmas has changed slightly (`#14174
  <https://github.com/coq/coq/pull/14174>`_, by Jason Gross).
