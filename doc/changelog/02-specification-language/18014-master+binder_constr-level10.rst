- **Changed:**
  :token:`term_forall_or_fun`, :token:`term_let`, :token:`term_fix`,
  :token:`term_cofix` and :token:`term_if` from :token:`term` at level 200
  to :token:`term10` at level 10. This is a first step towards getting rid
  of the recovery mechanism of camlp5/coqpp. The impact will mostly be
  limited to rare cases of additional parentheses around the above
  (`#18014 <https://github.com/coq/coq/pull/18014>`_,
  by Hugo Herbelin).
