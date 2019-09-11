- Fix a printing bug of OCaml extraction on dependent record projections, which
  produced improper `assert false`. This change makes the OCaml extractor
  internally inline record projections by default; thus the monolithic OCaml
  extraction (:cmd:`Extraction` and :cmd:`Recursive Extraction`) does not
  produce record projection constants anymore except for record projections
  explicitly instructed to extract, and records declared in opaque modules
  (`#10577 <https://github.com/coq/coq/pull/10577>`_,
  fixes `#7348 <https://github.com/coq/coq/issues/7348>`_,
  by Kazuhiko Sakaguchi).
