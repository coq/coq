- **Added:**
  :tacn:`lazy`, :tacn:`simpl`, :tacn:`cbn` and :tacn:`cbv` and the associated :cmd:`Eval`
  and :tacn:`eval` reductions learned to do head reduction when given flag `head`
  (eg `Eval lazy head in (fun x => Some ((fun y => y) x)) 0` produces `Some ((fun y => y) 0)`)
  (`#17503 <https://github.com/coq/coq/pull/17503>`_,
  by Gaëtan Gilbert; :tacn:`cbv` case added in `#18190 <https://github.com/coq/coq/pull/18190>`_,
  by Hugo Herbelin).
