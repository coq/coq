Goal True -> True /\ True.
  intro x; split;
    unshelve (let f := open_constr:(_) in clear x; refine f); exact x.
Defined.
