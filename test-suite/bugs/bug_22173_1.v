Goal True.
Proof.
  eassert (Some _ = Some _) as HS by shelve.
  injection HS. (* undefined quality *)
  exact (fun _:0=0 => I).
  Unshelve. reflexivity.
Qed.
