Goal True -> True.
  simple refine (let H : True -> True := _ in
                 _);
    [ intro x; exact x | ];
    lazymatch goal with
    | [ H := ?v |- _ ]
      => abstract exact v
    end.
Qed.
