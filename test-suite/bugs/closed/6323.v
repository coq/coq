Goal True.
  simple refine (let X : Type := _ in _);
    [ abstract exact Set using Set'
    | let X' := (eval cbv delta [X] in X) in
      clear X;
      simple refine (let id' : { x : X' | True } -> X' := _ in _);
      [ abstract refine (@proj1_sig _ _) | ]
    ].
Abort.
