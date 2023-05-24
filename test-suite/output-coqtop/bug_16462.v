Ltac foo x y := idtac; fail 1.
Ltac bar x f := idtac; f foo x I.
Ltac baz x := let H := fresh in
              simple refine (let H : True := _ in _);
              [ abstract exact I
              | let v := (eval cbv in H) in
                let F := ltac:(fun _ => let v' := v in constr:(fun _ => ltac:(idtac v'; fail 1))) in
                let f := ltac:(fun f x y => idtac v; f x) in
                f F () () ].
Set Ltac Backtrace.
Goal True.
  baz I.
