Goal 1 = 2.
Proof.
match goal with
  | [ |- context G[2] ] => let y := constr:(fun x => $(let r := constr:(@eq Set x x) in
                                                       clear x;
                                                       exact r)$) in
                           pose y
end.
Abort.
