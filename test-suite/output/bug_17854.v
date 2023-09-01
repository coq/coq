Fail Check fun b : bool
      => match b, b with
         | true as a, true as a | true as a, _ => true
         | _, _ => false
         end.

Fail Check fun b : bool
      => match b, b with
         | true as a, true as a => true
         | _, _ => false
         end.

Definition f b :=
         match b, b with
         | true as a as a, true as b => true
         | _, _ => false
         end.

Module Bug18002.

(* Non linearity to be checked first also at the level of inner
   disjunctive patterns *)

Inductive U := p :nat->nat->U.

Fail Check  match p 1 2 with
 | (p n 0 | p n (S n)) => 0
 | _ => 1
 end.

End Bug18002.
