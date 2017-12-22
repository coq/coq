Goal forall x : nat, x = x.
Proof.
intros x.
refine ((fun x x => _ tt) tt tt).
let t := match goal with [ |- ?P ] => P end in
let _ := type of t in
idtac.
