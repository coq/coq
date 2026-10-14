(* Two "only printing" declarations may use different argument entries. *)

Axiom funspec : forall {A B} T (pre : T -> A) (post : T -> B), Prop.

Notation "'WITH' x : A  'PRE'  [ ] P 'POST' [ ] Q" :=
  (funspec _ (fun x : A => P) (fun x : A => Q))
    (at level 10, x ident, P at level 100, Q at level 100, only printing).

Notation "'WITH' x : A  'PRE'  [ ] P 'POST' [ ] Q" :=
  (funspec _ (fun x : A => P) (fun x : A => Q))
    (at level 10, x strict pattern at level 9, P at level 100, Q at level 100,
     only printing).
