(* Submitted by Roland Zumkeller *)

Notation "a ? b ; c" := (if a then b else c) (at level 10).

Check (true ? 0 ; 1).
Check if true as x return (if x then nat else bool) then 0 else true.

Notation "'proj1' t" := (let (a,_) := t in a) (at level 1).

Check (fun e : nat * nat => proj1 e).

Notation "'decomp' a 'as' x , y 'in' b" := (let (x,y) := a in b) (at level 1).

Check (decomp (true,true) as t, u in (t,u)).

(* Submitted by Roland Zumkeller *)

Notation "! A" := (forall _:nat, A) (at level 60).

Check ! (0=0).
Check forall n, n=0.
Check forall n:nat, 0=0.
