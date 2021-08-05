Set Primitive Projections.
Set Implicit Arguments.
Record prod A B := pair { fst : A ; snd : B }.
Goal forall A B : Set, True.
Proof.
  intros A B.
  evar (a : prod A B); evar (f : (prod A B -> Set)).
  let a' := (eval unfold a in a) in
  eset(foo:=eq_refl : a' = (@pair _ _ (fst a') (snd a'))).
  (* check generated evar names *)
  [fst]:idtac.
  [snd]:idtac.
Abort.

(* Combining eta for arrow type and tuples *)
Goal forall A B : Set, True.
Proof.
  intros A B.
  evar (a : nat -> prod (A -> A -> A) B); evar (f : (nat -> prod (A -> A -> A) B) -> Set).
  let a' := (eval unfold a in a) in
  eset(foo:=eq_refl : a' = (fun x => pair (fun y y' => fst (a' x) y y') (snd (a' x)))).
  (* check generated evar names *)
  [fst]:idtac.
  [snd]:idtac.
Abort.

Goal forall A B : Set, True.
Proof.
  intros A B.
  evar (a : nat); evar (f : nat -> Set).
  let a' := (eval unfold a in a) in
  eset(foo:=eq_refl : a' = S (pred a')).
Abort.

(* An example with de Bruijn *)
Check fun (z:nat) (z':z=z) =>
  eq_refl : ?[q] = (fun x : z'=z' => pair (fun (y:x=x) (y':y=y) => fst (?q x) y y') (snd (?q x))).
