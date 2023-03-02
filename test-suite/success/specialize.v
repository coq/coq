
Goal forall a b c : nat,  a = b -> b = c -> forall d, a+d=c+d.
intros.

(* "compatibility" mode: specializing a global name
   means a kind of generalize *)

specialize eq_trans. intros _.
specialize eq_trans with (1:=H)(2:=H0). intros _.
specialize eq_trans with (x:=a)(y:=b)(z:=c). intros _.
specialize eq_trans with (1:=H)(z:=c). intros _.
specialize eq_trans with nat a b c. intros _.
specialize (@eq_trans nat). intros _.
specialize (@eq_trans _ a b c). intros _.
specialize (eq_trans (x:=a)). intros _.
specialize (eq_trans (x:=a)(y:=b)). intros _.
specialize (eq_trans H H0). intros _.
specialize (eq_trans H0 (z:=b)). intros _.

(* incomplete bindings: y is left quantified and z is instantiated. *)
specialize eq_trans with (x:=a)(z:=c).
intro h.
(* y can be instantiated now *)
specialize h with (y:=b).
(* z was instantiated above so this must fail. *)
Fail specialize h with (z:=c).
clear h.

(* incomplete bindings: 1st dep hyp is instantiated thus A, x and y
   instantiated too. *)
specialize eq_trans with (1:=H).
intro h.
(* 2nd dep hyp can be instantiated now, which instatiates z too. *)
specialize h with (1:=H0).
(* checking that there is no more products in h. *)
match type of h with
| _ = _ => idtac
| _ => fail "specialize test failed: hypothesis h should be an equality at this point"
end.
clear h.


(* local "in place" specialization *)
assert (Eq:=eq_trans).

specialize Eq.
specialize Eq with (1:=H)(2:=H0). Undo.
specialize Eq with (x:=a)(y:=b)(z:=c). Undo.
specialize Eq with (1:=H)(z:=c). Undo.
specialize Eq with nat a b c. Undo.
specialize (Eq nat). Undo.
specialize (Eq _ a b c). Undo.
(* no implicit argument for Eq, hence no (Eq (x:=a)) *)
specialize (Eq _ _ _ _ H H0). Undo.
specialize (Eq _ _ _ b H0). Undo.

(* incomplete binding *)
specialize Eq with (y:=b).
(* A and y have been instantiated so this works *)
specialize (Eq _ _ H H0).
Undo 2.

(* incomplete binding (dependent) *)
specialize Eq with (1:=H).
(* A, x and y have been instantiated so this works *)
specialize (Eq _ H0).
Undo 2.

(* incomplete binding (dependent) *)
specialize Eq with (1:=H) (2:=H0).
(* A, x and y have been instantiated so this works *)
match type of Eq with
| _ = _ => idtac
| _ => fail "specialize test failed: hypothesis Eq should be an equality at this point"
end.
Undo 2.

(*
(** strange behavior to inspect more precisely *)

(* 1) proof aspect : let H:= ... in (fun H => ..) H
    presque ok... *)

(* 2) echoue moins lorsque zero premise de mangé *)
specialize eq_trans with (1:=Eq).  (* mal typé !! *)

(* 3) Seems fixed.*)
specialize eq_trans with _ a b c. intros _.
(* Anomaly: Evar ?88 was not declared. Please report. *)
*)

Abort.

(* Test use of pose proof and assert as a specialize *)

Goal True -> (True -> 0=0) -> False -> 0=0.
intros H0 H H1.
pose proof (H I) as H.
(* Check that the hypothesis is in 2nd position by removing the top one *)
match goal with H:_ |- _ => clear H end.
match goal with H:_ |- _ => exact H end.
Qed.

Goal True -> (True -> 0=0) -> False -> 0=0.
intros H0 H H1.
assert (H:=H I).
(* Check that the hypothesis is in 2nd position by removing the top one *)
match goal with H:_ |- _ => clear H end.
match goal with H:_ |- _ => exact H end.
Qed.


(* let ins should be supported int he type of the specialized hypothesis *)
Axiom foo: forall (m1:nat) (m2: nat), let n := 2 * m1 in (m1 = m2 -> False).
Goal False.
  pose proof foo as P.
  assert (2 = 2) as A by reflexivity.
  (* specialize P with (m2:= 2). *)
  specialize P with (1 := A).
  match type of P with
  | let n := 2 * 2 in False => idtac
  | _ => fail "test failed"
  end.
  assumption.
Qed.

(* Another more subtle test on letins: they should not interfere with foralls. *)
Goal forall (P: forall a c:nat,
                  let b := c in
                  let d := 1 in
                  forall n : a = d, a = c+1),
    True.
  intros P.
  specialize P with (1:=eq_refl).
  match type of P with
  | forall c : nat, let f := c in let d := 1 in 1 = c + 1 => idtac
  | _ => fail "test failed"
  end.
  constructor.
Qed.


(* Test specialize as *)

Goal (forall x, x=0) -> 1=0.
intros.
specialize (H 1) as ->.
reflexivity.
Qed.

(* A test from corn *)

Goal (forall x y, x=0 -> y=0 -> True) -> True.
intros.
specialize (fun z => H 0 z eq_refl).
exact (H 0 eq_refl).
Qed.

Module bug_17322.

Axiom key : Type.
Axiom value : Type.
Axiom eqb : key -> key -> bool.
Axiom remove : list value -> key -> list value.
Axiom sorted : list value -> bool.
Axiom lookup : list value -> key -> value.

Goal forall (l : list value) (k : key),
  (sorted l = true -> forall k' : key, eqb k k' = false ->
    lookup (remove l k') k = lookup l k) ->
  sorted l = true -> False
.
Proof.
intros l k IHl ST.
specialize IHl with (1 := ST).
Abort.

End bug_17322.

Module bug_17322_2.

Axiom tuple : Type.
Axiom mem : Type.
Axiom unchecked_store_bytes : tuple -> mem.
Axiom load_bytes : mem -> Prop.

Goal forall
(IHn : forall (m' : mem) (w : tuple),
  unchecked_store_bytes w = m' -> load_bytes m' -> True),
True.
Proof.
intros.
Fail specialize IHn with (1 := eq_refl).
(* After #17322 this fails with

    In environment
    IHn : forall (m' : mem) (w : tuple), unchecked_store_bytes w = m' -> load_bytes m' -> True
    m' : mem
    w : tuple
    Unable to unify "?t" with "w" (cannot instantiate "?t" because "w" is not in its scope:
    available arguments are "IHn").

   Previously it was leaving w as an unresolved evar, producing the hypothesis

    IHn : load_bytes (unchecked_store_bytes ?w) -> True

   The correct behaviour should probably to requantify on w as

    IHn : forall w, load_bytes (unchecked_store_bytes w) -> True

*)
Abort.

End bug_17322_2.
