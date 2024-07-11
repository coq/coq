Module S.
  #[local] Set Printing Unfolded Projection As Match.
  #[projections(primitive=yes)]
  Record r (u : unit) := { r_car : Type }.

  Axiom u : unit.

  Definition rO : r u -> r u := fun o => {| r_car := option (r_car u o) |}.

  Goal forall o, exists M, M (r_car u o)= r_car u (rO o).
  Proof.
    intros. eexists _.
    Timeout 1 refine (eq_refl _).
  Qed.
End S.

Module T.
  #[local] Set Printing Unfolded Projection As Match.
  #[projections(primitive=yes)]
  Record r (u : unit) := { r_car : Type }.

  Axiom u : unit.
  Axiom v : forall i : nat, r u.

  Goal forall i, exists P, P (v i) = r_car u (v i).
  Proof.
    intros. eexists _.
    (* Unable to unify "r (v i)" with "?P (v i)". *)
    refine (eq_refl _).
  Qed.
End T.

(* Here we test that CS inference happens even if the projection is
   primitive and the projected term has a type that is not an inductive
   (but rather an evar). We exploit the fact that Coq considers are
   well typed terms containing evars for which a suspended
   unif problem exists. *)
Require Import Ltac2.Ltac2 Ltac2.Unification Ltac2.Constr Ltac2.Printf.

Module U.

  #[projections(primitive=yes)] Record r := R { r_car : Type }.
  #[projections(primitive=yes)] Record s := S { s_car : Type }.

  (* The type of the CS instance will help unification make a choice
     for the (_ : _ r) problem below *)
  Canonical Structure foo (x : s): (fun x=>x) r := R (s_car x).

  Axiom a : s.

  Goal True.
  Ltac2 Eval
    let t1 := open_constr:( ( _ : _ r ).(r_car) ) in (* the problem mentioned above *)
    let t2 := constr:( (a).(s_car) ) in
    (* safeguard against parser *)
    match (Constr.Unsafe.kind t1) with
    | Constr.Unsafe.Proj _ _ _ => ()
    | _ => fail
    end;
    match (Constr.Unsafe.kind t2) with
    | Constr.Unsafe.Proj _ _ _ => ()
    | _ => fail
    end;
    (* printf "%t = %t" t1 t2; *)
    unify_with_full_ts t1 t2; (* fails before #19358 *)
    (* printf "%t = %t" t1 t2. *)
    ().
  Abort.

End U.
