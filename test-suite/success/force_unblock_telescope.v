(* Telescope-backed, block-local [__unblock] regression tests. *)

Require Import Corelib.Force Corelib.extraction.Extraction Ltac2.Ltac2.
Set Default Proof Mode "Classic".

Ltac syn_refl := lazymatch goal with |- ?t = ?t => exact eq_refl end.
Notation LAZY t := (ltac:(let x := eval lazy in t in exact x)) (only parsing).
Notation WHNF t := (ltac:(let x := eval lazy head in t in exact x)) (only parsing).

(* [__unblock] is source syntax local to a block body. *)
Fail Check (__unblock nat (__block nat 0)).
Fail Check (fun b : Blocked nat => __unblock nat b).

Axiom f : bool -> Blocked (nat -> Prop).
Axiom g : bool -> Blocked Prop.
Axiom dep : forall n : nat, Blocked (n = n).
Axiom nested_blocked : Blocked (Blocked nat).
Axiom stuck_nat : Blocked nat.

(* These definitions exercise saving and checking telescope-bearing blocks. *)
Definition captured_outer_binder : Blocked Prop :=
  __block Prop (forall (x z : bool), __unblock _ (f x) 0).

Definition captured_inner_binder_only : Blocked Prop :=
  __block Prop (forall (_unused : nat) (z : bool), __unblock _ (g z)).

Definition captured_local_definition : Blocked (forall n : nat, n = n) :=
  __block _ (fun n : nat => let m := n in __unblock _ (dep m)).

Definition captured_nested_entry : Blocked nat :=
  __block nat (__unblock _ (__unblock _ nested_blocked)).

Definition captured_repeated_entries : Blocked (Prop * Prop) :=
  __block _ (__unblock _ (g true), __unblock _ (g true)).

(* Ltac2 exposes the actual entry array and telescopes, rather than an expanded
   body. Telescope declarations are exposed outermost first. *)
Goal True.
Proof.
  ltac2:(
    let c := constr:(__block _ (forall (x z : bool), __unblock _ (f x) 0)) in
    match Constr.Unsafe.kind c with
    | Constr.Unsafe.PBlock _ _ entries _ =>
      if Int.equal (Array.length entries) 1 then () else Control.throw Assertion_failure;
      match Array.get entries 0 with
      | Constr.Unsafe.PBlockEntry context _ _ _ =>
        if Int.equal (Array.length context) 1 then () else Control.throw Assertion_failure;
        match Array.get context 0 with
        | Constr.Unsafe.PBlockAssum binder =>
          if Constr.equal (Constr.Binder.type binder) 'bool
          then () else Control.throw Assertion_failure
        | _ => Control.throw Assertion_failure
        end
      end
    | _ => Control.throw Assertion_failure
    end;

    (* Capturing the inner sibling does not retain an unrelated outer sibling. *)
    let c := constr:(__block _
      (forall (_unused : nat) (z : bool), __unblock _ (g z))) in
    match Constr.Unsafe.kind c with
    | Constr.Unsafe.PBlock _ _ entries _ =>
      match Array.get entries 0 with
      | Constr.Unsafe.PBlockEntry context _ _ _ =>
        if Int.equal (Array.length context) 1 then () else Control.throw Assertion_failure;
        match Array.get context 0 with
        | Constr.Unsafe.PBlockAssum binder =>
          if Constr.equal (Constr.Binder.type binder) 'bool
          then () else Control.throw Assertion_failure
        | _ => Control.throw Assertion_failure
        end
      end
    | _ => Control.throw Assertion_failure
    end;

    (* A selected local definition closes over the assumption it depends on. *)
    let c := constr:(__block _
      (fun n : nat => let m := n in __unblock _ (dep m))) in
    match Constr.Unsafe.kind c with
    | Constr.Unsafe.PBlock _ _ entries _ =>
      match Array.get entries 0 with
      | Constr.Unsafe.PBlockEntry context _ _ _ =>
        if Int.equal (Array.length context) 2 then () else Control.throw Assertion_failure;
        match Array.get context 0, Array.get context 1 with
        | Constr.Unsafe.PBlockAssum _, Constr.Unsafe.PBlockDef _ _ => ()
        | _, _ => Control.throw Assertion_failure
        end
      end
    | _ => Control.throw Assertion_failure
    end;

    (* Identical source occurrences remain distinct entries. *)
    let c := constr:(__block _
      (__unblock _ (g true), __unblock _ (g true))) in
    match Constr.Unsafe.kind c with
    | Constr.Unsafe.PBlock _ _ entries _ =>
      if Int.equal (Array.length entries) 2 then () else Control.throw Assertion_failure
    | _ => Control.throw Assertion_failure
    end;

    (* The outer nested occurrence depends on the earlier hidden entry. *)
    let c := constr:(__block _ (__unblock _ (__unblock _ nested_blocked))) in
    match Constr.Unsafe.kind c with
    | Constr.Unsafe.PBlock _ _ entries _ =>
      if Int.equal (Array.length entries) 2 then () else Control.throw Assertion_failure;
      match Array.get entries 1 with
      | Constr.Unsafe.PBlockEntry _ _ value _ =>
        match Constr.Unsafe.kind value with
        | Constr.Unsafe.Rel 1 => ()
        | _ => Control.throw Assertion_failure
        end
      end
    | _ => Control.throw Assertion_failure
    end).
  exact I.
Qed.

(* Unsafe construction can expose entries, but the checker rejects malformed
   hidden references and accepts the corresponding well-scoped block. *)
Goal True.
Proof.
  ltac2:(
    let base := constr:(__block nat 0) in
    match Constr.Unsafe.kind base with
    | Constr.Unsafe.PBlock instance _ _ _ =>
      let entry := Constr.Unsafe.PBlockEntry (Array.of_list []) 'nat base Constr.Relevance.relevant in
      let rel1 := Constr.Unsafe.make (Constr.Unsafe.Rel 1) in
      let rel2 := Constr.Unsafe.make (Constr.Unsafe.Rel 2) in
      let good := Constr.Unsafe.make
        (Constr.Unsafe.PBlock instance 'nat [|entry|] rel1) in
      match Constr.Unsafe.check good with
      | Val _ => ()
      | Err _ => Control.throw Assertion_failure
      end;
      let bad_body := Constr.Unsafe.make
        (Constr.Unsafe.PBlock instance 'nat [|entry|] rel2) in
      match Constr.Unsafe.check bad_body with
      | Err _ => ()
      | Val _ => Control.throw Assertion_failure
      end;
      let bad_entry := Constr.Unsafe.PBlockEntry
        (Array.of_list []) 'nat rel1 Constr.Relevance.relevant in
      let bad_value := Constr.Unsafe.make
        (Constr.Unsafe.PBlock instance 'nat [|bad_entry|] rel1) in
      match Constr.Unsafe.check bad_value with
      | Err _ => ()
      | Val _ => Control.throw Assertion_failure
      end
    | _ => Control.throw Assertion_failure
    end).
  exact I.
Qed.

Definition concrete_dep (n : nat) : Blocked (n = n) :=
  __block _ (eq_refl n).

Goal WHNF (__block _ (fun n : nat => __unblock _ (concrete_dep n))) =
     __block _ (fun n : nat => eq_refl n).
Proof. syn_refl. Qed.

Goal WHNF
       (__block nat
         (__unblock nat
           (__unblock (Blocked nat)
             (__block (Blocked nat) (__block nat 3))))) =
     __block nat 3.
Proof. syn_refl. Qed.

Goal LAZY (__block _
       (__unblock _ (__block _ 1) + __unblock _ (__block _ 1))) =
     __block _ 2.
Proof. syn_refl. Qed.

(* A stuck capture reifies as [PRun], never as an internal unblock term. *)
Goal WHNF (__block nat (__unblock nat stuck_nat)) =
     __block nat (__run nat nat stuck_nat (fun n => n)).
Proof. syn_refl. Qed.

Goal LAZY (__run nat nat
       (__block nat (S (__unblock nat (__block nat 1))))
       (fun n => n)) = 2.
Proof. syn_refl. Qed.

Goal __run nat nat
       (__block nat (S (__unblock nat (__block nat 1))))
       (fun n => n) = 2.
Proof. cbn. reflexivity. Qed.

Goal (__run _ _
       (__block _ (fun n : nat => let m := n in __unblock _ (concrete_dep m)))
       (fun f => f) 3) = eq_refl 3.
Proof. cbn. reflexivity. Qed.

Definition one_stuck_capture : Blocked nat :=
  __block nat (__unblock nat stuck_nat).
Definition two_stuck_captures : Blocked nat :=
  __block nat (let _ := __unblock nat stuck_nat in __unblock nat stuck_nat).

Goal one_stuck_capture = one_stuck_capture.
Proof. reflexivity. Qed.
Fail Check (eq_refl : one_stuck_capture = two_stuck_captures).

Definition under_lambda (b : Blocked nat) : nat -> Blocked nat :=
  fun n => __block nat (n + __unblock nat b).

Inductive sunit : SProp := sitt.
Definition blocked_sunit : Blocked sunit := __block sunit sitt.
Definition captured_sprop : Blocked sunit :=
  __block sunit (__unblock sunit blocked_sunit).
Definition captured_prop (b : Blocked Prop) : Blocked Prop :=
  __block Prop (__unblock Prop b).
Definition captured_set (b : Blocked nat) : Blocked nat :=
  __block nat (__unblock nat b).
Polymorphic Definition captured_type@{u v}
    (b : Blocked@{Type;v} Type@{u}) : Blocked@{Type;v} Type@{u} :=
  __block@{Type;v} Type@{u} (__unblock@{Type;v} Type@{u} b).

Polymorphic Definition polymorphic_capture@{u}
    (A : Type@{u}) (b : Blocked A) : Blocked (A -> A) :=
  __block _ (fun x : A => let y := x in __unblock _ b).

Definition extracted_capture (b : Blocked nat) : nat :=
  __run nat nat (__block nat (S (__unblock nat b))) (fun n => n).
Extraction TestCompile extracted_capture.
