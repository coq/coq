Ltac assert_eq tac :=
  lazymatch goal with
  | |- ?l = ?r =>
      let l := tac l in
      tryif (constr_eq l r) then
        change (l = r);
        reflexivity
      else
        fail "reduced term" l "not equal to RHS term" r
  end.
Ltac assert_norm_eq :=
  idtac; assert_eq ltac:(fun l => let l := eval kred in l in l).
Ltac assert_head_eq :=
  idtac; assert_eq ltac:(fun l => let l := eval kred head in l in l).

Goal 1 + 1 = S (0 + 1).
Proof.
  assert_head_eq.
Qed.

Arguments Nat.add _ !_.

Goal 1 + (1 + 1) = S (0 + S (0 + 1)).
Proof.
  assert_head_eq.
Qed.

Axiom x : nat.

Goal x + 1 = x + 1.
Proof.
  assert_head_eq.
Qed.

Goal x + 1 = x + 1.
Proof.
  assert_head_eq.
Qed.
Goal 1 + x = 1 + x.
Proof.
  assert_head_eq.
Qed.
Goal 1 + (x + 1) = 1 + (x + 1).
Proof.
  assert_head_eq.
Qed.

Arguments Nat.add !_ _.
Goal 1 + (x + 1) = S (0 + (x + 1)).
Proof.
  assert_head_eq.
Qed.

Arguments Nat.add _ _ /.

Goal 1 + (x + 1) = S (x + 1).
Proof.
  assert_norm_eq.
Qed.


(* motivating example *)
Inductive type : Set :=
    Tptr : type -> type
  | Tref : type -> type
  | Trv_ref : type -> type
  | Tint : type -> type -> type
  | Tvoid : type
  | Tarray : type -> type -> type
  | Tnamed : type -> type
  | Tfunction : type -> type -> type -> type
  | Tbool : type
  | Tmember_pointer : type -> type -> type
  | Tfloat : type -> type
  | Tqualified : type -> type -> type
  | Tnullptr : type
  | Tnullptr1 : type
  | Tnullptr2 : type
  | Tnullptr3 : type
  | Tnullptr4 : type
  | Tnullptr5 : type
  | Tnullptr6 : type
  | Tnullptr7 : type
  | Tnullptr8 : type
  | Tnullptr9 : type
  | Tnullptr10 : type
  | Tnullptr11 : type
  | Tnullptr12 : type
  | Tnullptr13 : type
  | Tnullptr14 : type
  | Tnullptr15 : type
  | Tnullptr16 : type
  | Tnullptr17 : type
  | Tnullptr18 : type
  | Tnullptr19 : type
  | Tnullptr20 : type
  | Tnullptr21 : type
  | Tnullptr22 : type
  | Tnullptr23 : type
  | Tnullptr24 : type
  | Tnullptr25 : type
  | Tnullptr26 : type
  | Tnullptr27 : type
  | Tnullptr28 : type
  | Tnullptr29 : type
  | Tarch : type -> type -> type
  | Tbla : bla -> type
  | Tblu : blu -> type
with bla :=
| bla1 : type -> bla
| bla2 : type -> bla
| bla3 : type -> bla
| bla4 : type -> bla
with blu :=
| blu1 : type -> blu
| blu2 : type -> blu
| blu3 : type -> blu
| blu4 : type -> blu
.


#[local] Notation EQ_DEC T := (forall x y : T, {x = y} + {~ x = y}) (only parsing).

Lemma type_eq_dec' : EQ_DEC type
with bla_eq_dec' : EQ_DEC bla
with blu_eq_dec' : EQ_DEC blu.
Proof.
  all: intros x y.
  all: pose (type_eq_dec' : EQ_DEC type).
  all: pose (bla_eq_dec' : EQ_DEC bla).
  all: pose (blu_eq_dec' : EQ_DEC blu).
  all: decide equality.
Defined.

Definition type_eq_dec := Eval lazy zeta delta [type_eq_dec'] in type_eq_dec'.
Definition bla_eq_dec :=  Eval lazy zeta delta [bla_eq_dec']  in bla_eq_dec'.
Definition blu_eq_dec :=  Eval lazy zeta delta [blu_eq_dec']  in blu_eq_dec'.

Definition Decision := fun P : Prop => {P} + {~ P}.
Definition RelDecision := fun {A B : Type} (R : A -> B -> Prop) => forall (x : A) (y : B), Decision (R x y).
Definition bool_decide {P:Prop} : {P} + {~P} -> bool :=
    fun x => match x with | left _ => true | right _ => false end.
Definition decide_rel {A B : Type} (R : A -> B -> Prop) (RelDecision : RelDecision R) : forall (x : A) (y : B), Decision (R x y) :=
  RelDecision.

Eval kred in bool_decide (decide_rel _ (fun x y => left eq_refl) 1 1).

Goal (if if bool_decide (decide_rel _ type_eq_dec Tvoid Tvoid) then true else false then True else False).
  Succeed time "lazy " lazy.       (* Tactic call lazy  ran for 0. secs (0.u,0.s) (success) *)
  Succeed time "cbv  " cbv.        (* Tactic call cbv   ran for 0. secs (0.u,0.s) (success) *)
  Succeed time "vm   " vm_compute. (* Tactic call vm    ran for 0. secs (0.u,0.s) (success) *)
  Succeed time "simpl" simpl.      (* Tactic call simpl ran for 0.062 secs (0.061u,0.s) (su *)
  Succeed time "cbn  " cbn.        (* Tactic call cbn   ran for 0.707 secs (0.706u,0.s) (su *)
  Succeed time "kred " kred.       (* Tactic call kred  ran for 0. secs (0.u,0.s) (success) *)
Abort.

(* issue #18619 *)
Fixpoint test (n : nat) (b : bool) :=
  match n with
  | 0 => if b then true else false
  | S n => test n b
  end.
Arguments test : simpl nomatch.
Goal forall b, test 5000 b = b.
Proof. intros.
  assert_succeeds ((time simpl); lazymatch goal with |- test 0 b = b => idtac end). (* 0.016s - 0.022s *)
  assert_succeeds ((time cbn);   lazymatch goal with |- test 0 b = b => idtac end). (* 3s *)
  assert_succeeds ((time kred);   lazymatch goal with |- test 0 b = b => idtac end). (* 0.003 *)
  assert_succeeds ((time lazy);   lazymatch goal with |- (if b then true else false) = b => idtac end). (* 0.002 *)
Abort.

(* issue #15720 *)
Module Import PTELE.
  Inductive tele : Type :=
  | tO : tele
  | tS {X : Type} : (X -> tele) -> tele.

  Fixpoint tele_fun (t : tele) (T: Type) : Type :=
    match t with
    | tO => T
    | tS F => forall x, tele_fun (F x) T
    end.
  Notation "t -pt> T" := (tele_fun t T)(format "t  -pt>  T", at level 99, T at level 200, right associativity).

  Module FixArgs.
  Section ArgRecord.
    #[local] Set Primitive Projections.
    Context {A : Type} {P : A -> Type}.
    Record arg := taS' { arg_hd : A; arg_tl : P arg_hd }.
  End ArgRecord.

  Record argO := taO {}.
  Arguments arg {_} _.

  (* Eeverything below is identical to code in [FixArgsNonPrim] *)
  Fixpoint tele_arg (t : tele) : Type :=
    match t return Type with
    | tO => argO
    | tS F => arg (fun x => tele_arg (F x))
    end.
  Definition taS {X F} (x : X) (a : tele_arg (F x)) : tele_arg (tS F) :=
    taS' x a.

  Fixpoint tele_app {t : tele} {T} : tele_fun t T -> tele_arg t -> T :=
    match t with
    | tO => fun f _ => f
    | tS F => fun f '(taS' x args) => tele_app (f x) args
    end.
  #[global] Arguments tele_app {!_ _} _ !_ /.

  Fixpoint tele_bind {t:tele} {T} : (tele_arg t -> T) -> t -pt> T :=
    match t with
    | tO => fun g => g taO
    | tS F => fun g x => tele_bind (fun a => g (taS x a))
    end.
  #[global] Arguments tele_bind {!_ _} _ /.

  End FixArgs.

  Module FixArgsNonPrim.

  Section ArgRecord.
    #[local] Unset Primitive Projections.
    Context {A : Type} {P : A -> Type}.
    Record arg := taS' { arg_hd : A; arg_tl : P arg_hd }.
  End ArgRecord.

  Record argO := taO {}.
  Arguments arg {_} _.

  (* Eeverything below is identical to code in [FixArgs] *)
  Fixpoint tele_arg (t : tele) : Type :=
    match t return Type with
    | tO => argO
    | tS F => arg (fun x => tele_arg (F x))
    end.
  Definition taS {X F} (x : X) (a : tele_arg (F x)) : tele_arg (tS F) :=
    taS' x a.
  #[global] Arguments taS _ _ _ & _.
  Coercion tele_arg : tele >-> Sortclass.

  Fixpoint tele_app {t : tele} {T} : tele_fun t T -> tele_arg t -> T :=
    match t with
    | tO => fun f _ => f
    | tS F => fun f '(taS' x args) => tele_app (f x) args
    end.
  #[global] Arguments tele_app {!_ _} _ !_ /.

  (** Currying telescopic functions *)
  Fixpoint tele_bind {t:tele} {T} : (t -> T) -> t -pt> T :=
    match t with
    | tO => fun g => g taO
    | tS F => fun g x => tele_bind (fun a => g (taS x a))
    end.
  #[global] Arguments tele_bind {!_ _} _ /.

  End FixArgsNonPrim.

End PTELE.

Fixpoint build_tele (n : nat) : tele :=
  match n with
  | 0 => tO
  | S n => tS (fun _ : nat => build_tele n)
  end.

Module Prim.
  Import PTELE.FixArgs.
  Fixpoint build_fn (n : nat) : build_tele n -pt> nat :=
    match n as n return build_tele n -pt> nat with
    | 0 => 0
    | S n => fun x => build_fn n
    end.

  Fixpoint add (m n : nat) (p : build_tele n -pt> nat) : build_tele n -pt> nat :=
    match m with
    | 0 => p
    | S m => tele_bind (fun x => 1 + tele_app (add m n p) x)
    end.

  (* Time Eval compute in @add 20   10 (build_fn 10). (* 0.000s *) *)
  (* Time Eval compute in @add 200  10 (build_fn 10). (* 0.005s *) *)
  (* Time Eval compute in @add 2000 10 (build_fn 10). (* 0.050s *) *)

  (* Set Debug "kred". *)
  (* Set Printing All. *)
  Time Eval kred     in @add 2    10 (build_fn 10). (* 0.s *)
  Time Eval kred     in @add 4    10 (build_fn 10). (* 0.001s *)
  Time Eval kred     in @add 8    10 (build_fn 10). (* 0.003s *)
  Time Eval kred     in @add 10   10 (build_fn 10). (* 0.008s    *)
  Time Eval kred     in @add 4000 10 (build_fn 10). (* 0.26s    *)

  (* Time Eval cbn     in @add 2    10 (build_fn 10). (* 0.004s *) *)
  (* Time Eval cbn     in @add 4    10 (build_fn 10). (* 0.040s *) *)
  (* Time Eval cbn     in @add 8    10 (build_fn 10). (* 2.400s *) *)
  (* Time Eval cbn     in @add 10   10 (build_fn 10). (* 11s    *) *)
  (* [m=20] runs out of memory after a while. *)

  (* Time Eval simpl   in @add 2    10 (build_fn 10). (* 0.003s *) *)
  (* Time Eval simpl   in @add 4    10 (build_fn 10). (* 0.030s *) *)
  (* Time Eval simpl   in @add 8    10 (build_fn 10). (* 1.800s *) *)
  (* Time Eval simpl   in @add 10   10 (build_fn 10). (* 10s    *) *)
  (* [m=20] runs out of memory after a while. *)
End Prim.

Module NonPrim.
  Import PTELE.FixArgsNonPrim.
  Fixpoint build_fn (n : nat) : build_tele n -pt> nat :=
    match n as n return build_tele n -pt> nat with
    | 0 => 0
    | S n => fun x => build_fn n
    end.

  Fixpoint add (m n : nat) (p : build_tele n -pt> nat) : build_tele n -pt> nat :=
    match m with
    | 0 => p
    | S m => tele_bind (fun x => 1 + tele_app (add m n p) x)
    end.

  Time Eval kred     in @add 2    10 (build_fn 10). (* 0.001s *)
  Time Eval kred     in @add 4    10 (build_fn 10). (* 0.002s *)
  Time Eval kred     in @add 8    10 (build_fn 10). (* 0.003s *)
  Time Eval kred     in @add 10   10 (build_fn 10). (* 0.004s *)
  Time Eval kred     in @add 20   10 (build_fn 10). (* 0.013s *)
  Time Eval kred     in @add 200  10 (build_fn 10). (* 0.04s  *)
  Time Eval kred     in @add 2000 10 (build_fn 10). (* 0.13s  *)
  Time Eval kred     in @add 4000 10 (build_fn 10). (* 0.26s  *)

  (* Time Eval compute in @add 20   10 (build_fn 10). (* 0.000s *) *)
  (* Time Eval compute in @add 200  10 (build_fn 10). (* 0.005s *) *)
  (* Time Eval compute in @add 2000 10 (build_fn 10). (* 0.050s *) *)

  (* Time Eval cbn     in @add 2    10 (build_fn 10). (* 0.001s *) *)
  (* Time Eval cbn     in @add 4    10 (build_fn 10). (* 0.003s *) *)
  (* Time Eval cbn     in @add 8    10 (build_fn 10). (* 0.006s *) *)
  (* Time Eval cbn     in @add 10   10 (build_fn 10). (* 0.008s *) *)
  (* Time Eval cbn     in @add 20   10 (build_fn 10). (* 0.016s *) *)
  (* Time Eval cbn     in @add 200  10 (build_fn 10). (* 0.17s  *) *)
  (* Time Eval cbn     in @add 2000 10 (build_fn 10). (* 3.5s   *) *)

  (* Time Eval simpl   in @add 2    10 (build_fn 10). (* 0.001s *) *)
  (* Time Eval simpl   in @add 4    10 (build_fn 10). (* 0.003s *) *)
  (* Time Eval simpl   in @add 8    10 (build_fn 10). (* 0.006s *) *)
  (* Time Eval simpl   in @add 10   10 (build_fn 10). (* 0.007s *) *)
  (* Time Eval simpl   in @add 20   10 (build_fn 10). (* 0.014s *) *)
  (* Time Eval simpl   in @add 200  10 (build_fn 10). (* 0.15s  *) *)
  (* Time Eval simpl   in @add 2000 10 (build_fn 10). (* 2.75s  *) *)
End NonPrim.
