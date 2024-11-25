Require Import Corelib.Classes.Morphisms.
Require Import Corelib.Setoids.Setoid.

Definition T := nat.
Axiom MT : Type.
Axiom ret : T -> MT.
Axiom bind : MT -> (T -> MT) -> MT.
Axiom bind_bind : forall x f1 f2, bind (bind x f1) f2 = bind x (fun x => bind (f1 x) f2).
Axiom bind_ret : forall x f, bind (ret x) f = f x.
Reserved Notation "A <- X ; B" (at level 70, X at next level, right associativity, format "'[v' A  <-  X ; '/' B ']'").
Notation "v <- x ; f" := (bind x (fun v => f)).
Axiom bind_Proper : Proper (eq ==> (eq ==> eq) ==> eq) bind.
Axiom bind_Proper' : Proper (eq ==> pointwise_relation _ eq ==> eq) bind.
#[export] Existing Instances bind_Proper bind_Proper'.

Module Thunked.
  Definition nat_rect P (O_case : unit -> P) (S_case : nat -> P -> P) (n : nat) : P
    := Datatypes.nat_rect (fun _ => P) (O_case tt) S_case n.
End Thunked.

Definition make_binds_assoc_def (n : nat) (v : MT) :=
  @Thunked.nat_rect
    MT
    (fun _ => v)
    (fun _ rec => bind rec (fun x => ret x))
    n.

Lemma foo :
  let n := 2%nat in
  forall v, make_binds_assoc_def n v = make_binds_assoc_def n v.
Proof.
  cbv [make_binds_assoc_def].
  intros.
  rewrite_strat ((eval cbv [Thunked.nat_rect nat_rect]); (topdown bind_bind)).
  reflexivity.
Qed.
