Require Import TestSuite.admit.
(* File reduced by coq-bug-finder from original input, then from 716 lines to 197 lines, then from 206 lines to 162 lines, then from 163 lines to 73 lines *)
Require Import Coq.Sets.Ensembles.
Require Import Coq.Strings.String.
Global Set Implicit Arguments.
Global Set Asymmetric Patterns.
Ltac clearbodies := repeat match goal with | [ H := _ |- _ ] => clearbody H end.

Inductive Comp : Type -> Type :=
| Return : forall A, A -> Comp A
| Bind : forall A B, Comp A -> (A -> Comp B) -> Comp B.
Inductive computes_to : forall A, Comp A -> A -> Prop :=
| ReturnComputes : forall A v, @computes_to A (Return v) v
| BindComputes : forall A B comp_a f comp_a_value comp_b_value,
                   @computes_to A comp_a comp_a_value
                   -> @computes_to B (f comp_a_value) comp_b_value
                   -> @computes_to B (Bind comp_a f) comp_b_value.

Inductive is_computational : forall A, Comp A -> Prop :=
| Return_is_computational : forall A (x : A), is_computational (Return x)
| Bind_is_computational : forall A B (cA : Comp A) (f : A -> Comp B),
                            is_computational cA
                            -> (forall a,
                                  @computes_to _ cA a -> is_computational (f a))
                            -> is_computational (Bind cA f).
Theorem is_computational_inv A (c : Comp A)
: is_computational c
  -> match c with
       | Return _ _ => True
       | Bind _ _ x f => is_computational x
                         /\ forall v, computes_to x v
                                      -> is_computational (f v)
     end.
  admit.
Defined.
Fixpoint is_computational_unique_val A (c : Comp A) {struct c}
: is_computational c -> { a | unique (computes_to c) a }.
Proof.
  refine match c as c return is_computational c -> { a | unique (computes_to c) a } with
           | Return T x => fun _ => exist (unique (computes_to (Return x)))
                                          x
                                          _
           | Bind _ _ x f
             => fun H
                => let H' := is_computational_inv H in
                   let xv := @is_computational_unique_val _ _ (proj1 H') in
                   let fxv := @is_computational_unique_val _ _ (proj2 H' _ (proj1 (proj2_sig xv))) in
                   exist (unique (computes_to _))
                         (proj1_sig fxv)
                         _
         end;
  clearbodies;
  clear is_computational_unique_val;
  clear;
  first [ abstract admit
        | abstract admit ].
(* [Fail] does not catch the anomaly *)
Defined.
(* Anomaly: Uncaught exception Not_found(_). Please report. *)
