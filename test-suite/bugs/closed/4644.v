(* Testing a regression of unification in 8.5 in problems of the form
   "match ?y with ... end = ?x args" *)

Lemma foo : exists b, forall a, match a with tt => tt end = b a.
Proof.
eexists. intro.
refine (_ : _ = match _ with tt => _ end).
refine eq_refl.
Qed.

(**********************************************************************)

Axiom proof_admitted : False.
Tactic Notation "admit" := case proof_admitted.
Require Export Coq.Classes.Morphisms.
Require Import Coq.Lists.List.

Global Set Implicit Arguments.

Definition list_caset A (P : list A -> Type) (N : P nil) (C : forall x xs, P (x::xs))
           ls
  : P ls
  := match ls with
     | nil => N
     | x::xs => C x xs
     end.

Axiom list_caset_Proper'
  : forall {A P},
    Proper (eq
              ==> pointwise_relation _ (pointwise_relation _ eq)
              ==> eq
              ==> eq)
           (@list_caset A (fun _ => P)).
Goal forall (T T' : Set) (a3 : list T), exists y2, forall (a4 : T' -> bool),
        match a3 with
        | nil => 0
        | (_ :: _)%list => 1
        end = y2 a4.
  clear; eexists; intros.
  reflexivity. Undo.
  Local Ltac t :=
    lazymatch goal with
    | [ |- match ?v with nil => ?N | cons x xs => @?C x xs end = _ :> ?P ]
      => let T := type of v in
         let A := match (eval hnf in T) with list ?A => A end in
         refine (@list_caset_Proper' A P _ _ _ _ _ _ _ _ _
                 : @list_caset A (fun _ => P) N C v = match _ with nil => _ | cons x xs => _ end)
    end.
  (etransitivity; [ t | reflexivity ]) || fail 0 "too early".
  Undo.
  t.
