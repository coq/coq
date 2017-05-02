(* -*- mode: coq; coq-prog-args: ("-R" "." "Fiat" "-top" "BooleanRecognizerOptimized" "-R" "." "Top") -*- *)
(* File reduced by coq-bug-finder from original input, then from 2407 lines to 22 lines, then from 528 lines to 35 lines, then from 331 lines to 42 lines, then from 56 lines to 42 lines, then from 63 lines to 46 lines, then from 60 lines to 46 lines *) (* coqc version 8.5 (February 2016) compiled on Feb 21 2016 15:26:16 with OCaml 4.02.3
   coqtop version 8.5 (February 2016) *)
Axiom proof_admitted : False.
Tactic Notation "admit" := case proof_admitted.
Require Coq.Lists.List.
Import Coq.Lists.List.
Import Coq.Classes.Morphisms.

Definition list_caset A (P : list A -> Type) (N : P nil) (C : forall x xs, P (x::xs))
           ls
  : P ls
  := match ls with
     | nil => N
     | x::xs => C x xs
     end.

Global Instance list_caset_Proper' {A P}
  : Proper (eq
              ==> pointwise_relation _ (pointwise_relation _ eq)
              ==> eq
              ==> eq)
           (@list_caset A (fun _ => P)).
admit.
Defined.

Global Instance list_caset_Proper'' {A P}
  : (Proper (eq ==> pointwise_relation _ (pointwise_relation _ eq) ==> forall_relation (fun _ => eq))
   (list_caset A (fun _ => P))).
Admitted.

Goal    forall (Char : Type) (P : forall _ : list bool, Prop) (l : list bool) (l0 : forall _ : forall _ : Char, bool, list bool)
               
               (T : Type) (T0 : forall _ : T, Type) (t : T),
    
    let predata := t in

    forall (splitdata : T0 predata) (l5 : forall _ : T0 t, list nat) (T1 : Type) (b : forall (_ : T1) (_ : Char), bool)
           
           (T2 : Type) (a11 : T2) (xs : list T2) (T3 : Type) (i0 : T3) (P0 : Set) (b1 : forall (_ : nat) (_ : P0), bool)
           
           (l2 : forall (_ : forall _ : T1, list bool) (_ : forall _ : P0, list bool) (_ : T2), list bool)
           
           (l1 : forall (_ : forall _ : forall _ : Char, bool, list bool) (_ : forall _ : P0, list bool) (_ : T3), list bool)
           
           (_ : forall NT : forall _ : P0, list bool, @eq (list bool) (l1 l0 NT i0) (l2 (fun f : T1 => l0 (b f)) NT a11)),
      
      P
        (@list_caset T2 (fun _ : list T2 => list bool) l
                     (fun (_ : T2) (_ : list T2) => l1 l0 (fun a9 : P0 => @map nat bool (fun x0 : nat => b1 x0 a9) (l5 splitdata)) i0
) xs).
  intros.
  subst predata;
  let H := match goal with H : forall _, _ = _ |- _ => H end in
  setoid_rewrite H || fail 0 "too early".
  Undo.
  setoid_rewrite H.
