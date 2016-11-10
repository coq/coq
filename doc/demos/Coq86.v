(** This file introduces the new features of Coq 8.6 *)

From Coq Require Import Arith List Omega Bool Program.Tactics.
  
(** * Fine grained error-reporting and error processing, in structured scripts *)

(* In CoqIDE, Coqoon, PG-XML proof blocks confine errors hence Coq can continue to
   process the structured proof *)

(* Lemma failing_branch : False /\ True. *)
(* Proof. *)
(* split. *)
(*   { exact I. }  (* This branch fails, but Coq does not give up *) *)
(*   { exact I. }  (* This branch is executed, can be edited, etc... *) *)
(* Qed. *)

(* This behavior can be disabled, see "error resiliency" command line flags *)

(** Multi-goal, multi-success typeclasses eauto engine See
    Coq86typeclasses for a more detailed demonstration. *)

Class pred (n : nat) : Prop := {}.
Instance pred0 : pred 0 := {}.
(** pred1 has priority over pred0 *)
Instance pred1 : pred 1 := {}.
Class pred2 (n : nat) : Prop := {}.
(** There is not [pred2 1] instance *)
Instance pred20 : pred2 0 := {}.

Goal exists x : nat, pred x /\ pred2 x.
  eexists. split.
  (** The resolution can backtrack across goals, *)
  Set Typeclasses Debug.
  (** Here using two different calls to resolution on two different
      goals, using the multiple successes of the first call to find
      pred0 *)
  all:[> typeclasses eauto .. ].
  Undo.
  (** Here using a multi-goal call *)
  all:typeclasses eauto.
  Show Proof.  
Qed.

(** Goal selectors *)

Goal exists n : nat, pred n /\ pred2 n /\ True.
  eexists.
  split; [|split].
  (** Applies the multi-goal tactic to the list of goals *)
  1-2:typeclasses eauto.
  exact I.
  Undo 2.
  2-3:cycle 1.
  1,3:typeclasses eauto.
  (* Same result, selection of non-contiguous range *)
  exact I.
Qed.

(** Warnings *)

Set Warnings "all". 
Test Warnings.

(** Turns unknown warning into an error *)
Set Warnings "+unknown-warning". 
Test Warnings.

Fail Set Warnings "bla".

(** Turns it back into a warning *)
Set Warnings "unknown-warning". 
Test Warnings.

Set Warnings "bla".

(** What is the semantics of all,default? *)
Set Warnings "default".
Test Warnings.

Print Warnings.
Print Warnings "numbers".
Print Warnings "numbers":"large-nat".
Set Warnings "+large-nat".
Print Warnings "numbers":"large-nat".

(** Irrefutable patterns *)

Module IrrefutablePatterns.
  
  Definition fst {A B} '((a, b) : _ * B) : A := a.
  Definition snd {A B} '((a, b) : A * B) := b.
  
  Record myrec := makemy { somebool : bool; somenat : nat }.
         
  Lemma eta_my : forall '(makemy b n), b = true \/ b = false.
    intros [[|] n]; auto.
  Qed.

  Definition map_pair (l : list (nat * nat)) : list nat :=
    map (fun '(pair x _) => x) l.
  
End IrrefutablePatterns.

(** Ltacprof *)

(** Cleaner generic arguments *)

Module GenericArguments.

End GenericArguments.

(** Keyed Unification *)

Module KeyedUnification.
  (** The purpose of Keyed Unification is to allow [rewrite] to see subterms to rewrite
      up to controlable reduction. The strategy is to match the lhs or rhs of the lemma 
      with a subterm in the goal or hypothesis, by finding an applicative subterm whose
      head is equivalent to the head in the lemma and the use full unification on the 
      arguments, whether they are closed or not. *)
  Set Keyed Unification.
  
  Section foo.
    Variable f : nat -> nat. 
    
    Definition g := f.
    
    Variable lem : g 0 = 0.
    
    Goal f 0 = 0.
    Proof.
      Fail rewrite lem.
      (** Found no subterm matching "g 0" in the current goal. *)
    Abort.

    Declare Equivalent Keys @g @f.
    (** Now f and g are considered equivalent heads for subterm selection *)
    Goal f 0 = 0.
    Proof.
      rewrite lem.
      reflexivity.
    Qed.
    
    Print Equivalent Keys.
  End foo.
End KeyedUnification.
  
(** Unification constraint handling *)

Module UnifConstraints.

  (** This option governs the automating solving of remaining unification constraints
      at each ".". Unification can use heuristics to solve these remaining constraints. *)
  Set Solve Unification Constraints. (* The default *)
  
  Goal forall n : nat, True /\ True /\ True \/ n = n.
    (** This higher-order unification constraint does not have a unique solution. *)
    intros n. Fail refine (nat_rect _ _ _ n).
    Unset Solve Unification Constraints.
    (** This lets the constraint float. *)
    refine (nat_rect _ _ _ n).
    (** This forces constraint solving, here failing *)
    Fail solve_constraints.
    (** If we remove the spurious dependency of the predicate on [n]: *)
    Undo 2.
    simple refine (nat_rect _ _ _ n). (* simple refine does not shelve dependent subgoals *)
    Set Printing Existential Instances.
    clear n. intros n. (* We must use an intro here to let the unifier solve 
                          the higher-order problem *)
    solve_constraints.
    all:simpl.
  Admitted.
End UnifConstraints.
