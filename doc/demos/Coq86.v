(** This file introduces the new features of Coq 8.6 *)

From Coq Require Import Arith List Omega Bool Program.Tactics.
  
(** Fine grained error-reporting and error processing, in structured scripts *)

(** Multi-goal, multi-success typeclasses eauto engine *)

Module Typeclasses.
  Module Backtracking.
    Class A := { foo : nat }.
    
    Instance A_1 : A | 2 := { foo := 42 }.
    Instance A_0 : A | 1 := { foo := 0 }.
    Lemma aeq (a : A) : foo = foo.
      reflexivity.
    Qed.
    (** Declare [eq] as a class so that typeclass resolution considers it *)
    Existing Class eq.

    (** A_0 has priority, but its foo field is not equal to 42 *)
    Arguments foo A : clear implicits.
    Example find42 : exists n, n = 42.
    Proof.
      eexists. etransitivity.
      (** [notypeclasses refine] does not run typeclass resolution, so we can 
          see what typeclass constraints are necessary. 
          ?[a] declares an evar a of type A *)
      notypeclasses refine (@aeq ?[a]).
      (** We find A_0 *)
      typeclasses eauto.
      (** This can't work as [foo A_0 = 0] *)
      Fail reflexivity. 
      Undo 2.
      (* Without multiple successes it fails as it finds A_0 again but cannot backtrack on it
         ([once] prevents backtracking) *)
      Set Typeclasses Debug.
      Fail all:((once (typeclasses eauto))
                + apply eq_refl).
      (* It does backtrack if other goals fail *)
      all:[> typeclasses eauto + reflexivity .. ].
      Show Proof.  
    Qed.

    Hint Extern 0 (_ = _) => reflexivity : equality.
    
    Goal exists n, n = 42.
      eexists. etransitivity.
      notypeclasses refine (@aeq ?[a]).
      typeclasses eauto.
      Fail reflexivity.
      Undo 2.
      
      (* Does backtrack between individual goals *)
      Set Typeclasses Debug.
      all:(typeclasses eauto with typeclass_instances equality).
    Qed.
    
    Unset Typeclasses Debug.
    
  End Backtracking.

  Module HintCut.
    (** Hint Cuts *)
    
    Hint Resolve 100 eq_sym eq_trans : core.
    Goal forall x y z : nat, x = y -> z = y -> x = z.
    Proof.
      intros.
      Fail Timeout 1 typeclasses eauto with core.
    Abort.
    
    (** These proof search paths are automatically discarded *)
    Hint Cut [(_)* eq_sym eq_sym] : core.
    Hint Cut [_* eq_trans eq_trans] : core.
    Hint Cut [_* eq_trans eq_sym eq_trans] : core.
    
    Goal forall x y z : nat, x = y -> z = y -> x = z.
    Proof.
      intros.
      typeclasses eauto with core.
    Qed.

    (** Useful for hierarchies *)
    Module Hierarchies.

      Class A := mkA { data : nat }.
      Class B := mkB { aofb :> A }.
      
      Existing Instance mkB.
      
      Definition makeB (a : A) : B := _.
      Definition makeA (a : B) : A := _.
      
      Fail Timeout 1 Definition makeA' : A := _.

      (** Both the constructor and the projections can be declared as instances
          without leading to divergence *)
      Hint Cut [_* mkB aofb] : typeclass_instances.
      Fail Definition makeA' : A := _.
      Fail Definition makeB' : B := _.
    End Hierarchies.
  End HintCut.

  Module HintModes.
    (** Hint modes *)
    
    Class Equality (A : Type) := { eqp : A -> A -> Prop }.
    
    Check (eqp 0%nat 0).
    
    Instance nat_equality : Equality nat := { eqp := eq }.
    
    Instance default_equality A : Equality A | 1000 :=
      { eqp := eq }.
    
    Check (eqp 0%nat 0).
    
    (* Defaulting *)
    Check (fun x y => eqp x y).
    (* No more defaulting, reduce "trigger-happiness" *)
    Definition ambiguous x y := eqp x y.
    
    (** This says that to start resolution for an Equality t constraint,
        t's head must _not_ be an evar *)
    Hint Mode Equality ! : typeclass_instances.
    Fail Definition ambiguous' x y := eqp x y.
    Definition nonambiguous (x y : nat) := eqp x y.
  
    (** Typical looping instances with defaulting: *)
    Definition flip {A B C} (f : A -> B -> C) := fun x y => f y x.
    
    Class SomeProp {A : Type} (f : A -> A -> A) :=
      { prf : forall x y, f x y = f x y }.
    
    (** This is dangerous as [flip f] is unifiable with an evar or even
        a term with a deep evar. *)
    Instance propflip (A : Type) (f : A -> A -> A) :
      SomeProp f -> SomeProp (flip f).
    Proof.
      intros []. constructor. reflexivity.
    Qed.

    (** This applies propflip indefinitely *)
    Fail Timeout 1 Check prf.
    
    (** Now we ask for the indexes of the typeclass to be evar free to
        trigger resolution *)
    Hint Mode SomeProp + + : typeclass_instances.

    (** No resolution done *)
    Check prf.
    (** We have enough info to trigger propflip *)
    Check (fun H : SomeProp plus => _ : SomeProp (flip plus)).
  End HintModes.

  (** Iterative deepening / breadth-first search *)

  Module IterativeDeepening.

    Class A := {}.
    Class B := {}.
    Class C := {}.
      
    Instance: B -> A | 0 := {}.
    Instance: C -> A | 0 := {}.
    Instance: C -> B -> A | 0 := {}.
    Instance: A -> A | 0 := {}.
  
    Goal C -> A.
      intros.
      (** This diverges in depth-first search *)
      Fail Timeout 1 typeclasses eauto.
      (** In breadth-first search (implemented by iterative deepening) *)
      Set Typeclasses Iterative Deepening.
      (** It fails at depth 1 *)
      Fail typeclasses eauto 1.
      (** Succeeds at depth 2 *)
      typeclasses eauto 2.
      Undo.
      (** Or any other depth *)
      typeclasses eauto.
    Qed.

  End IterativeDeepening.
End Typeclasses.

(** Goal selectors *)

(** Warnings *)

(** Irrefutable patterns *)

(** Ltacprof *)

(** Cleaner generic arguments *)

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
  
  Definition G {A} (f : A -> A -> A) (x : A) := f x x.
  
  Lemma list_foo A (l : list A) : G (@app A) (l ++ nil) = G (@app A) l.
  Proof. unfold G; rewrite app_nil_r; reflexivity. Qed.
  
  (* Bundled version of a magma *)
  Structure magma := Magma { b_car :> Type; op : b_car -> b_car -> b_car }.
  Arguments op {_} _ _.
  
  (* Instance for lists *)
  Canonical Structure list_magma A := Magma (list A) (@app A).
  
  (* Basically like list_foo, but now uses the op projection instead of app for
     the argument of G *)
  Lemma test1 A (l : list A) : G op (l ++ nil) = G op l.

    (* Ensure that conversion of terms with evars is allowed once a keyed candidate unifier is found *)
    rewrite -> list_foo.
    reflexivity.
  Qed.

  (* Basically like list_foo, but now uses the op projection for everything *)
  Lemma test2 A (l : list A) : G op (op l nil) = G op l.
  Proof.
    rewrite ->list_foo.
    reflexivity.
  Qed.

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
    clear n. intros n. (* We must use an intro here to let the unifier solve 
                          the higher-order problem *)
    solve_constraints.
    all:simpl.
  Admitted.
End UnifConstraints.

(** Compatibility options *)

(** The options to make code compatible with Coq 8.5 are the following 
  (loaded by -compat 8.5).
*)

(** We use some deprecated options in this file, so we disable the
    corresponding warning, to silence the build of this file. *)
Local Set Warnings "-deprecated-option".

(* In 8.5, "intros [|]", taken e.g. on a goal "A\/B->C", does not
   behave as "intros [H|H]" but leave instead hypotheses quantified in
   the goal, here producing subgoals A->C and B->C. *)

Global Unset Bracketing Last Introduction Pattern.

(** Subst has some irregularities *)

Global Unset Regular Subst Tactic.

(** Injection does not ?? *)
Global Unset Structural Injection.

(** [abstract]ed proofs and Program obligations were not shrinked.
  Shrinking removes abstractions by unused variables in these cases *)
Global Unset Shrink Abstract.
Global Unset Shrink Obligations.

(** Refolding was used not only by [cbn] but also during unification,
  resulting in blowups sometimes. *)
Global Set Refolding Reduction.

(** The resolution algorithm for type classes has changed. *)
Global Set Typeclasses Legacy Resolution.

(** The resolution algorithm tried to limit introductions (and hence
  eta-expansions). Can be very expensive as well *)
Global Set Typeclasses Limit Intros.

(** The unification strategy for typeclasses eauto has changed, 
  Filtered Unification is not on by default in 8.6 though. *)
Global Unset Typeclasses Filtered Unification.

(** Allow silently letting unification constraints float after a ".", now
  disallowed by default (one gets unification errors instead) *)
Global Unset Solve Unification Constraints.
