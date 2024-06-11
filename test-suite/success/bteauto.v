(* coq-prog-args: ("-async-proofs" "off") *)
Require Import Program.Tactics.
Module Backtracking.
  Class A := { foo : nat }.

  #[global] Instance A_1 : A | 2 := { foo := 42 }.
  #[global] Instance A_0 : A | 1 := { foo := 0 }.
  Lemma aeq (a : A) : foo = foo.
    reflexivity.
  Qed.
  
  Arguments foo A : clear implicits.
  Example find42 : exists n, n = 42.
  Proof.
    eexists.
    eapply eq_trans.
    evar (a : A). subst a.
    refine (@aeq ?a).
    Unshelve. all:cycle 1.
    typeclasses eauto.
    Fail reflexivity. 
    Undo 1.
    (* Without multiple successes it fails *)
    Set Typeclasses Debug Verbosity 2.
    Fail all:((once (typeclasses eauto with typeclass_instances))
              + apply eq_refl).
    (* Does backtrack if other goals fail *)
    all:[> typeclasses eauto + reflexivity .. ].
    Undo 1.
    all:(typeclasses eauto + reflexivity). (* Note "+" is a focussing combinator *)
    Show Proof.  
  Qed.

  Print find42.
  
  #[global] Hint Extern 0 (_ = _) => reflexivity : equality.
  
  Goal exists n, n = 42.
    eexists.
    eapply eq_trans.
    evar (a : A). subst a.
    refine (@aeq ?a).
    Unshelve. all:cycle 1.
    typeclasses eauto.
    Fail reflexivity.
    Undo 1.
    
    (* Does backtrack between individual goals *)
    Set Typeclasses Debug.
    all:(typeclasses eauto with typeclass_instances equality).
  Qed.
  
  Unset Typeclasses Debug.

  Module Leivant.
    Axiom A : Type.
    Existing Class A.
    Axioms a b c d e: A.
    #[global] Existing Instances a b c d e.
    
    Ltac get_value H := eval cbv delta [H] in H.
    
    Goal True.
      Fail refine (let H := _ : A in _); let v := get_value H in idtac v; fail.
    Admitted.

    Goal exists x:A, x=a.
      unshelve evar (t : A). all:cycle 1.
      refine (@ex_intro _ _ t _).
      all:cycle 1.
      all:(typeclasses eauto + reflexivity).
    Qed.      
  End Leivant.
End Backtracking.


#[export] Hint Resolve eq_sym eq_trans | 100 : core.
#[export] Hint Cut [(_)* eq_sym eq_sym] : core.
#[export] Hint Cut [_* eq_trans eq_trans] : core.
#[export] Hint Cut [_* eq_trans eq_sym eq_trans] : core.


Goal forall x y z : nat, x = y -> z = y -> x = z.
Proof.
  intros.
  typeclasses eauto with core.
Qed.

Module Hierarchies.
  Class A := mkA { data : nat }.
  Class B := mkB { aofb :: A }.

  #[export] Existing Instance mkB.

  Definition makeB (a : A) : B := _.
  Definition makeA (a : B) : A := _.

  Fail Timeout 1 Definition makeA' : A := _.

  #[export] Hint Cut [_* mkB aofb] : typeclass_instances.
  Fail Definition makeA' : A := _.
  Fail Definition makeB' : B := _.
End Hierarchies.

(** Hint modes *)

Class Equality (A : Type) := { eqp : A -> A -> Prop }.

Check (eqp 0%nat 0).

#[export] Instance nat_equality : Equality nat := { eqp := eq }.

#[export] Instance default_equality A : Equality A | 1000 :=
  { eqp := eq }.

Check (eqp 0%nat 0).

(* Defaulting *)
Check (fun x y => eqp x y).
(* No more defaulting, reduce "trigger-happiness" *)
Definition ambiguous x y := eqp x y.

#[export] Hint Mode Equality ! : typeclass_instances.
Fail Definition ambiguous' x y := eqp x y.
Definition nonambiguous (x y : nat) := eqp x y.

(** Typical looping instances with defaulting: *)
Definition flip {A B C} (f : A -> B -> C) := fun x y => f y x.

Class SomeProp {A : Type} (f : A -> A -> A) :=
  { prf : forall x y, f x y = f x y }.

#[export] Instance propflip (A : Type) (f : A -> A -> A) :
  SomeProp f -> SomeProp (flip f).
Proof.
  intros []. constructor. reflexivity.
Qed.

Fail Timeout 1 Check prf.

#[export] Hint Mode SomeProp + + : typeclass_instances.
Check prf.
Check (fun H : SomeProp plus => _ : SomeProp (flip plus)).

(** Iterative deepening / breadth-first search *)

Module IterativeDeepening.

  Class A.
  Class B.
  Class C.

  #[export] Instance: B -> A | 0 := {}.
  #[export] Instance: C -> A | 0 := {}.
  #[export] Instance: C -> B -> A | 0 := {}.
  #[export] Instance: A -> A | 0 := {}.
  
  Goal C -> A.
    intros.
    Fail Timeout 1 typeclasses eauto.
    Set Typeclasses Iterative Deepening.
    Fail typeclasses eauto 1.
    typeclasses eauto 2.
    Undo.
    Unset Typeclasses Iterative Deepening.
    Fail Timeout 1 typeclasses eauto.
    Set Typeclasses Iterative Deepening.
    Typeclasses eauto := debug 3.
    typeclasses eauto.
  Qed.

End IterativeDeepening.
