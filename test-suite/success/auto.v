(* Wish #2154 by E. van der Weegen *)

(* auto was not using f_equal-style lemmas with metavariables occurring
   only in the type of an evar of the concl, but not directly in the
   concl itself *)

Parameters
  (F: Prop -> Prop)
  (G: forall T, (T -> Prop) -> Type)
  (L: forall A (P: A -> Prop), G A P -> forall x, F (P x))
  (Q: unit -> Prop).

Hint Resolve L.

Goal G unit Q -> F (Q tt).
  intro.
  eauto. 
Qed.

(* Test implicit arguments in "using" clause *)

Goal forall n:nat, nat * nat.
auto using (pair O).
Undo.
eauto using (pair O).
Qed.

Create HintDb test discriminated.

Parameter foo : forall x, x = x + 0.
Hint Resolve foo : test.

Variable C : nat -> Type -> Prop.

Variable c_inst : C 0 nat.

Hint Resolve c_inst : test.

Hint Mode C - + : test.
Hint Resolve c_inst : test2.
Hint Mode C + + : test2.

Goal exists n, C n nat.
Proof.
  eexists. Fail progress debug eauto with test2. 
  progress eauto with test.
Qed.

(** Patterns of Extern have a "matching" semantics.
    It is not so for apply/exact hints *)

Class B (A : Type).
Class I. 
Instance i : I.
  
Definition flip {A B C : Type} (f : A -> B -> C) := fun y x => f x y.
Class D (f : nat -> nat -> nat).
Definition ftest (x y : nat) := x + y.
Definition flipD (f : nat -> nat -> nat) : D f -> D (flip f).
  Admitted.
Module Instnopat.
  Local Instance: B nat.
  (* pattern_of_constr -> B nat *)
  (* exact hint *)
  Check (_ : B nat).
  (* map_eauto -> B_instance0 *)
  (* NO Constr_matching.matches !!! *)
  Check (_ : B _).

  Goal exists T, B T.
    eexists.
    eauto with typeclass_instances.
  Qed.

  Local Instance: D ftest.
  Local Hint Resolve flipD | 0 : typeclass_instances.
  (* pattern: D (flip _) *)
  Fail Timeout 1 Check (_ : D _). (* loops applying flipD *)  
  
End Instnopat.

Module InstnopatApply.
  Local Instance: I -> B nat.
  (* pattern_of_constr -> B nat *)
  (* apply hint  *)
  Check (_ : B nat).
  (* map_eauto -> B_instance0 *)
  (* NO Constr_matching.matches !!! *)
  Check (_ : B _).

  Goal exists T, B T.
    eexists.
    eauto with typeclass_instances.
  Qed.
End InstnopatApply.
  
Module InstPat.
  Hint Extern 3 (B nat) => split : typeclass_instances.
  (* map_eauto -> Extern hint *)
  (* Constr_matching.matches -> true *)
  Check (_ : B nat).
  (* map_eauto -> Extern hint *)
  (* Constr_matching.matches -> false:
     Because an inductive in the pattern does not match an evar in the goal *)
  Check (_ : B _).

  Goal exists T, B T.
    eexists.
    (* map_existential -> Extern hint *)
    (* Constr_matching.matches -> false *)
    Fail progress eauto with typeclass_instances.
    (* map_eauto -> Extern hint *)
    (* Constr_matching.matches -> false *)
    Fail typeclasses eauto.
  Abort.

  Hint Extern 0 (D (flip _)) => apply flipD : typeclass_instances.
  Module withftest.
    Local Instance: D ftest.

    Check (_ : D _).
    (* D_instance_0 : D ftest *)
    Check (_ : D (flip _)).
    (* ... : D (flip ftest) *)
  End withftest.
  Module withoutftest.
    Hint Extern 0 (D ftest) => split : typeclass_instances.
    Check (_ : D _).
    (* ? : D ?, _not_ looping *)
    Check (_ : D (flip _)).
    (* ? : D (flip ?), _not_ looping *)

    Check (_ : D (flip ftest)).
    (* flipD ftest {|  |} : D (flip ftest) *)
  End withoutftest.
End InstPat.
