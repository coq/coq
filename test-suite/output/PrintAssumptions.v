
(** Print Assumption and opaque modules :

  Print Assumption used to consider as axioms the modular fields
  unexported by their signature, cf bug report #2186. This should
  now be fixed, let's test this here. *)

(* First, a minimal test-case *)

Axiom foo : nat.

Module Type T.
 Parameter bar : nat.
End T.

Module M : T.
  Module Hide. (* An entire sub-module could be hidden *)
  Definition x := foo.
  End Hide.
  Definition bar := Hide.x.
End M.

Module N (X:T) : T.
  Definition y := X.bar. (* A non-exported field *)
  Definition bar := y.
End N.

Module P := N M.

Print Assumptions M.bar. (* Should answer: foo *)
Print Assumptions P.bar. (* Should answer: foo *)

(* Print Assumptions used empty instances on polymorphic inductives *)
Module Poly.

  Set Universe Polymorphism.
  Axiom bli : Type.

  Definition bla := bli -> bli.

  Inductive blo : bli -> Type := .

  Print Assumptions bla.
  Print Assumptions blo.

End Poly.

Module UIP.
  Set Definitional UIP.

  Inductive seq {A} (a:A) : A -> SProp :=
    srefl : seq a a.
  Arguments srefl {_ _}.

  Definition eq_to_seq {A x y} (e:x = y :> A) : seq x y
    := match e with eq_refl => srefl end.
  Definition seq_to_eq {A x y} (e:seq x y) : x = y :> A
    := match e with srefl => eq_refl end.

  Definition norm {A x y} (e:x = y :> A) : x = y
    := seq_to_eq (eq_to_seq e).

  Definition norm_id {A x y} (e:x = y :> A) : norm e = e
    := match e with eq_refl => eq_refl end.

  Theorem UIP {A x y} (e e':x = y :> A) : e = e'.
  Proof.
    rewrite <-(norm_id e), <-(norm_id e').
    reflexivity.
  Defined.

  Print Assumptions UIP.
End UIP.

(** Print Assumption and Include *)

Module INCLUDE.

Module M.
Axiom foo : False.
End M.

Module N.
Include M.
End N.

Print Assumptions N.foo.

End INCLUDE.

(* Print Assumptions did not enter implementation of submodules (#7192) *)

Module SUBMODULES.

Definition a := True.
Module Type B. Axiom f : Prop. End B.
Module Type C. Declare Module D : B. End C.
Module E: C.
  Module D <: B. Definition f := a. End D.
End E.
Print Assumptions E.D.f.

(* Idem in the scope of a functor *)

Module Type T. End T.
Module F (X : T).
  Definition a := True.
  Module Type B. Axiom f : Prop. End B.
  Module Type C. Declare Module D : B. End C.
  Module E: C.
    Module D <: B. Definition f := a. End D.
  End E.
  Print Assumptions E.D.f.
End F.

End SUBMODULES.

(* Testing a variant of #7192 across files *)
(* This was missing in the original fix to #7192 *)
Require Import module_bug7192.
Print Assumptions M7192.D.f.

(* Testing reporting assumptions from modules in files *)
(* A regression introduced in the original fix to #7192 was missing implementations *)
Require Import module_bug8416.
Print Assumptions M8416.f.
