Axiom magic:False.

(* Submitted by Dachuan Yu (bug #220) *)
Fixpoint T[n:nat] : Type := 
 Cases n of 
 | O => (nat -> Prop) 
 | (S n') => (T n') 
 end. 
Inductive R : (n:nat)(T n) -> nat -> Prop := 
  | RO : (Psi:(T O); l:nat) 
          (Psi l) -> (R O Psi l) 
  | RS : (n:nat; Psi:(T (S n)); l:nat) 
          (R n Psi l) -> (R (S n) Psi l). 
Definition Psi00 : (nat -> Prop) := [n:nat] False. 
Definition Psi0 : (T O) := Psi00. 
Lemma Inversion_RO : (l:nat)(R O Psi0 l) -> (Psi00 l).
Inversion 1.
Abort.

(* Submitted by Pierre Casteran (bug #540) *)

Set Implicit Arguments.
Parameter rule: Set -> Type.

Inductive extension [I:Set]:Type :=
 NL : (extension I) 
|add_rule : (rule I)  -> (extension I)  -> (extension I).


Inductive in_extension [I :Set;r: (rule I)] : (extension I)  -> Type :=
 in_first : (e:?)(in_extension r (add_rule r e))
|in_rest : (e,r':?)(in_extension r e) -> (in_extension r (add_rule r' e)).

Implicits NL [1].

Inductive super_extension [I:Set;e :(extension I)] : (extension I)  -> Type :=
 super_NL   : (super_extension   e NL)
| super_add : (r:?)(e': (extension I))
                 (in_extension  r e) ->
                 (super_extension  e e') ->
                 (super_extension  e (add_rule r e')). 



Lemma super_def : (I :Set)(e1, e2: (extension I))
                 (super_extension  e2 e1) ->
                 (ru:?) 
                   (in_extension ru e1) ->
                   (in_extension ru e2).
Proof.                 
 Induction 1.
 Inversion 1; Auto.
 Elim magic.
Qed.

(* Example from Norbert Schirmer on Coq-Club, Sep 2000 *)

Unset Implicit Arguments.
Definition Q[n,m:nat;prf:(le n m)]:=True.
Goal (n,m:nat;H:(le (S n) m))(Q (S n) m H)==True.
Intros.
Dependent Inversion_clear H.
Elim magic.
Elim magic.
Qed.

(* Submitted by Boris Yakobowski (bug #529) *)
(* Check that Inversion does not fail due to unnormalized evars *)

Set Implicit Arguments.
Require Import Bvector.

Inductive I : nat -> Set :=
| C1 : (I (S O))
| C2 : (k,i:nat)(vector (I i) k) -> (I i).

Inductive SI : (k:nat)(I k) -> (vector nat k) -> nat -> Prop :=
| SC2 : (k,i,vf:nat) (v:(vector (I i) k))(xi:(vector nat i))(SI (C2 v) xi vf).

Theorem SUnique : (k:nat)(f:(I k))(c:(vector nat k))
(v,v':?) (SI f c v) -> (SI f c v') -> v=v'.
Proof.
NewInduction 1.
Intros H ; Inversion H.
Admitted.

(* Used to failed at some time *)

Parameter bar : (p,q:nat) p=q -> Prop.
Inductive foo : nat -> nat -> Prop := 
  C : (a,b:nat)(Heq:a = b) (bar a b Heq) -> (foo a b).
Lemma depinv : (a,b:?) (foo a b) -> True.
Intros a b H.
Inversion H.
Abort.
