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
