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
