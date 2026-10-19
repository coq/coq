(* One object under two user names (a module alias, Include, a functor that
   returns or includes its argument, an ascription) has one entry per user name
   in the output, as the walk without reuse reports it: the second query of
   each pair replays the type of an axiom that names both. A functor
   application that defines its own constants gives another canonical name and
   is not such a case. *)

(* Alias, a fixpoint assumed guarded. *)
Module N1.
  Unset Guard Checking.
  Fixpoint f (n : nat) : nat := f n.
  Set Guard Checking.
End N1.
Module M1 := N1.
Axiom b1 : M1.f = N1.f.
Print Assumptions b1.
Print Assumptions b1.

(* Include. *)
Module K2.
  Include N1.
End K2.
Axiom c2 : N1.f = K2.f.
Print Assumptions c2.
Print Assumptions c2.

(* Attribute, both names under one type. *)
Module M3.
  #[bypass_check(guard)] Fixpoint f (n : nat) : nat := f n.
End M3.
Module MA3 := M3.
Axiom X3 : (fun _ _ : nat => nat) (M3.f 0) (MA3.f 0).
Definition d3 : nat := X3.
Print Assumptions X3.
Print Assumptions d3.

(* The two names in two axioms reached by one replay. *)
Module M4. Definition c : nat := 0. End M4.
Module MA4 := M4.
Axiom X4a : (fun _ : nat => nat) M4.c.
Axiom X4b : (fun _ : nat => nat) MA4.c.
Definition d4 : nat := X4a + X4b.
Print All Dependencies d4.
Print All Dependencies d4.

(* An inductive assumed positive. *)
Module V5.
  #[bypass_check(positivity)] Inductive I : Type := C : (I -> nat) -> I.
End V5.
Module X5. Include V5. End X5.
Axiom b5 : V5.I -> X5.I -> nat.
Print Assumptions b5.
Print Assumptions b5.

(* Functor applications and ascription whose result has the canonical name of
   its argument's field: a functor returning its argument, a functor including
   its argument, and an ascription. *)
Module Type U. Unset Guard Checking. Fixpoint g (n : nat) : nat := g n. Set Guard Checking. End U.
Module P6. Unset Guard Checking. Fixpoint g (n : nat) : nat := g n. Set Guard Checking. End P6.
Module G (A : U) := A.
Module Q6 := G P6.
Axiom X6 : P6.g = Q6.g.
Print Assumptions X6.
Print Assumptions X6.
Module H (A : U). Include A. End H.
Module Q7 := H P6.
Axiom X7 : P6.g = Q7.g.
Print Assumptions X7.
Print Assumptions X7.
Module Q8 <: U := P6.
Axiom X8 : P6.g = Q8.g.
Print Assumptions X8.
Print Assumptions X8.
