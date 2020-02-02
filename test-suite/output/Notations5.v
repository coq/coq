Module AppliedTermsPrinting.

(* Test different printing paths for applied terms *)

  Module InferredGivenImplicit.
  Set Implicit Arguments.
  Set Maximal Implicit Insertion.

  Axiom p : forall A (a1 a2:A) B (b:B), a1 = a2 /\ b = b.

  Check p 0 0 true.
  (* p 0 0 true *)
  Check p 0 0.
  (* p 0 0 *)
  Check p 0.
  (* p 0 *)
  Check @p _ 0 0 bool.
  (* p 0 0 (B:=bool) *)
  Check p 0 0 (B:=bool).
  (* p 0 0 (B:=bool) *)
  Check @p nat.
  (* p (A:=nat) *)
  Check p (A:=nat).
  (* p (A:=nat) *)
  Check @p _ 0 0.
  (* @p nat 0 0 *)
  Check @p.
  (* @p *)

  Unset Printing Implicit Defensive.
  Check @p _ 0 0 bool.
  (* p 0 0 *)
  Check @p nat.
  (* p *)
  Set Printing Implicit Defensive.
  End InferredGivenImplicit.

  Module ManuallyGivenImplicit.
  Axiom p : forall {A} (a1 a2:A) {B} (b:B), a1 = a2 /\ b = b.

  Check p 0 0 true.
  (* p 0 0 true *)
  Check p 0 0.
  (* p 0 0 *)
  Check p 0.
  (* p 0 *)
  Check @p _ 0 0 bool.
  (* p 0 0 *)
  Check p 0 0 (B:=bool).
  (* p 0 0 *)
  Check @p nat.
  (* p *)
  Check p (A:=nat).
  (* p *)
  Check @p _ 0 0.
  (* @p nat 0 0 *)
  Check @p.
  (* @p *)

  End ManuallyGivenImplicit.

  Module ProjectionWithImplicits.
  Set Implicit Arguments.
  Set Maximal Implicit Insertion.

  Record T {A} (a1 a2:A) := { f : forall B (b:B), a1 = a2 /\ b = b }.
  Parameter x : T 0 0.
  Check f x true.
  (* f x true *)
  Check @f _ _ _ x bool.
  (* f x (B:=bool) *)
  Check f x (B:=bool).
  (* f x (B:=bool) *)
  Check @f nat.
  (* @f nat *)
  Check @f _ 0 0.
  (* f (a1:=0) (a2:=0) *)
  Check f (a1:=0) (a2:=0).
  (* f (a1:=0) (a2:=0) *)
  Check @f.
  (* @f *)

  Unset Printing Implicit Defensive.
  Check f (a1:=0) (a2:=0).
  (* f *)
  Set Printing Implicit Defensive.

  Set Printing Projections.

  Check x.(f) true.
  (* x.(f) true *)
  Check x.(@f _ _ _) bool.
  (* x.(f) (B:=bool) *)
  Check x.(f) (B:=bool).
  (* x.(f) (B:=bool) *)
  Check @f nat.
  (* @f nat *)
  Check @f _ 0 0.
  (* f (a1:=0) (a2:=0) *)
  Check f (a1:=0) (a2:=0).
  (* f (a1:=0) (a2:=0) *)
  Check @f.
  (* @f *)

  Unset Printing Implicit Defensive.
  Check f (a1:=0) (a2:=0).
  (* f *)

  End ProjectionWithImplicits.

  Module AtAbbreviationForApplicationHead.

  Axiom p : forall {A} (a1 a2:A) {B} (b:B), a1 = a2 /\ b = b.

  Notation u := @p.

  Check u _.
  (* p *)
  Check p.
  (* p *)
  Check @p.
  (* u *)
  Check u.
  (* u *)
  Check p 0 0.
  (* p 0 0 *)
  Check u nat 0 0 bool.
  (* p 0 0 -- WEAKNESS should ideally be (B:=bool) *)
  Check u nat 0 0.
  (* @p nat 0 0 *)
  Check @p nat 0 0.
  (* @p nat 0 0 *)

  End AtAbbreviationForApplicationHead.

  Module AbbreviationForApplicationHead.

  Set Implicit Arguments.
  Set Maximal Implicit Insertion.

  Axiom p : forall A (a1 a2:A) B (b:B), a1 = a2 /\ b = b.

  Notation u := p.

  Check p.
  (* u *)
  Check @p.
  (* u -- BUG *)
  Check @u.
  (* u -- BUG *)
  Check u.
  (* u *)
  Check p 0 0.
  (* u 0 0 *)
  Check u 0 0.
  (* u 0 0 *)
  Check @p nat 0 0.
  (* @u nat 0 0 *)
  Check @u nat 0 0.
  (* @u nat 0 0 *)
  Check p 0 0 true.
  (* u 0 0 true *)
  Check u 0 0 true.
  (* u 0 0 true *)

  End AbbreviationForApplicationHead.

  Module AtAbbreviationForPartialApplication.

  Set Implicit Arguments.
  Set Maximal Implicit Insertion.

  Axiom p : forall A (a1 a2:A) B (b:B), a1 = a2 /\ b = b.

  Notation v := (@p _ 0).

  Check v.
  (* v *)
  Check p 0 0.
  (* v 0 *)
  Check v 0.
  (* v 0 *)
  Check v 0 true.
  (* v 0 (B:=bool) true -- BUG *)
  Check @p nat 0.
  (* v *)
  Check @p nat 0 0.
  (* @v 0 *)
  Check @v 0.
  (* @v 0 *)
  Check @p nat 0 0 bool.
  (* v 0 (B:=bool) *)

  End AtAbbreviationForPartialApplication.

  Module AbbreviationForPartialApplication.

  Set Implicit Arguments.
  Set Maximal Implicit Insertion.

  Axiom p : forall A (a1 a2:A) B (b:B), a1 = a2 /\ b = b.

  Notation v := (p 0).

  Check v.
  (* v *)
  Check p 0 0.
  (* v 0 *)
  Check v 0.
  (* v 0 *)
  Check v 0 true.
  (* v 0 (B:=bool) true -- BUG *)
  Check @p nat 0.
  (* v *)
  Check @p nat 0 0.
  (* @v 0 *)
  Check @v 0.
  (* @v 0 *)
  Check @p nat 0 0 bool.
  (* v 0 (B:=bool) *)

  End AbbreviationForPartialApplication.

  Module NotationForHeadApplication.

  Set Implicit Arguments.
  Set Maximal Implicit Insertion.

  Axiom p : forall A (a1 a2:A) B (b:B), a1 = a2 /\ b = b.

  Notation "##" := p (at level 0).

  Check p.
  (* ## *)
  Check ##.
  (* ## *)
  Check p 0.
  (* ## 0 *)
  Check ## 0.
  (* ## 0 *)
  Check p 0 0.
  (* ## 0 0 *)
  Check ## 0 0.
  (* ## 0 0 *)
  Check p 0 0 true.
  (* ## 0 0 (B:=bool) true -- BUG B should not be displayed *)
  Check ## 0 0 true.
  (* ## 0 0 (B:=bool) true -- BUG B should not be displayed *)
  Check p 0 0 (B:=bool).
  (* ## 0 0 (B:=bool) *)
  Check ## 0 0 (B:=bool).
  (* ## 0 0 (B:=bool) *)

  End NotationForHeadApplication.

  Module AtNotationForHeadApplication.

  Set Implicit Arguments.
  Set Maximal Implicit Insertion.

  Axiom p : forall A (a1 a2:A) B (b:B), a1 = a2 /\ b = b.

  Notation "##" := @p (at level 0).

  Check p.
  (* p *)
  Check @p.
  (* ## *)
  Check ##.
  (* ## *)
  Check p 0.
  (* p 0 -- why not "## nat 0" *)
  Check ## nat 0.
  (* p 0 *)
  Check ## nat 0 0.
  (* @p nat 0 0 *)
  Check p 0 0.
  (* p 0 0 *)
  Check ## nat 0 0 _.
  (* p 0 0 *)
  Check ## nat 0 0 bool.
  (* p 0 0 (B:=bool) *)
  Check ## nat 0 0 bool true.
  (* p 0 0 true *)

  End AtNotationForHeadApplication.

  Module NotationForPartialApplication.

  Set Implicit Arguments.
  Set Maximal Implicit Insertion.

  Axiom p : forall A (a1 a2:A) B (b:B), a1 = a2 /\ b = b.

  Notation "## q" := (p q) (at level 0, q at level 0).

  Check p 0.
  (* ## 0 *)
  Check ## 0.
  (* ## 0 *)
  (* Check ## 0 0. *)
  (* Anomaly *)
  Check p 0 0 (B:=bool).
  (* ## 0 0 (B:=bool) *)
  Check ## 0 0 bool.
  (* ## 0 0 (B:=bool) -- INCONSISTENT parsing/printing *)
  Check p 0 0 true.
  (* ## 0 0 (B:=bool) true -- BUG B should not be displayed *)
  Check ## 0 0 bool true.
  (* ## 0 0 (B:=bool) true -- INCONSISTENT parsing/printing + BUG B should not be displayed *)

  End NotationForPartialApplication.

  Module AtNotationForPartialApplication.

  Set Implicit Arguments.
  Set Maximal Implicit Insertion.

  Axiom p : forall A (a1 a2:A) B (b:B), a1 = a2 /\ b = b.

  Notation "## q" := (@p _ q) (at level 0, q at level 0).

  Check p 0.
  (* ## 0 *)
  Check ## 0.
  (* ## 0 *)
  (* Check ## 0 0. *)
  (* Anomaly *)
  Check p 0 0 (B:=bool).
  (* ## 0 0 (B:=bool) *)
  Check ## 0 0 bool.
  (* ## 0 0 (B:=bool) -- INCONSISTENT parsing/printing *)
  Check p 0 0 true.
  (* ## 0 0 (B:=bool) true -- BUG B should not be displayed *)
  Check ## 0 0 bool true.
  (* ## 0 0 (B:=bool) true -- INCONSISTENCY parsing/printing + BUG B should not be displayed *)

  End AtNotationForPartialApplication.

End AppliedTermsPrinting.
