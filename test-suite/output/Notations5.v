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
  (* u ?A *)
  Check p.
  (* u ?A *)
  Check @p.
  (* u *)
  Check u.
  (* u *)
  Check p 0 0.
  (* u nat 0 0 ?B *)
  Check u nat 0 0 bool.
  (* u nat 0 0 bool *)
  Check u nat 0 0.
  (* u nat 0 0 *)
  Check @p nat 0 0.
  (* u nat 0 0 *)

  End AtAbbreviationForApplicationHead.

  Module AbbreviationForApplicationHead.

  Set Implicit Arguments.
  Set Maximal Implicit Insertion.

  Axiom p : forall A (a1 a2:A) B (b:B), a1 = a2 /\ b = b.

  Notation u := p.

  Check p.
  (* u *)
  Check @p.
  (* @u *)
  Check @u.
  (* @u *)
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
  (* v 0 true *)
  Check @p nat 0.
  (* v *)
  Check @p nat 0 0.
  (* @v 0 *)
  Check @v 0.
  (* @v 0 *)
  Check @p nat 0 0 bool.
  (* v 0 *)
  Eval simpl in (fun x => _:nat) (@p nat 0 0 bool).
  (* ?n@{x:=v 0 (B:=bool)} *)

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
  (* v 0 true *)
  Check @p nat 0.
  (* v *)
  Check @p nat 0 0.
  (* @v 0 *)
  Check @v 0.
  (* @v 0 *)
  Check @p nat 0 0 bool.
  (* v 0 *)
  Eval simpl in (fun x => _:nat) (@p nat 0 0 bool).
  (* ?n@{x:=v 0 (B:=bool)} *)

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
  (* ## 0 0 true *)
  Check ## 0 0 true.
  (* ## 0 0 true *)
  Check p 0 0 (B:=bool).
  (* ## 0 0 *)
  Check ## 0 0 (B:=bool).
  (* ## 0 0 *)
  Eval simpl in (fun x => _:nat) (@p nat 0 0 bool).
  (* ?n@{x:=## 0 0 (B:=bool)} *)

  End NotationForHeadApplication.

  Module AtNotationForHeadApplication.

  Set Implicit Arguments.
  Set Maximal Implicit Insertion.

  Axiom p : forall A (a1 a2:A) B (b:B), a1 = a2 /\ b = b.

  Notation "##" := @p (at level 0).

  Check p.
  (* ## ?A *)
  Check @p.
  (* ## *)
  Check ##.
  (* ## *)
  Check p 0.
  (* ## nat 0 *)
  Check ## nat 0.
  (* ## nat 0 *)
  Check ## nat 0 0.
  (* ## nat 0 0 *)
  Check p 0 0.
  (* ## nat 0 0 ?B *)
  Check ## nat 0 0 _.
  (* ## nat 0 0 ?B *)
  Check ## nat 0 0 bool.
  (* ## nat 0 0 bool *)
  Check ## nat 0 0 bool true.
  (* ## nat 0 0 bool true *)

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
  Check ## 0 0.
  (* ## 0 0 *)
  Check p 0 0 (B:=bool).
  (* ## 0 0 *)
  Check ## 0 0 (B:=bool).
  (* ## 0 0 *)
  Eval simpl in (fun x => _:nat) (## 0 0 (B:=bool)).
  (* ?n@{## 0 0 (B:=bool)} *)
  Check p 0 0 true.
  (* ## 0 0 true *)
  Check ## 0 0 true.
  (* ## 0 0 true *)

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
  Check ## 0 0.
  (* ## 0 0 *)
  Check p 0 0 (B:=bool).
  (* ## 0 0 *)
  Check ## 0 0 (B:=bool).
  (* ## 0 0 *)
  Eval simpl in (fun x => _:nat) (## 0 0 (B:=bool)).
  (* ?n@{## 0 0 (B:=bool)} *)
  Check p 0 0 true.
  (* ## 0 0 true *)
  Check ## 0 0 true.
  (* ## 0 0 true *)

  End AtNotationForPartialApplication.

End AppliedTermsPrinting.

Module AppliedPatternsPrinting.

  (* Other tests testing inheritance of scope and implicit in
     term and pattern for parsing and printing *)

  Inductive T := p (a:nat) (b:bool) {B} (b:B) : T.
  Notation "0" := true : bool_scope.

  Module A.
  Notation "#" := @p (at level 0).
  Check # 0 0 _ true.
  Check fun a => match a with # 0 0 _ _ => 1 | _ => 2 end. (* !! *)
  End A.

  Module B.
  Notation "#'" := p (at level 0).
  Check #' 0 0 true.
  Check fun a => match a with #' 0 0 _ => 1 | _ => 2 end.
  End B.

  Module C.
  Notation "## q" := (@p q) (at level 0, q at level 0).
  Check ## 0 0 true.
  Check fun a => match a with ## 0 0 _ => 1 | _ => 2 end.
  End C.

  Module D.
  Notation "##' q" := (p q) (at level 0, q at level 0).
  Check ##' 0 0 true.
  Check fun a => match a with ##' 0 0 _ => 1 | _ => 2 end.
  End D.

  Module E.
  Notation P := @ p.
  Check P 0 0 _ true.
  Check fun a => match a with P 0 0 _ _ => 1 | _ => 2 end.
  End E.

  Module F.
  Notation P' := p.
  Check P' 0 0 true.
  Check fun a => match a with P' 0 0 _ => 1 | _ => 2 end.
  End F.

  Module G.
  Notation Q q := (@p q).
  Check Q 0 0 true.
  Check fun a => match a with Q 0 0 _ => 1 | _ => 2 end.
  End G.

  Module H.
  Notation Q' q := (p q).
  Check Q' 0 0 true.
  Check fun a => match a with Q' 0 0 _ => 1 | _ => 2 end.
  End H.

End AppliedPatternsPrinting.

Module Activation0.
Module Activation.

  Disable Notation "_ + _" : nat_scope.
  Check Nat.add 0 0.
  Fail Check 0 + 0.

  Disable Notation "_ + _" : type_scope.
  Fail Check 0 + 0.

  Notation f x := (Some x).

  Disable Notation f.

  Check Some 0.
  Fail Check f 0.

End Activation.
End Activation0.

Module Activation1.
  Import Activation0.

  Check Nat.add 0 0.
  Check 0 + 0.

  Import Activation.
  Check Nat.add 0 0.
  Fail Check 0 + 0.
End Activation1.
