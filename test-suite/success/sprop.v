(* -*- mode: coq; coq-prog-args: ("-allow-sprop") -*- *)

Set Primitive Projections.
Set Warnings "+non-primitive-record".

Check SProp.

Definition iUnit : SProp := forall A : SProp, A -> A.

Definition itt : iUnit := fun A a => a.

Definition iUnit_irr (P : iUnit -> Type) (x y : iUnit) : P x -> P y
  := fun v => v.

Definition iSquash (A:Type) : SProp
  := forall P : SProp, (A -> P) -> P.
Definition isquash A : A -> iSquash A
  := fun a P f => f a.
Definition iSquash_rect A (P : iSquash A -> SProp) (H : forall x : A, P (isquash A x))
  : forall x : iSquash A, P x
  := fun x => x (P x) (H : A -> P x).

Fail Check (fun A : SProp => A : Type).

Lemma foo : Prop.
Proof. pose (fun A : SProp => A : Type). Abort.

(* define evar as product *)
Check (fun (f:(_:SProp)) => f _).

Inductive sBox (A:SProp) : Prop
  := sbox : A -> sBox A.

Definition uBox := sBox iUnit.

Definition sBox_irr A (x y : sBox A) : x = y.
Proof.
  Fail reflexivity.
  destruct x as [x], y as [y].
  reflexivity.
Defined.

(* Primitive record with all fields in SProp has the eta property of SProp so must be SProp. *)
Fail Record rBox (A:SProp) : Prop := rmkbox { runbox : A }.
Section Opt.
  Local Unset Primitive Projections.
  Record rBox (A:SProp) : Prop := rmkbox { runbox : A }.
End Opt.

(* Check that defining as an emulated record worked *)
Check runbox.

(* Check that it doesn't have eta *)
Fail Check (fun (A : SProp) (x : rBox A) => eq_refl : x = @rmkbox _ (@runbox _ x)).

Inductive sEmpty : SProp := .

Inductive sUnit : SProp := stt.

Inductive BIG : SProp := foo | bar.

Inductive Squash (A:Type) : SProp
  := squash : A -> Squash A.

Definition BIG_flip : BIG -> BIG.
Proof.
  intros [|]. exact bar. exact foo.
Defined.

Inductive pb : Prop := pt | pf.

Definition pb_big : pb -> BIG.
Proof.
  intros [|]. exact foo. exact bar.
Defined.

Fail Definition big_pb (b:BIG) : pb :=
  match b return pb with foo => pt | bar => pf end.

Inductive which_pb : pb -> SProp :=
| is_pt : which_pb pt
| is_pf : which_pb pf.

Fail Definition pb_which b (w:which_pb b) : bool
  := match w with
     | is_pt => true
     | is_pf => false
     end.

(* Non primitive because no arguments, but maybe we should allow it for sprops? *)
Fail Record UnitRecord : SProp := {}.

Section Opt.
  Local Unset Primitive Projections.
  Record UnitRecord' : SProp := {}.
End Opt.
Fail Scheme Induction for UnitRecord' Sort Set.

Record sProd (A B : SProp) : SProp := sPair { sFst : A; sSnd : B }.

Scheme Induction for sProd Sort Set.

Unset Primitive Projections.
Record sProd' (A B : SProp) : SProp := sPair' { sFst' : A; sSnd' : B }.
Set Primitive Projections.

Fail Scheme Induction for sProd' Sort Set.

Inductive Istrue : bool -> SProp := istrue : Istrue true.

Definition Istrue_sym (b:bool) := if b then sUnit else sEmpty.
Definition Istrue_to_sym b (i:Istrue b) : Istrue_sym b := match i with istrue => stt end.

Definition Istrue_rec (P:forall b, Istrue b -> Set) (H:P true istrue) b (i:Istrue b) : P b i.
Proof.
  destruct b.
  - exact_no_check H.
  - apply sEmpty_rec. apply Istrue_to_sym in i. exact i.
Defined.

Check (fun P v (e:Istrue true) => eq_refl : Istrue_rec P v _ e = v).

Record Truepack := truepack { trueval :> bool; trueprop : Istrue trueval }.

Definition Truepack_eta (x : Truepack) (i : Istrue x) : x = truepack x i := @eq_refl Truepack x.

Class emptyclass : SProp := emptyinstance : forall A:SProp, A.

(** Sigma in SProp can be done through Squash and relevant sigma. *)
Definition sSigma (A:SProp) (B:A -> SProp) : SProp
  := Squash (@sigT (rBox A) (fun x => rBox (B (runbox _ x)))).

Definition spair (A:SProp) (B:A->SProp) (x:A) (y:B x) : sSigma A B
  := squash _ (existT _ (rmkbox _ x) (rmkbox _ y)).

Definition spr1 (A:SProp) (B:A->SProp) (p:sSigma A B) : A
  := let 'squash _ (existT _ x y) := p in runbox _ x.

Definition spr2 (A:SProp) (B:A->SProp) (p:sSigma A B) : B (spr1 A B p)
  := let 'squash _ (existT _ x y) := p return B (spr1 A B p) in runbox _ y.
(* it's SProp so it computes properly *)

(** Fixpoints on SProp values are only allowed to produce SProp results *)
Inductive sAcc (x:nat) : SProp := sAcc_in : (forall y, y < x -> sAcc y) -> sAcc x.

Definition sAcc_inv x (s:sAcc x) : forall y, y < x -> sAcc y.
Proof.
  destruct s as [H]. exact H.
Defined.

Section sFix_fail.
  Variable P : nat -> Type.
  Variable F : forall x:nat, (forall y:nat, y < x -> P y) -> P x.

  Fail Fixpoint sFix (x:nat) (a:sAcc x) {struct a} : P x :=
    F x (fun (y:nat) (h: y < x) => sFix y (sAcc_inv x a y h)).
End sFix_fail.

Section sFix.
  Variable P : nat -> SProp.
  Variable F : forall x:nat, (forall y:nat, y < x -> P y) -> P x.

  Fixpoint sFix (x:nat) (a:sAcc x) {struct a} : P x :=
    F x (fun (y:nat) (h: y < x) => sFix y (sAcc_inv x a y h)).

End sFix.
