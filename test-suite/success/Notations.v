(* Check that "where" clause behaves as if given independently of the  *)
(* definition (variant of BZ#1132 submitted by Assia Mahboubi) *)

Fixpoint plus1 (n m:nat) {struct n} : nat :=
   match n with
   | O => m
   | S p => S (p+m)
   end
 where "n + m" := (plus1 n m) : nat_scope.

(* Check behaviour wrt yet empty levels (see Stephane's bug #1850) *)

Parameter P : Type -> Type -> Type -> Type.
Notation "e |= t --> v" := (P e t v)     (at level 100, t at level 54).
Check (nat |= nat --> nat).

(* Check that first non empty definition at an empty level can be of any
   associativity *)

Module Type v1.
Notation "x +1" := (S x) (at level 8, left associativity).
End v1.
Module Type v2.
Notation "x +1" := (S x) (at level 8, right associativity).
End v2.

(* Check that empty levels (here 8 and 2 in pattern) are added in the
   right order *)

Notation "' 'C_' G ( A )" := (A,G) (at level 8, G at level 2).

(* Check import of notations from within a section *)

Notation "+1 x" := (S x) (at level 25, x at level 9).
Section A. Require Import make_notation. End A.

(* Check use of "$" (see bug #1961) *)

Notation "$ x" := (id x) (at level 30).
Check ($ 5).

(* Check regression of bug #2087 *)

Notation "'exists' x , P" := (x, P)
   (at level 200, x ident, right associativity,	only parsing).

Definition foo P := let '(exists x, Q) := P in x = Q :> nat.

(* Check empty levels when extending binder_constr *)

Notation "'exists' x >= y , P" := (exists x, x >= y /\ P)%nat
   (at level 200, x ident, right associativity, y at level 69).

(* This used to loop at some time before r12491 *)

Notation R x := (@pair _ _ x).
Check (fun x:nat*nat => match x with R x y => (x,y) end).

(* Check multi-tokens recursive notations *)

Local Notation "[ a  # ; ..  # ; b ]" := (a + .. (b + 0) ..).
Check [ 0 ].
Check [ 0 # ; 1 ].

(* Check well-scoping of alpha-renaming of private binders *)
(* see bug #2248 (thanks to Marc Lasson) *)

Notation "{ q , r | P }" := (fun (p:nat*nat) => let (q, r) := p in P).
Check (fun p => {q,r| q + r = p}).

(* Check that declarations of empty levels are correctly backtracked *)

Section B.
Notation "*" := 5 (at level 0) : nat_scope.
Notation "[ h ] p" := (h + p) (at level 8, p at level 9, h at level 7) : nat_scope.
End B.

(* Should succeed *)
Definition n := 5 * 5.

(* Check that lonely notations (here FOO) do not modify the visibility
   of scoped interpretations (bug #2634 fixed in r14819) *)

Notation "x ++++ y" := (mult x y) (at level 40).
Notation "x ++++ y" := (plus x y) : A_scope.
Open Scope A_scope.
Notation "'FOO' x" := (S x) (at level 40).
Goal (2 ++++ 3) = 5.
reflexivity.
Abort.

(* Check correct failure handling when a non-constructor notation is
   used in cases pattern (bug #2724 in 8.3 and 8.4beta) *)

Notation "'FORALL'  x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 200, x binder, y binder, right associativity) : type_scope.

Fail Check fun x => match x with S (FORALL x, _) => 0 end.

(* Bug #2708: don't check for scope of variables used as binder *)

Parameter traverse : (nat -> unit) -> (nat -> unit).
Notation traverse_var f l := (traverse (fun l => f l) l).

(* Check that when an ident become a keyword, it does not break
   previous rules relying on the string to be classified as an ident *)

Notation "'intros' x" := (S x) (at level 0).
Goal True -> True. intros H. exact H. Qed.

(* Check absence of collision on ".." in nested notations with ".." *)
Notation "[ a , .. , b ]" := (a, (.. (b,tt) ..)).

(* Check that vector notations do not break Ltac [] (bugs #4785, #4733) *)
Require Import Coq.Vectors.VectorDef.
Import VectorNotations.
Goal True. idtac; []. (* important for test: no space here *) constructor. Qed.

(* Check parsing of { and } is not affected by notations #3479 *)
Notation " |- {{ a }} b" := (a=b) (no associativity, at level 10).
Goal True.
{{ exact I. }}
Qed.

Check |- {{ 0 }} 0.

(* Check parsing of { and } is not affected by notations #3479 *)
Notation " |- {{ a }} b" := (a=b) (no associativity, at level 10).
Goal True.
{{ exact I. }}
Qed.

(* Check that we can have notations without any symbol iff they are "only printing". *)
Fail Notation "" := (@nil).
Notation "" := (@nil) (only printing).

(* Check that a notation cannot be neither parsing nor printing. *)
Fail Notation "'foobarkeyword'" := (@nil) (only parsing, only printing).

(* Check "where" clause for inductive types with parameters *)

Reserved Notation "x === y" (at level 50).
Inductive EQ {A} (x:A) : A -> Prop := REFL : x === x
 where "x === y" := (EQ x y).

(* Check that strictly ident or _ are coerced to a name *)

Fail Check {x@{u},y|x=x}.
Fail Check {?[n],y|0=0}.

(* Check that 10 is well declared left associative *)

Section C.
Notation "f $$$ x" := (id f x) (at level 10, left associativity).
End C.
