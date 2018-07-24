Set Primitive Projections.
Set Nonrecursive Elimination Schemes.
Module Prim.

Record F := { a : nat; b : a = a }.
Record G (A : Type) := { c : A; d : F }.

Check c.
End Prim.
Module Univ.
Set Universe Polymorphism.
Set Implicit Arguments.
Record Foo (A : Type) := { foo : A }.

Record G (A : Type) := { c : A; d : c = c; e : Foo A }.

Definition Foon : Foo nat := {| foo := 0 |}.

Definition Foonp : nat := Foon.(foo).

Definition Gt : G nat := {| c:= 0; d:=eq_refl; e:= Foon |}.

Check (Gt.(e)).

Section bla.

  Record bar := { baz : nat; def := 0; baz' : forall x, x = baz \/ x = def }.
End bla.

End Univ.

Set Primitive Projections.
Unset Elimination Schemes.
Set Implicit Arguments.

Check nat.

Inductive X (U:Type) := { k : nat; a: k = k -> X U; b : let x := a eq_refl in X U }.

Parameter x:X nat.
Check (a x : forall _ : @eq nat (k x) (k x), X nat).
Check (b x : X nat).

Inductive Y := { next : option Y }.

Check _.(next) : option Y.
Lemma eta_ind (y : Y) : y = Build_Y y.(next).
Proof. Fail reflexivity. Abort.

Inductive Fdef := { Fa : nat ; Fb := Fa; Fc : Fdef }.

Fail Scheme Fdef_rec := Induction for Fdef Sort Prop.

(* 
  Rules for parsing and printing of primitive projections and their eta expansions.
  If r : R A where R is a primitive record with implicit parameter A.
  If p : forall {A} (r : R A) {A : Set}, list (A * B).
*)

Record R {A : Type} := { p : forall {X : Set}, A * X }.
Arguments R : clear implicits.

Record R' {A : Type} := { p' : forall X : Set, A * X }.
Arguments R' : clear implicits.

Unset Printing All.

Parameter r : R nat.

Check (r.(p)).
Set Printing Projections.
Check (r.(p)).
Unset Printing Projections.
Set Printing All.
Check (r.(p)).
Unset Printing All.
  
(* Check (r.(p)).
   Elaborates to a primitive application, X arg implicit.
   Of type nat * ?ex
   No Printing All: p r
   Set Printing Projections.: r.(p)
   Printing All: r.(@p) ?ex
 *)

Check p r.
Set Printing Projections.
Check p r.
Unset Printing Projections.
Set Printing All.
Check p r.
Unset Printing All.

Check p r (X:=nat).
Set Printing Projections.
Check p r (X:=nat).
Unset Printing Projections.
Set Printing All.
Check p r (X:=nat).
Unset Printing All.

(* Same elaboration, printing for p r *)

(** Explicit version of the primitive projection, under applied w.r.t implicit arguments
      can be printed only using projection notation. r.(@p) *)
Check r.(@p _). 
Set Printing Projections.
Check r.(@p _). 
Unset Printing Projections.
Set Printing All.
Check r.(@p _).
Unset Printing All.
  
(** Explicit version of the primitive projection, applied to its implicit arguments
      can be printed using application notation r.(p), r.(@p) in fully explicit form *)
Check r.(@p _) nat.
Set Printing Projections.
Check r.(@p _) nat. 
Unset Printing Projections.
Set Printing All.
Check r.(@p _) nat.
Unset Printing All.

Parameter r' : R' nat.

Check (r'.(p')).
Set Printing Projections.
Check (r'.(p')). 
Unset Printing Projections.
Set Printing All.
Check (r'.(p')).
Unset Printing All.
  
(* Check (r'.(p')).
   Elaborates to a primitive application, X arg explicit.
   Of type forall X : Set, nat * X
   No Printing All: p' r'
   Set Printing Projections.: r'.(p')
   Printing All: r'.(@p')
 *)

Check p' r'.
Set Printing Projections.
Check p' r'.
Unset Printing Projections.
Set Printing All.
Check p' r'.
Unset Printing All.

(* Same elaboration, printing for p r *)

(** Explicit version of the primitive projection, under applied w.r.t implicit arguments
      can be printed only using projection notation. r.(@p) *)
Check r'.(@p' _). 
Set Printing Projections.
Check r'.(@p' _). 
Unset Printing Projections.
Set Printing All.
Check r'.(@p' _).
Unset Printing All.
  
(** Explicit version of the primitive projection, applied to its implicit arguments
      can be printed only using projection notation r.(p), r.(@p) in fully explicit form *)
Check p' r' nat. 
Set Printing Projections.
Check p' r' nat. 
Unset Printing Projections.
Set Printing All.
Check p' r' nat. 
Unset Printing All.

Check (@p' nat).
Check p'.
Set Printing All.

Check (@p' nat).
Check p'.
Unset Printing All.

Record wrap (A : Type) := { unwrap : A; unwrap2 : A }.

Definition term (x : wrap nat) := x.(unwrap).
Definition term' (x : wrap nat) := let f := (@unwrap2 nat) in f x.

Require Coq.extraction.Extraction.
Recursive Extraction term term'.
Extraction TestCompile term term'.
(*Unset Printing Primitive Projection Parameters.*)

(* Primitive projections in the presence of let-ins (was not failing in beta3)*)

Set Primitive Projections.
Record s (x:nat) (y:=S x) := {c:=x; d:x=c}.
Lemma f : 0=1.
Proof.
  Fail apply d.
(*
split.
reflexivity.
Qed.
*)
Abort.

(* Primitive projection match compilation *)
Require Import List.
Set Primitive Projections.

Record prod (A B : Type) := pair { fst : A ; snd : B }.
Arguments pair {_ _} _ _.

Fixpoint split_at {A} (l : list A) (n : nat) : prod (list A) (list A) :=
  match n with
  | 0 => pair nil l
  | S n =>
    match l with
    | nil => pair nil nil
    | x :: l => let 'pair l1 l2 := split_at l n in pair (x :: l1) l2
    end
  end.

Time Eval vm_compute in split_at (repeat 0 20) 10. (* Takes 0s *)
Time Eval vm_compute in split_at (repeat 0 40) 20. (* Takes 0.001s *)
Timeout 1 Time Eval vm_compute in split_at (repeat 0 60) 30. (* Used to take 60s, now takes 0.001s *)

Check (@eq_refl _ 0 <: 0 = fst (pair 0 1)).
Fail Check (@eq_refl _ 0 <: 0 = snd (pair 0 1)).

Check (@eq_refl _ 0 <<: 0 = fst (pair 0 1)).
Fail Check (@eq_refl _ 0 <<: 0 = snd (pair 0 1)).
