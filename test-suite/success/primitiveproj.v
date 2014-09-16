Set Primitive Projections.
Set Record Elimination Schemes.
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

(* Inductive X (U:Type) := Foo (k : nat) (x : X U).  *)
(* Parameter x : X nat. *)
(* Check x.(k). *)

Inductive X (U:Type) := { k : nat; a: k = k -> X U; b : let x := a eq_refl in X U }.

Parameter x:X nat.
Check (a x : forall _ : @eq nat (k x) (k x), X nat).
Check (b x : X nat).

Inductive Y := { next : option Y }.

Check _.(next) : option Y.
Lemma eta_ind (y : Y) : y = Build_Y y.(next).
Proof. reflexivity. Defined.

Variable t : Y.

Fixpoint yn (n : nat) (y : Y) : Y := 
  match n with
    | 0 => t
    | S n => {| next := Some (yn n y) |}
  end.

Lemma eta_ind'  (y: Y) : Some (yn 100 y) = Some {| next := (yn 100 y).(next) |}.
Proof. reflexivity. Defined.


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
