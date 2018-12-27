(* An example with constr subentries *)

Module A.

Declare Custom Entry myconstr.

Notation "[ x ]" := x (x custom myconstr at level 6).
Notation "x + y" := (Nat.add x y) (in custom myconstr at level 5) : nat_scope.
Notation "x * y" := (Nat.mul x y) (in custom myconstr at level 4) : nat_scope.
Notation "< x >" := x (in custom myconstr at level 3, x constr at level 10).
Check [ < 0 > + < 1 > * < 2 >].

Axiom a : nat.
Notation b := a.
Check [ < b > + < a > * < 2 >].

Declare Custom Entry anotherconstr.

Notation "[ x ]" := x (x custom myconstr at level 6).
Notation "<< x >>" := x (in custom myconstr at level 3, x custom anotherconstr at level 10).
Notation "# x" := (Some x) (in custom anotherconstr at level 8, x constr at level 9).
Check [ << # 0 >> ].

End A.

Module B.

Inductive Expr :=
 | Mul : Expr -> Expr -> Expr
 | Add : Expr -> Expr -> Expr
 | One : Expr.

Declare Custom Entry expr.
Notation "[ expr ]" := expr (expr custom expr at level 2).
Notation "1" := One (in custom expr at level 0).
Notation "x y" := (Mul x y) (in custom expr at level 1, left associativity).
Notation "x + y" := (Add x y) (in custom expr at level 2, left associativity).
Notation "( x )" := x (in custom expr at level 0, x at level 2).
Notation "{ x }" := x (in custom expr at level 0, x constr).
Notation "x" := x (in custom expr at level 0, x ident).

Axiom f : nat -> Expr.
Check [1 {f 1}].
Check fun x y z => [1 + y z + {f x}].
Check fun e => match e with
| [x y + z] => [x + y z]
| [1 + 1] => [1]
| y => [y + e]
end.

End B.

Module C.

Inductive Expr :=
 | Add : Expr -> Expr -> Expr
 | One : Expr.

Declare Custom Entry expr.
Notation "[ expr ]" := expr (expr custom expr at level 1).
Notation "1" := One (in custom expr at level 0).
Notation "x + y" := (Add x y) (in custom expr at level 2, left associativity).
Notation "( x )" := x (in custom expr at level 0, x at level 2).

(* Check the use of a two-steps coercion from constr to expr 1 then
   from expr 0 to expr 2 (note that camlp5 parsing is more tolerant
   and does not require parentheses to parse from level 2 while at
   level 1) *)

Check [1 + 1].

End C.

(* An example of interaction between coercion and notations from
   Robbert Krebbers. *)

Require Import String.

Module D.

Inductive expr :=
  | Var : string -> expr
  | Lam : string -> expr -> expr
  | App : expr -> expr -> expr.

Notation Let x e1 e2 := (App (Lam x e2) e1).

Parameter e1 e2 : expr.

Check (Let "x" e1 e2).

Coercion App : expr >-> Funclass.

Check (Let "x" e1 e2).

End D.

(* Check fix of #8551: a delimiter should be inserted because the
   lonely notation hides the scope nat_scope, even though the latter
   is open *)

Module E.

Notation "# x" := (S x) (at level 20) : nat_scope.
Notation "# x" := (Some x).
Check fun x => (# x)%nat.

End E.

(* Other tests of precedence *)

Module F.

Notation "# x" := (S x) (at level 20) : nat_scope.
Notation "## x" := (S x) (at level 20).
Check fun x => S x.
Open Scope nat_scope.
Check fun x => S x.
Notation "### x" := (S x) (at level 20) : nat_scope.
Check fun x => S x.
Close Scope nat_scope.
Check fun x => S x.

End F.

(* Lower priority of generic application rules *)

Module G.

Declare Scope predecessor_scope.
Delimit Scope predecessor_scope with pred.
Declare Scope app_scope.
Delimit Scope app_scope with app.
Notation "x .-1" := (Nat.pred x) (at level 10, format "x .-1") : predecessor_scope.
Notation "f ( x )" := (f x) (at level 10, format "f ( x )") : app_scope.
Check fun x => pred x.

End G.

(* Checking arbitration between in the presence of a notation in type scope *)

Module H.

Notation "∀ x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[  ' '[  ' ∀  x  ..  y ']' ,  '/' P ']'") : type_scope.
Check forall a, a = 0.

Close Scope type_scope.
Check ((forall a, a = 0) -> True)%type.
Open Scope type_scope.

Notation "#" := (forall a, a = 0).
Check #.
Check # -> True.

Close Scope type_scope.
Check (# -> True)%type.
Open Scope type_scope.

Declare Scope my_scope.
Notation "##" := (forall a, a = 0) : my_scope.
Open Scope my_scope.
Check ##.

End H.

(* Fixing bugs reported by G. Gonthier in #9207 *)

Module I.

Definition myAnd A B := A /\ B.
Notation myAnd1 A := (myAnd A).
Check myAnd1 True True.

Set Warnings "-auto-template".

Record Pnat := {inPnat :> nat -> Prop}.
Axiom r : nat -> Pnat.
Check r 2 3.

End I.

(* Fixing a bug reported by G. Gonthier in #9207 *)

Module J.

Module Import Mfoo.
Module Foo.
Definition FooCn := 2.
Module Bar.
Notation Cn := FooCn.
End Bar.
End Foo.
Export Foo.Bar.
End Mfoo.
About Cn.

End J.

Require Import Coq.Numbers.Cyclic.Int63.Int63.
Module NumeralNotations.
  Module Test17.
    (** Test int63 *)
    Declare Scope test17_scope.
    Delimit Scope test17_scope with test17.
    Local Set Primitive Projections.
    Record myint63 := of_int { to_int : int }.
    Numeral Notation myint63 of_int to_int : test17_scope.
    Check let v := 0%test17 in v : myint63.
  End Test17.
End NumeralNotations.

Module K.

Notation "# x |-> t & u" := ((fun x => (x,t)),(fun x => (x,u)))
  (at level 0, x pattern, t, u at level 39).
Check fun y : nat => # (x,z) |-> y & y.
Check fun y : nat => # (x,z) |-> (x + y) & (y + z).

End K.
