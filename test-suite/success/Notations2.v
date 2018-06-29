(* This file is giving some examples about how implicit arguments and
   scopes are treated when using abbreviations or notations, in terms
   or patterns, or when using @ and parentheses in terms and patterns.

The convention is:

Constant foo with implicit arguments and scopes used in a term or a pattern:

       foo      do not deactivate further arguments and scopes
       @foo     deactivates further arguments and scopes
       (foo x)  deactivates further arguments and scopes
       (@foo x) deactivates further arguments and scopes

Notations binding to foo:

#   := foo      do not deactivate further arguments and scopes
#   := @foo     deactivates further arguments and scopes
# x := foo x    deactivates further arguments and scopes
# x := @foo x   deactivates further arguments and scopes

Abbreviations binding to foo:

f   := foo      do not deactivate further arguments and scopes
f   := @foo     deactivates further arguments and scopes
f x := foo x    do not deactivate further arguments and scopes
f x := @foo x   do not deactivate further arguments and scopes
*)

(* One checks that abbreviations and notations in patterns now behave like in terms *)

Inductive prod' A : Type -> Type :=
| pair' (a:A) B (b:B) (c:bool) : prod' A B.
Arguments pair' [A] a%bool_scope [B] b%bool_scope c%bool_scope.
Notation "0" := true : bool_scope.

(* 1. Abbreviations do not stop implicit arguments to be inserted and scopes to be used *)
Notation c1 x := (pair' x).
Check pair' 0 0 0 : prod' bool bool.
Check (pair' 0) _ 0%bool 0%bool : prod' bool bool. (* parentheses are blocking implicit and scopes *)
Check c1 0 0 0 : prod' bool bool.
Check fun x : prod' bool bool => match x with c1 0 y 0 => 2 | _ => 1 end.

(* 2. Abbreviations do not stop implicit arguments to be inserted and scopes to be used *)
Notation c2 x := (@pair' _ x).
Check (@pair' _ 0) _ 0%bool 0%bool : prod' bool bool. (* parentheses are blocking implicit and scopes *)
Check c2 0 0 0 : prod' bool bool.
Check fun A (x : prod' bool A) => match x with c2 0 y 0 => 2 | _ => 1 end.
Check fun A (x : prod' bool A) => match x with (@pair' _ 0) _ y 0%bool => 2 | _ => 1 end.

(* 3. Abbreviations do not stop implicit arguments to be inserted and scopes to be used *)
Notation c3 x := ((@pair') _ x).
Check (@pair') _ 0%bool _ 0%bool 0%bool : prod' bool bool. (* @ is blocking implicit and scopes *)
Check ((@pair') _ 0%bool) _ 0%bool 0%bool : prod' bool bool. (* parentheses and @ are blocking implicit and scopes *)
Check c3 0 0 0 : prod' nat bool. (* First scope is blocked but not the last two scopes *)
Check fun A (x :prod' nat A) => match x with c3 0 y 0 => 2 | _ => 1 end.

(* 4. Abbreviations do not stop implicit arguments to be inserted and scopes to be used *)
(* unless an atomic @ is given *)
Notation c4 := (@pair').
Check (@pair') _ 0%bool _ 0%bool 0%bool : prod' bool bool.
Check c4 _ 0%bool _ 0%bool 0%bool : prod' bool bool.
Check fun A (x :prod' bool A) => match x with c4 _ 0%bool _ y 0%bool => 2 | _ => 1 end.
Check fun A (x :prod' bool A) => match x with (@pair') _ 0%bool _ y 0%bool => 2 | _ => 1 end.

(* 5. Notations stop further implicit arguments to be inserted and scopes to be used *)
Notation "# x" := (pair' x) (at level 0, x at level 1).
Check pair' 0 0 0 : prod' bool bool.
Check # 0 _ 0%bool 0%bool : prod' bool bool.
Check fun A (x :prod' bool A) => match x with # 0 _ y 0%bool => 2 | _ => 1 end.

(* 6. Notations stop further implicit arguments to be inserted and scopes to be used *)
Notation "## x" := ((@pair') _ x) (at level 0, x at level 1).
Check (@pair') _ 0%bool _ 0%bool 0%bool : prod' bool bool.
Check ((@pair') _ 0%bool) _ 0%bool 0%bool : prod' bool bool.
Check ## 0%bool _ 0%bool 0%bool : prod' bool bool.
Check fun A (x :prod' bool A) => match x with ## 0%bool _ y 0%bool => 2 | _ => 1 end.

(* 7. Notations stop further implicit arguments to be inserted and scopes to be used *)
Notation "###" := (@pair') (at level 0).
Check (@pair') _ 0%bool _ 0%bool 0%bool : prod' bool bool.
Check ### _ 0%bool _ 0%bool 0%bool : prod' bool bool.
Check fun A (x :prod' bool A) => match x with ### _ 0%bool _ y 0%bool => 2 | _ => 1 end.

(* 8. Notations w/o @ preserves implicit arguments and scopes *)
Notation "####" := pair' (at level 0).
Check #### 0 0 0 : prod' bool bool.
Check fun A (x :prod' bool A) => match x with #### 0 y 0 => 2 | _ => 1 end.

(* 9. Notations w/o @ but arguments do not preserve further implicit arguments and scopes *)
Notation "##### x" := (pair' x) (at level 0, x at level 1).
Check ##### 0 _ 0%bool 0%bool : prod' bool bool.
Check fun A (x :prod' bool A) => match x with ##### 0 _ y 0%bool => 2 | _ => 1 end.

(* 10. Check computation of binding variable through other notations *)
(* it should be detected as binding variable and the scopes not being checked *)
Notation "'FUNNAT' i => t" := (fun i : nat => i = t) (at level 200).
Notation "'Funnat' i => t" := (FUNNAT i => t + i%nat) (at level 200).

(* 11. Notations with needed factorization of a recursive pattern *)
(* See https://github.com/coq/coq/issues/6078#issuecomment-342287412 *)
Module M11.
Notation "[:: x1 ; .. ; xn & s ]" := (cons x1 .. (cons xn s) ..).
Notation "[:: x1 ; .. ; xn ]" := (cons x1 .. (cons xn nil) ..).
Check [:: 1 ; 2 ; 3 ].
Check [:: 1 ; 2 ; 3 & nil ]. (* was failing *)
End M11.

(* 12. Preventively check that a variable which does not occur can be instantiated *)
(* by any term. In particular, it should not be restricted to a binder *)
Module M12.
Notation "N ++ x" := (S x) (only parsing).
Check 2 ++ 0.
End M12.

(* 13. Check that internal data about associativity are not used in comparing levels *)
Module M13.
Notation "x ;; z" := (x + z)
  (at level 100, z at level 200, only parsing, right associativity).
Notation "x ;; z" := (x * z)
  (at level 100, z at level 200, only parsing) : foo_scope.
End M13.

(* 14. Check that a notation with a "ident" binder does not include a pattern *)
Module M14.
Notation "'myexists' x , p" := (ex (fun x => p))
  (at level 200, x ident, p at level 200, right associativity) : type_scope.
Check myexists I, I = 0. (* Should not be seen as a constructor *)
End M14.

(* 15. Testing different ways to give the same levels without failing *)

Module M15.
  Local Notation "###### x" := (S x) (right associativity, at level 79, x at next level).
  Fail Local Notation "###### x" := (S x) (right associativity, at level 79).
  Local Notation "###### x" := (S x) (at level 79).
End M15.

(* 16. Some test about custom entries *)
Module M16.
  (* Test locality *)
  Local Declare Custom Entry foo.
  Fail Notation "#" := 0 (in custom foo). (* Should be local *)
  Local Notation "#" := 0 (in custom foo).

  (* Test import *)
  Module A.
  Declare Custom Entry foo2.
  End A.
  Fail Notation "##" := 0 (in custom foo2).
  Import A.
  Local Notation "##" := 0 (in custom foo2).

  (* Test Print Grammar *)
  Print Grammar foo.
  Print Grammar foo2.
End M16.
