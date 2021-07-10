(* An example with constr subentries *)

Module A.

Declare Custom Entry myconstr.

Notation "[ x ]" := x (x custom myconstr at level 6).
Notation "x + y" := (Nat.add x y) (in custom myconstr at level 5).
Notation "x * y" := (Nat.mul x y) (in custom myconstr at level 4).
Notation "< x >" := x (in custom myconstr at level 3, x constr at level 10).
Check [ < 0 > + < 1 > * < 2 >].
Print Custom Grammar myconstr.

Axiom a : nat.
Notation b := a.
Check [ < b > + < a > * < 2 >].

Declare Custom Entry anotherconstr.

Notation "[ x ]" := x (x custom myconstr at level 6).
Notation "<< x >>" := x (in custom myconstr at level 3, x custom anotherconstr at level 10).
Notation "# x" := (Some x) (in custom anotherconstr at level 8, x constr at level 9).
Check [ << # 0 >> ].

(* Now check with global *)

Axiom c : nat.
Notation "x" := x (in custom myconstr at level 0, x global).
Check [ b + c ].
Check fun a => [ a + a ].

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

(* Fixing overparenthesizing reported by G. Gonthier in #9207 (PR #9214, in 8.10)*)

Module I.

Definition myAnd A B := A /\ B.
Notation myAnd1 A := (myAnd A).
Check myAnd1 True True.

Set Warnings "-auto-template".

Record Pnat := {inPnat :> nat -> Prop}.
Axiom r : nat -> Pnat.
Check r 2 3.

End I.

Require Import Coq.Numbers.Cyclic.Int63.Uint63.
Module NumberNotations.
  Module Test17.
    (** Test uint63 *)
    Declare Scope test17_scope.
    Delimit Scope test17_scope with test17.
    Local Set Primitive Projections.
    Record myint63 := of_int { to_int : int }.
    Definition parse x :=
      match x with Pos x => Some (of_int x) | Neg _ => None end.
    Definition print x := Pos (to_int x).
    Number Notation myint63 parse print : test17_scope.
    Check let v := 0%test17 in v : myint63.
  End Test17.
End NumberNotations.

Module K.

Notation "# x |-> t & u" := ((fun x => (x,t)),(fun x => (x,u)))
  (at level 0, x pattern, t, u at level 39).
Check fun y : nat => # (x,z) |-> y & y.
Check fun y : nat => # (x,z) |-> (x + y) & (y + z).

End K.

Module EmptyRecordSyntax.

Record R := { n : nat }.
Check fun '{|n:=x|} => true.

End EmptyRecordSyntax.

Module M.

(* Accept boxes around the end variables of a recursive notation (if equal boxes) *)

Notation " {@ T1 ; T2 ; .. ; Tn } " :=
  (and T1 (and T2 .. (and Tn True)..))
  (format "'[v' {@  '[' T1 ']'  ;  '//' '['  T2  ']'  ;  '//' ..  ;   '//' '['  Tn  ']'  } ']'").

Fail Notation " {@ T1 ; T2 ; .. ; Tn } " :=
  (and T1 (and T2 .. (and Tn True)..))
  (format "'[v' {@  '[' T1 ']'  ;  '//' '['  T2  ']'  ;  '//' ..  ;   '//' '['  Tn   ']'  } ']'").

Fail Notation " {@ T1 ; T2 ; .. ; Tn } " :=
  (and T1 (and T2 .. (and Tn True)..))
  (format "'[v' {@  '[' T1 ']'  ;  '//' '['  T2  ']'  ;  '//' ..  ;   '//' '[v'  Tn  ']'  } ']'").

Fail Notation " {@ T1 ; T2 ; .. ; Tn } " :=
  (and T1 (and T2 .. (and Tn True)..))
  (format "'[v' {@  '[' T1 ']'  ;  '//' '['  T2  ']'  ;  '//' ..  ;   '//' '['   Tn  ']'  } ']'").

Fail Notation " {@ T1 ; T2 ; .. ; Tn } " :=
  (and T1 (and T2 .. (and Tn True)..))
  (format "'[v' {@  '[' T1 ']'  ;  '//' '['  T2  ']'   ;  '//' ..  ;   '//' '['  Tn  ']'  } ']'").

End M.

Module Bug11331.

Notation "{ p }" := (p) (in custom expr at level 201, p constr).
Print Custom Grammar expr.

End Bug11331.

Module Bug_6082.

Declare Scope foo.
Notation "[ x ]" := (S x) (format "[  x  ]") : foo.
Open Scope foo.
Check fun x => S x.

Declare Scope bar.
Notation "[ x ]" := (S x) (format "[ x ]") : bar.
Open Scope bar.

Check fun x => S x.

End Bug_6082.

Module Bug_7766.

Notation "∀ x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[  ' ∀  x  ..  y ']' ,  P") : type_scope.

Check forall (x : nat), x = x.

Notation "∀ x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 200, x binder, y binder, right associativity,
   format "∀ x .. y , P") : type_scope.

Check forall (x : nat), x = x.

End Bug_7766.

Module N.

(* Other tests about generic and specific formats *)

Reserved Notation "x %%% y" (format "x  %%%  y", at level 35).
Reserved Notation "x %%% y" (format "x %%% y", at level 35).

(* Not using the reserved format, we warn *)

Notation "x %%% y" := (x+y) (format "x   %%%   y", at level 35).

(* Same scope (here lonely): we warn *)

Notation "x %%%% y" := (x+y) (format "x  %%%%  y", at level 35).
Notation "x %%%% y" := (x+y) (format "x %%%% y", at level 35).

(* Test if the format for a specific notation becomes the default
   generic format or if the generic format, in the absence of a
   Reserved Notation, is the one canonically obtained from the
   notation *)

Declare Scope foo_scope.
Declare Scope bar_scope.
Declare Scope bar'_scope.
Notation "x %% y" := (x+y) (at level 47, format "x   %%   y") : foo_scope.
Open Scope foo_scope.
Check 3 %% 4.

(* No scope, we inherit the initial format *)

Notation "x %% y" := (x*y) : bar_scope. (* Inherit the format *)
Open Scope bar_scope.
Check 3 %% 4.

(* Different scope and no reserved notation, we don't warn *)

Notation "x %% y" := (x*y) (at level 47, format "x    %%    y") : bar'_scope.
Open Scope bar'_scope.
Check 3 %% 4.

(* Warn for combination of "only parsing" and "format" *)

Notation "###" := 0 (at level 0, only parsing, format "###").

(* In reserved notation, warn only for the "only parsing" *)

Reserved Notation "##" (at level 0, only parsing, format "##").

End N.

Module O.

Notation U t := (match t with 0 => 0 | S t => t | _ => 0 end).
Check fun x => U (S x).
Notation V t := (t,fun t => t).
Check V tt.
Check fun x : nat => V x.

End O.

Module Bug12691.

Notation "x :=: y" := True (at level 70, no associativity, only parsing).
Notation "x :=: y" := (x = y).
Check (0 :=: 0).

End Bug12691.

Module CoercionEntryTransitivity.

Declare Custom Entry com.
Declare Custom Entry com_top.
Notation "<{ e }>" := e (at level 0, e custom com_top at level 99).
Notation "x ; y" :=
         (x + y)
           (in custom com_top at level 90, x custom com at level 90, right associativity).
Notation "x" := x (in custom com at level 0, x constr at level 0).
Notation "x" := x (in custom com_top at level 90, x custom com at level 90).

Check fun x => <{ x ; (S x) }>.

End CoercionEntryTransitivity.

(* Some corner cases *)

Module P.

(* Basic rules:
   - a section variable be used for itself and as a binding variable
   - a global name cannot be used for itself and as a binding variable
*)

  Definition pseudo_force {A} (n:A) (P:A -> Prop) := forall n', n' = n -> P n'.

  Module NotationMixedTermBinderAsIdent.

  Set Warnings "-deprecated-ident-entry". (* We do want ident! *)
  Notation "▢_ n P" := (pseudo_force n (fun n => P))
    (at level 0, n ident, P at level 9, format "▢_ n  P").
  Check exists p, ▢_p (p >= 1).
  Section S.
  Variable n:nat.
  Check ▢_n (n >= 1).
  End S.
  Fail Check ▢_nat (nat = bool).
  Fail Check ▢_O (O >= 1).
  Axiom n:nat.
  Fail Check ▢_n (n >= 1).

  End NotationMixedTermBinderAsIdent.

  Module NotationMixedTermBinderAsPattern.

  Notation "▢_ n P" := (pseudo_force n (fun n => P))
    (at level 0, n pattern, P at level 9, format "▢_ n  P").
  Check exists x y, ▢_(x,y) (x >= 1 /\ y >= 2).
  Section S.
  Variable n:nat.
  Check ▢_n (n >= 1).
  End S.
  Fail Check ▢_nat (nat = bool).
  Check ▢_tt (tt = tt).
  Axiom n:nat.
  Fail Check ▢_n (n >= 1).

  End NotationMixedTermBinderAsPattern.

  Module NotationMixedTermBinderAsStrictPattern.

  Notation "▢_ n P" := (pseudo_force n (fun n => P))
    (at level 0, n strict pattern, P at level 9, format "▢_ n  P").
  Check exists x y, ▢_(x,y) (x >= 1 /\ y >= 2).
  Section S.
  Variable n:nat.
  Check ▢_n (n >= 1).
  End S.
  Fail Check ▢_nat (nat = bool).
  Check ▢_tt (tt = tt).
  Axiom n:nat.
  Fail Check ▢_n (n >= 1).

  End NotationMixedTermBinderAsStrictPattern.

  Module AbbreviationMixedTermBinderAsStrictPattern.

  Notation myforce n P := (pseudo_force n (fun n => P)).
  Check exists x y, myforce (x,y) (x >= 1 /\ y >= 2).
  Section S.
  Variable n:nat.
  Check myforce n (n >= 1). (* strict hence not used for printing *)
  End S.
  Fail Check myforce nat (nat = bool).
  Check myforce tt (tt = tt).
  Axiom n:nat.
  Fail Check myforce n (n >= 1).

  End AbbreviationMixedTermBinderAsStrictPattern.

  Module Bug4765Part.

  Notation id x := ((fun y => y) x).
  Check id nat.

  Notation id' x := ((fun x => x) x).
  Check fun a : bool => id' a.
  Check fun nat : bool => id' nat.
  Fail Check id' nat.

  End Bug4765Part.

  Module NotationBinderNotMixedWithTerms.

  Notation "!! x , P" := (forall x, P) (at level 200, x pattern).
  Check !! nat, nat = true.

  Notation "!!! x , P" := (forall x, P) (at level 200).
  Check !!! nat, nat = true.

  Notation "!!!! x , P" := (forall x, P) (at level 200, x strict pattern).
  Check !!!! (nat,id), nat = true /\ id = false.

  End NotationBinderNotMixedWithTerms.

End P.

Module MorePrecise1.

(* A notation with limited iteration is strictly more precise than a
   notation with unlimited iteration *)

Notation "∀ x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[  ' '[  ' ∀  x  ..  y ']' ,  '/' P ']'") : type_scope.

Check forall x, x = 0.

Notation "∀₁ z , P" := (forall z, P)
  (at level 200, right associativity) : type_scope.

Check forall x, x = 0.

Notation "∀₂ y x , P" := (forall y x, P)
  (at level 200, right associativity) : type_scope.

Check forall x, x = 0.
Check forall x y, x + y = 0.

Notation "(( x , y ))" := (x,y) : core_scope.

Check ((1,2)).

End MorePrecise1.

Module MorePrecise2.

(* Case of a bound binder *)
Notation "%% [ x == y ]" := (forall x, S x = y) (at level 0, x pattern, y at level 60).

(* Case of an internal binder *)
Notation "%%% [ y ]" := (forall x : nat, x = y) (at level 0).

(* Check that the two previous notations are indeed finer *)
Notation "∀ x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[  ' '[  ' ∀  x  ..  y ']' ,  '/' P ']'").
Notation "∀' x .. y , P" := (forall y, .. (forall x, P) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[  ' '[  ' ∀'  x  ..  y ']' ,  '/' P ']'").

Check %% [x == 1].
Check %%% [1].

Notation "[[ x ]]" := (pair 1 x).

Notation "( x ; y ; .. ; z )" := (pair .. (pair x y) .. z).
Notation "[ x ; y ; .. ; z ]" := (pair .. (pair x z) .. y).

(* Check which is finer *)
Check [[ 2 ]].

End MorePrecise2.

Module MorePrecise3.

(* This is about a binder not bound in a notation being strictly more
   precise than a binder bound in the notation (since the notation
   applies - a priori - stricly less often) *)

Notation "%%%" := (forall x, x) (at level 0).

Notation "∀ x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[  ' '[  ' ∀  x  ..  y ']' ,  '/' P ']'").

Check %%%.

End MorePrecise3.

Module TypedPattern.

Notation "## x P" := (forall x:nat*nat, P) (x pattern, at level 0).
Check ## (x,y) (x=0).
Fail Check ## ((x,y):bool*bool) (x=y).

End TypedPattern.

Module SingleBinder.

Notation "## x P" := (forall x, x = x -> P) (x binder, at level 0).
Check ## '(x,y) (x+y=0).
Check ## (x:nat) (x=0).
Check ## '((x,y):nat*nat) (x=0).
Check fun (f : ## {a} (a=0)) => f (a:=1) eq_refl.

End SingleBinder.

Module GenericFormatPrecedence.
(* Check that if a generic format exists, we use it preferably to no
   explicit generic format *)
Notation "[ 'MyNotation' G ]" := (S G) (at level 0, format "[ 'MyNotation'  G ]") : nat_scope.
Notation "[ 'MyNotation' G ]" := (G+0) (at level 0, only parsing) : bool_scope.
Notation "[ 'MyNotation' G ]" := (G*0).
Check 0*0.
End GenericFormatPrecedence.

Module LeadingIdent.

Notation "'MyNone' +" := None (format "'MyNone' +").
Check fun MyNone : nat => MyNone.
Check MyNone+.
Check Some MyNone+.

End LeadingIdent.
