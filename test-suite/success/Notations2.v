(* This file is giving some examples about how implicit arguments and
   scopes are (inconsistently) treated when using abbreviations or
   notations, in terms or patterns, or when using @ and parentheses in
   terms and patterns *)

(* One compromise would be that:
   - Neither abbreviations nor notations break implicit arguments and
     scopes unless the head constant is with @ and surrounded with parentheses.
     + This would change 3. terms and patterns to behave like 4. terms,
       with former behavior possible by using instead (@pair' _ x%nat)
       or (pair' x%nat).
     + This would change 4. patterns to behave like 4. terms, introducing the
       possibibility to have the deactivation in patterns, as it is in terms,
       by using (@pair').
     + This would change 5. terms to behave like 5. patterns, introducing the
       possibibility to have the activation behavior in terms, as it with
       abbreviations, using either (@(pair') _ x%nat) or (pair' _ x).
     + This would change 6. patterns to behave like 6. terms, introducing the
       possibibility to have the deactivation behavior in patterns, as it with
       abbreviations in terms, using either (@(pair') _ x%nat) or (pair' _ x).
   - "(foo args)" directly in terms would still deactivation implicit
     arguments and scopes for further arguments, as of today.
   - "(@foo args)" directly in terms would deactivate implicit arguments and scopes
     in args as of today, but not for further arguments, on the contrary of today
   - "((@foo) args)" directly in terms would deactivate implicit
     arguments and scopes in args and for further arguments, as it is today

   Then, in both terms and patterns:
   - "(@foo args)" in an abbreviation or notation would behave the same as
     "(@foo args)" when expanded, i.e. with deactivation of implicit arguments
     and scopes only for args, but not for further arguments.
   - "((@foo) args)" in an abbreviation or notation would behave the same as
     "((@foo) args)" when expanded, i.e. with deactivation of implicit arguments and scopes.
   - "(foo args)" in an abbreviation or notation would behave the same as
     "foo args" when expanded, i.e. with no change on implicit arguments and scopes.
*)

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
Check fun x : prod' bool bool => match x with (pair' 0) y 0 => 2 | _ => 1 end. (* Inconsistent with terms *)

(* 2. Abbreviations do not stop implicit arguments to be inserted and scopes to be used *)
Notation c2 x := (@pair' _ x).
Check (@pair' _ 0) _ 0%bool 0%bool : prod' bool bool. (* parentheses are blocking implicit and scopes *)
Check c2 0 0 0 : prod' bool bool.
Check fun A (x : prod' bool A) => match x with c2 0 y 0 => 2 | _ => 1 end.
Check fun A (x : prod' bool A) => match x with (@pair' _ 0) y 0 => 2 | _ => 1 end. (* Inconsistent with terms *)

(* 3. Abbreviations do not stop implicit arguments to be inserted and scopes to be used *)
Notation c3 x := ((@pair') _ x).
Check (@pair') _ 0%bool _ 0%bool 0%bool : prod' bool bool. (* @ is blocking implicit and scopes *)
Check ((@pair') _ 0%bool) _ 0%bool 0%bool : prod' bool bool. (* parentheses and @ are blocking implicit and scopes *)
Check c3 0 0 0 : prod' nat bool. (* First scope is blocked but not the last two scopes *)
Check fun A (x :prod' nat A) => match x with c3 0 y 0 => 2 | _ => 1 end.
(* Check fun A (x :prod' nat A) => match x with ((@pair') _ 0) y 0 => 2 | _ => 1 end.*)

(* 4. Abbreviations do not stop implicit arguments to be inserted and scopes to be used *)
(* unless an atomic @ is given, in terms but not in patterns *)
Notation c4 := (@pair').
Check (@pair') _ 0%bool _ 0%bool 0%bool : prod' bool bool.
Check c4 _ 0 _ 0 0%bool : prod' nat nat. (* all 0 are in nat_scope: would there be incompatibilities to change that? *)
Check fun A (x :prod' bool A) => match x with c4 _ 0 _ y 0 => 2 | _ => 1 end. (* Inconsistent with terms: both 0 are in bool_scope *)
Check fun A (x :prod' nat A) => match x with (@pair') _ 0 y 0 => 2 | _ => 1 end. (* Inconsistent with terms: the implicit arguments and scopes are not deactivated *)

(* 5. Notations stop further implicit arguments to be inserted and scopes to be used *)
(* in terms but not in patterns *)
Notation "% x" := (pair' x) (at level 0, x at level 0).
Check pair' 0 0 0 : prod' bool bool.
Check % 0 _ 0 0%bool : prod' bool nat. (* last two 0 are in nat_scope *)
Check fun A (x :prod' bool A) => match x with % 0 y 0 => 2 | _ => 1 end. (* Inconsistent with terms: both 0 are in bool_scope *)
Check fun A (x :prod' bool A) => match x with pair' 0 y 0 => 2 | _ => 1 end.

(* 6. Notations stop further implicit arguments to be inserted and scopes to be used *)
(* in terms but not in patterns *)
Notation "% x" := ((@pair') _ x%nat) (at level 0, x at level 0).
Check (@pair') _ 0 _ 0%bool 0%bool : prod' nat bool.
Check ((@pair') _ 0) _ 0%bool 0%bool : prod' nat bool.
Check % 0 _ 0 0%bool : prod' nat nat. (* last two 0 are in nat_scope *)
Check fun A (x :prod' nat A) => match x with % 0 y 0 => 2 | _ => 1 end. (* Inconsistent with terms: last 0 is in bool_scope, and implicit is not given *)
Check fun A (x :prod' bool A) => match x with (@pair') 0 y 0 => 2 | _ => 1 end. (* inconsistent with terms: the implicit arguments and scopes are not deactivated *)
Check fun A (x :prod' nat A) => match x with ((@pair') _) 0 y 0 => 2 | _ => 1 end.
