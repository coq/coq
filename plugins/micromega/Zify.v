(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import ZifyClasses.
Require Export ZifyInst.
Require Import InitialRing.

(** From PreOmega *)

(** I) translation of Z.max, Z.min, Z.abs, Z.sgn into recognized equations *)

Ltac zify_unop_core t thm a :=
 (* Let's introduce the specification theorem for t *)
 pose proof (thm a);
 (* Then we replace (t a) everywhere with a fresh variable *)
 let z := fresh "z" in set (z:=t a) in *; clearbody z.

Ltac zify_unop_var_or_term t thm a :=
 (* If a is a variable, no need for aliasing *)
 let za := fresh "z" in
 (rename a into za; rename za into a; zify_unop_core t thm a) ||
 (* Otherwise, a is a complex term: we alias it. *)
 (remember a as za; zify_unop_core t thm za).

Ltac zify_unop t thm a :=
 (* If a is a scalar, we can simply reduce the unop. *)
 (* Note that simpl wasn't enough to reduce [Z.max 0 0] (#5439) *)
 let isz := isZcst a in
 match isz with
  | true =>
    let u := eval compute in (t a) in
    change (t a) with u in *
  | _ => zify_unop_var_or_term t thm a
 end.

Ltac zify_unop_nored t thm a :=
 (* in this version, we don't try to reduce the unop (that can be (Z.add x)) *)
 let isz := isZcst a in
 match isz with
  | true => zify_unop_core t thm a
  | _ => zify_unop_var_or_term t thm a
 end.

Ltac zify_binop t thm a b:=
 (* works as zify_unop, except that we should be careful when
    dealing with b, since it can be equal to a *)
 let isza := isZcst a in
 match isza with
   | true => zify_unop (t a) (thm a) b
   | _ =>
       let za := fresh "z" in
       (rename a into za; rename za into a; zify_unop_nored (t a) (thm a) b) ||
       (remember a as za; match goal with
         | H : za = b |- _ => zify_unop_nored (t za) (thm za) za
         | _ => zify_unop_nored (t za) (thm za) b
        end)
 end.

(* end from PreOmega *)

Ltac applySpec S :=
  let t := type of S in
  match t with
  | @BinOpSpec _ _ ?Op _ =>
    let Spec := (eval unfold S, BSpec in (@BSpec _ _ Op _ S)) in
    repeat
      match goal with
      | H : context[Op ?X ?Y] |- _ => zify_binop Op Spec X Y
      | |- context[Op ?X ?Y]       => zify_binop Op Spec X Y
      end
  | @UnOpSpec _ _ ?Op _ =>
    let Spec := (eval unfold S, USpec in (@USpec _ _ Op _ S)) in
    repeat
      match goal with
      | H : context[Op ?X] |- _ => zify_unop Op Spec X
      | |- context[Op ?X ]       => zify_unop Op Spec X
      end
  end.

(** [zify_post_hook] is there to be redefined. *)
Ltac zify_post_hook := idtac.

Ltac zify := zify_tac ; (iter_specs applySpec) ; zify_post_hook.
