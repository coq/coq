(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*********************************************************)
(**          Definitions for the axiomatization          *)
(*********************************************************)

Require Export ZArith_base.

Parameter R : Set.

(* Declare Scope positive_scope with Key R *)
Delimit Scope R_scope with R.

(* Automatically open scope R_scope for arguments of type R *)
Bind Scope R_scope with R.

Local Open Scope R_scope.

Parameter R0 : R.
Parameter R1 : R.
Parameter Rplus : R -> R -> R.
Parameter Rmult : R -> R -> R.
Parameter Ropp : R -> R.
Parameter Rinv : R -> R.
Parameter Rlt : R -> R -> Prop.
Parameter up : R -> Z.

Infix "+" := Rplus : R_scope.
Infix "*" := Rmult : R_scope.
Notation "- x" := (Ropp x) : R_scope.
Notation "/ x" := (Rinv x) : R_scope.

Infix "<" := Rlt : R_scope.

(***********************************************************)

(**********)
Definition Rgt (r1 r2:R) : Prop := r2 < r1.

(**********)
Definition Rle (r1 r2:R) : Prop := r1 < r2 \/ r1 = r2.

(**********)
Definition Rge (r1 r2:R) : Prop := Rgt r1 r2 \/ r1 = r2.

(**********)
Definition Rminus (r1 r2:R) : R := r1 + - r2.

(**********)
Definition Rdiv (r1 r2:R) : R := r1 * / r2.

(**********)

Infix "-" := Rminus : R_scope.
Infix "/" := Rdiv   : R_scope.

Infix "<=" := Rle : R_scope.
Infix ">=" := Rge : R_scope.
Infix ">"  := Rgt : R_scope.

Notation "x <= y <= z" := (x <= y /\ y <= z) : R_scope.
Notation "x <= y < z"  := (x <= y /\ y <  z) : R_scope.
Notation "x < y < z"   := (x <  y /\ y <  z) : R_scope.
Notation "x < y <= z"  := (x <  y /\ y <= z) : R_scope.

(* Parsing and Printing digits strings as type R (when integer) *)

Fixpoint R_of_pos' (p' : positive') : R :=
  match p' with
  | x'H => R1
  | x'O x'H => Rplus R1 R1
  | x'I x'H => Rplus R1 (Rplus R1 R1)
  | x'O q => Rmult (Rplus R1 R1) (R_of_pos' q)
  | x'I q => Rplus R1 (Rmult (Rplus R1 R1) (R_of_pos' q))
  end.

Definition R_of_Z' (z' : Z') : option R :=
  match z' with
  | Z'0 => Some R0
  | Z'pos p' => Some (R_of_pos' p')
  | Z'neg p' => Some (Ropp (R_of_pos' p'))
  end.

Fixpoint pos'pred_double x :=
  match x with
  | x'I p => x'I (x'O p)
  | x'O p => x'I (pos'pred_double p)
  | x'H => x'H
  end.

Definition Z'succ_double x' :=
  match x' with
  | Z'0 => Z'pos x'H
  | Z'pos p' => Z'pos (x'I p')
  | Z'neg p' => Z'neg (pos'pred_double p')
  end.

Definition Z'double x' :=
  match x' with
  | Z'0 => Z'0
  | Z'pos p' => Z'pos (x'O p')
  | Z'neg p' => Z'neg (x'O p')
  end.

Definition Z'opp z' :=
  match z' with
  | Z'0 => Z'0
  | Z'pos q => Z'neg q
  | Z'neg q => Z'pos q
  end.

Ltac Z'_of_posR2 r :=
  match r with
  | Rplus R1 R1 => constr: (Z'pos (x'O x'H))
  | Rplus R1 (Rplus R1 R1) => constr: (Z'pos (x'I x'H))
  | Rmult ?a ?b =>
      match Z'_of_posR2 a with
      | Z'pos (x'O x'H) =>
          let b' := Z'_of_posR2 b in
          eval compute in (Z'double b')
      end
  | Rplus R1 (Rmult ?a ?b) =>
      match Z'_of_posR2 a with
      | Z'pos (x'O x'H) =>
           let b' := Z'_of_posR2 b in
           eval compute in (Z'succ_double b')
      end
  end.

Ltac Z'_of_posR r :=
  match r with
  | R0 => Z'0
  | R1 => constr: (Z'pos x'H)
  | ?r => Z'_of_posR2 r
  end.

Ltac Z'_of_R r :=
  match r with
  | Ropp ?s =>
      match Z'_of_posR s with
      | Z'0 => fail
      | ?z => eval compute in (Z'opp z)
      end
  | _ =>
      Z'_of_posR r
  end.

Numeral Notation R R_of_Z' Z'_of_R : R_scope
  (printing Ropp R0 Rplus Rmult R1).
