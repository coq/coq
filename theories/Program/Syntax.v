(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(** Custom notations and implicits for Coq prelude definitions.

   Author: Matthieu Sozeau
   Institution: LRI, CNRS UMR 8623 - University Paris Sud
*)

(** Haskell-style notations for the unit type and value. *)

Notation " () " := Datatypes.unit : type_scope.
Notation " () " := tt.

(** Set maximally inserted implicit arguments for standard definitions. *)

Implicit Arguments eq [[A]].

Implicit Arguments Some [[A]].
Implicit Arguments None [[A]].

Implicit Arguments inl [[A] [B]].
Implicit Arguments inr [[A] [B]].

Implicit Arguments left [[A] [B]].
Implicit Arguments right [[A] [B]].

Implicit Arguments pair [[A] [B]].
Implicit Arguments fst [[A] [B]].
Implicit Arguments snd [[A] [B]].

Implicit Arguments nil [[A]].
Implicit Arguments cons [[A]].

(** Standard notations for lists. *)

Notation " [ ] " := nil : list_scope.
Notation " [ x ] " := (cons x nil) : list_scope.
Notation " [ x ; .. ; y ] " := (cons x .. (cons y nil) ..) : list_scope.

(** Implicit arguments for vectors. *)

Require Import Bvector.

Implicit Arguments Vnil [[A]].
Implicit Arguments Vcons [[A] [n]].

(** Treating n-ary exists *)

Tactic Notation "exists" constr(x) := exists x.
Tactic Notation "exists" constr(x) constr(y) := exists x ; exists y.
Tactic Notation "exists" constr(x) constr(y) constr(z) := exists x ; exists y ; exists z.
Tactic Notation "exists" constr(x) constr(y) constr(z) constr(w) := exists x ; exists y ; exists z ; exists w.
