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

Implicit Arguments Some [[A]].
Implicit Arguments None [[A]].

Implicit Arguments pair [[A] [B]].
Implicit Arguments fst [[A] [B]].
Implicit Arguments snd [[A] [B]].

Implicit Arguments nil [[A]].
Implicit Arguments cons [[A]].

Require List.
Export List.ListNotations.

Require Import Bvector.

(** Treating n-ary exists *)

Tactic Notation "exists" constr(x) := exists x.
Tactic Notation "exists" constr(x) constr(y) := exists x ; exists y.
Tactic Notation "exists" constr(x) constr(y) constr(z) := exists x ; exists y ; exists z.
Tactic Notation "exists" constr(x) constr(y) constr(z) constr(w) := exists x ; exists y ; exists z ; exists w.
