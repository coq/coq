(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import Orders BinInt Zcompare Zorder.

(** THIS FILE IS DEPRECATED. *)

(*begin hide*)
(* Compatibility with names of the old Zminmax file *)
Notation Zmin_max_absorption_r_r := Z.min_max_absorption (compat "8.3").
Notation Zmax_min_absorption_r_r := Z.max_min_absorption (compat "8.3").
Notation Zmax_min_distr_r := Z.max_min_distr (compat "8.3").
Notation Zmin_max_distr_r := Z.min_max_distr (compat "8.3").
Notation Zmax_min_modular_r := Z.max_min_modular (compat "8.3").
Notation Zmin_max_modular_r := Z.min_max_modular (compat "8.3").
Notation max_min_disassoc := Z.max_min_disassoc (compat "8.3").
(*end hide*)
