(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

open Dpctypes
open Names

val subst_term : identifier -> term -> term -> term
val subst : identifier -> term -> formula -> formula
val all_lit : formula -> formula list
val subst_f_f : formula -> formula -> formula -> formula
val all_var_term : term -> identifier list
val free_var_formula : formula -> identifier list
val id_in_formula : identifier -> formula -> bool

