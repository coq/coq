(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Tacexpr
open Term
open Proof_type
open Topconstr

val rawwit_orient : bool raw_abstract_argument_type
val wit_orient : bool closed_abstract_argument_type
val orient : bool Pcoq.Gram.Entry.e

val rawwit_with_constr : constr_expr option raw_abstract_argument_type
val wit_with_constr : constr option closed_abstract_argument_type
val with_constr : constr_expr option Pcoq.Gram.Entry.e
