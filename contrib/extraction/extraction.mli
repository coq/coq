(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*s Extraction from Coq terms to Miniml. *)

open Names
open Term
open Miniml
open Environ
open Nametab

(*s Result of an extraction. *)

type info = Logic | Info

type arity = Arity | NotArity

type type_var = info * arity

type signature = type_var list

type extraction_result =
  | Emltype of ml_type * signature * identifier list
  | Emlterm of ml_ast

(*s Extraction function. *)

val extract_constr : env -> constr -> extraction_result

(*s ML declaration corresponding to a Coq reference. *)

val extract_declaration : global_reference -> ml_decl

val signature : env -> constr -> signature
