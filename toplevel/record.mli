(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*i*)
open Names
open Term
open Sign
(*i*)

(* [declare_projections ref coers params fields] declare projections of
   record [ref] (if allowed), and put them as coercions accordingly to
   [coers]; it returns the absolute names of projections *)

val declare_projections :
  inductive_path -> bool list -> named_context -> constant_path option list

val definition_structure :
   bool * identifier * (identifier * Coqast.t) list *
  (bool * (identifier * bool * Coqast.t)) list * identifier * sorts -> unit
