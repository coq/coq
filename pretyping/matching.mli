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
open Environ
open Pattern
(*i*)

(*s This modules implements pattern-matching on terms *)

exception PatternMatchingFailure

(* [matches pat c] matches [c] against [pat] and returns the resulting
   assignment of metavariables; it raises [PatternMatchingFailure] if
   not matchable; bindings are given in increasing order based on the
   numbers given in the pattern *)
val matches      :
  constr_pattern -> constr -> (int * constr) list

(* [is_matching pat c] just tells if [c] matches against [pat] *)

val is_matching      :
  constr_pattern -> constr -> bool

(* [matches_conv env sigma] matches up to conversion in environment
   [(env,sigma)] when constants in pattern are concerned; it raises
   [PatternMatchingFailure] if not matchable; bindings are given in
   increasing order based on the numbers given in the pattern *)

val matches_conv :
  env -> Evd.evar_map -> constr_pattern -> constr -> (int * constr) list

(* To skip to the next occurrence *)
exception NextOccurrence of int

(* Tries to match a subterm of [c] with [pat] *)
val sub_match :
  int -> constr_pattern -> constr -> ((int * constr) list * constr)

(* [is_matching_conv env sigma pat c] tells if [c] matches against [pat]
   up to conversion for constants in patterns *)

val is_matching_conv :
  env -> Evd.evar_map -> constr_pattern -> constr -> bool
