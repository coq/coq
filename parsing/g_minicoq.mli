(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*i*)
open Pp
open Identifier
open Names
open Term
open Mod_declarations
open Environ
(*i*)

val term : constr Grammar.Entry.e

type command =
  | Entry of (label * specification_entry)
  | BeginModule of label * (mod_bound_id * module_type_entry) list * 
      module_type_entry option
  | EndModule of label
  | Check of constr
  | Abbrev of identifier * constr
  | Print of long_name
  | Reduce of constr

val command : command Grammar.Entry.e

val pr_term : env -> constr -> std_ppcmds

