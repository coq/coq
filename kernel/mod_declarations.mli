(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)


(*i*)
open Util
open Identifier
open Names
open Declarations
(*i*)


type specification_entry = 
    SPEconst of constant_entry
  | SPEmind of mutual_inductive_entry
  | SPEmodule of module_entry
  | SPEmodtype of module_type_entry

and module_type_entry = 
    MTEident of long_name
  | MTEfunsig of mod_bound_id * module_type_entry * module_type_entry
  | MTEsig of mod_str_id * module_signature_entry

and module_signature_entry = (label * specification_entry) list



and module_expr = 
    MEident of module_path
  | MEfunctor of mod_bound_id * module_type_entry * module_expr
  | MEstruct of mod_str_id * module_structure
  | MEapply of module_expr * module_expr

and module_structure = (label * specification_entry) list


and module_entry = 
    { mod_entry_type : module_type_entry option;
      mod_entry_expr : module_expr option}


type specification_body = 
    SPBconst of constant_body
  | SPBmind of mutual_inductive_body
  | SPBmodule of module_body
  | SPBmodtype of module_type_body

and module_type_body = 
    MTBident of long_name
  | MTBfunsig of mod_bound_id * module_type_body * module_type_body
  | MTBsig of mod_str_id * module_signature_body

and module_signature_body = (label * specification_body) list


and module_body = 
    { mod_type : module_type_body;
      mod_eq : module_path option }

