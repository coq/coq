(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*i*)
open Names
open Term
open Sign
(*i*)

(* The type of mappings for existential variables.
   The keys are integers and the associated information is a record
   containing the type of the evar ([evar_concl]), the context under which 
   it was introduced ([evar_hyps]) and its definition ([evar_body]). 
   [evar_info] is used to add any other kind of information. *)

type evar = existential_key

type evar_body =
  | Evar_empty 
  | Evar_defined of constr

type evar_info = {
  evar_concl : constr;
  evar_hyps : named_context;
  evar_body : evar_body}

type evar_map

val empty : evar_map

val add : evar_map -> evar -> evar_info -> evar_map

val dom : evar_map -> evar list
val map : evar_map -> evar -> evar_info
val rmv : evar_map -> evar -> evar_map
val remap : evar_map -> evar -> evar_info -> evar_map
val in_dom : evar_map -> evar -> bool
val to_list : evar_map -> (evar * evar_info) list

val define : evar_map -> evar -> constr -> evar_map

val non_instantiated : evar_map -> (evar * evar_info) list
val is_evar : evar_map -> evar -> bool

val is_defined : evar_map -> evar -> bool

val evar_body : evar_info -> evar_body

val string_of_existential : evar -> string
val existential_of_int : int -> evar
