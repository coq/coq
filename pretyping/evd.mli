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

val is_evar : evar_map -> evar -> bool

val is_defined : evar_map -> evar -> bool

val evar_body : evar_info -> evar_body

val string_of_existential : evar -> string
val existential_of_int : int -> evar

(*s [existential_value sigma ev] raises [NotInstantiatedEvar] if [ev] has
    no body and [Not_found] if it does not exist in [sigma] *)

exception NotInstantiatedEvar
val existential_value : evar_map -> existential -> constr
val existential_type : evar_map -> existential -> types
val existential_opt_value : evar_map -> existential -> constr option

(*************************)
(* The type constructor ['a sigma] adds an evar map to an object of
  type ['a] *)
type 'a sigma = {
  it : 'a ;
  sigma : evar_map}

val sig_it  : 'a sigma -> 'a
val sig_sig : 'a sigma -> evar_map

(*************************)
(* Meta map *)

module Metaset : Set.S with type elt = metavariable

val meta_exists : (metavariable -> bool) -> Metaset.t -> bool

module Metamap : Map.S with type key = metavariable

val metamap_in_dom : metavariable -> 'a Metamap.t -> bool
val metamap_to_list : 'a Metamap.t -> (metavariable * 'a) list
val metamap_inv : 'a Metamap.t -> 'a -> metavariable list

type 'a freelisted = {
  rebus : 'a;
  freemetas : Metaset.t }

val mk_freelisted : constr -> constr freelisted
val map_fl : ('a -> 'b) -> 'a freelisted -> 'b freelisted

type clbinding =
  | Cltyp of constr freelisted
  | Clval of constr freelisted * constr freelisted

val map_clb : (constr -> constr) -> clbinding -> clbinding

type meta_map = clbinding Metamap.t
val meta_defined : meta_map -> metavariable -> bool
val meta_fvalue   : meta_map -> metavariable -> constr freelisted
val meta_ftype    : meta_map -> metavariable -> constr freelisted
val meta_declare : metavariable -> types -> meta_map -> meta_map
val meta_assign  : metavariable -> constr -> meta_map -> meta_map
