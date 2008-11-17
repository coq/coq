(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*i*)
open Util
open Names
open Term
open Sign
open Libnames
open Mod_subst
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
  evar_hyps : Environ.named_context_val;
  evar_body : evar_body;
  evar_extra : Dyn.t option}

val eq_evar_info : evar_info -> evar_info -> bool
val evar_context : evar_info -> named_context
type evar_map

val empty : evar_map

val add : evar_map -> evar -> evar_info -> evar_map

val dom : evar_map -> evar list
val find : evar_map -> evar -> evar_info
val remove : evar_map -> evar -> evar_map
val mem : evar_map -> evar -> bool
val to_list : evar_map -> (evar * evar_info) list
val fold : (evar -> evar_info -> 'a -> 'a) -> evar_map -> 'a -> 'a

val define : evar_map -> evar -> constr -> evar_map

val is_evar : evar_map -> evar -> bool

val is_defined : evar_map -> evar -> bool

val evar_concl : evar_info -> constr
val evar_hyps : evar_info -> Environ.named_context_val
val evar_body : evar_info -> evar_body
val evar_env :  evar_info -> Environ.env

val string_of_existential : evar -> string
val existential_of_int : int -> evar

(*s [existential_value sigma ev] raises [NotInstantiatedEvar] if [ev] has
    no body and [Not_found] if it does not exist in [sigma] *)

exception NotInstantiatedEvar
val existential_value : evar_map -> existential -> constr
val existential_type : evar_map -> existential -> types
val existential_opt_value : evar_map -> existential -> constr option

(*********************************************************************)
(* constr with holes *)
type open_constr = evar_map * constr

(*********************************************************************)
(* The type constructor ['a sigma] adds an evar map to an object of
  type ['a] *)
type 'a sigma = {
  it : 'a ;
  sigma : evar_map}

val sig_it  : 'a sigma -> 'a
val sig_sig : 'a sigma -> evar_map

(*********************************************************************)
(* Meta map *)

module Metaset : Set.S with type elt = metavariable

val meta_exists : (metavariable -> bool) -> Metaset.t -> bool

type 'a freelisted = {
  rebus : 'a;
  freemetas : Metaset.t }

val metavars_of : constr -> Metaset.t
val mk_freelisted : constr -> constr freelisted
val map_fl : ('a -> 'b) -> 'a freelisted -> 'b freelisted

type clbinding =
  | Cltyp of name * constr freelisted
  | Clval of name * constr freelisted * constr freelisted

val map_clb : (constr -> constr) -> clbinding -> clbinding

(*********************************************************************)
(* Unification state *)
type evar_defs

(* Assume empty [evar_map] and [conv_pbs] *)
val subst_evar_defs_light : substitution -> evar_defs -> evar_defs

(* create an [evar_defs] with empty meta map: *)
val create_evar_defs : evar_map -> evar_defs
val evars_of         : evar_defs -> evar_map
val evars_reset_evd  : evar_map ->  evar_defs -> evar_defs

(* Evars *)
type hole_kind =
  | ImplicitArg of global_reference * (int * identifier option)
  | BinderType of name
  | QuestionMark of bool (* Can it be turned into an obligation ? *)
  | CasesType
  | InternalHole
  | TomatchTypeParameter of inductive * int
val is_defined_evar :  evar_defs -> existential -> bool
val is_undefined_evar :  evar_defs -> constr -> bool
val undefined_evars : evar_defs -> evar_defs
val evar_declare :
  Environ.named_context_val -> evar -> types -> ?src:loc * hole_kind ->
  evar_defs -> evar_defs
val evar_define : evar -> constr -> evar_defs -> evar_defs
val evar_source : existential_key -> evar_defs -> loc * hole_kind

(* Unification constraints *)
type conv_pb = Reduction.conv_pb
type evar_constraint = conv_pb * Environ.env * constr * constr
val add_conv_pb :  evar_constraint -> evar_defs -> evar_defs
val get_conv_pbs : evar_defs -> (evar_constraint -> bool) -> 
  evar_defs * evar_constraint list

(* Metas *)
val meta_list : evar_defs -> (metavariable * clbinding) list
val meta_defined : evar_defs -> metavariable -> bool
(* [meta_fvalue] raises [Not_found] if meta not in map or [Anomaly] if
   meta has no value *)  
val meta_fvalue    : evar_defs -> metavariable -> constr freelisted
val meta_ftype     : evar_defs -> metavariable -> constr freelisted
val meta_name      : evar_defs -> metavariable -> name
val meta_with_name : evar_defs -> identifier -> metavariable
val meta_declare   :
  metavariable -> types -> ?name:name -> evar_defs -> evar_defs
val meta_assign    : metavariable -> constr -> evar_defs -> evar_defs

(* [meta_merge evd1 evd2] returns [evd2] extended with the metas of [evd1] *)
val meta_merge : evar_defs -> evar_defs -> evar_defs

(**********************************************************)
(* Sort variables *)

val new_sort_variable : evar_map -> sorts * evar_map
val is_sort_variable : evar_map -> sorts -> bool
val whd_sort_variable : evar_map -> constr -> constr
val set_leq_sort_variable : evar_map -> sorts -> sorts -> evar_map
val define_sort_variable : evar_map -> sorts -> sorts -> evar_map

(*********************************************************************)
(* debug pretty-printer: *)

val pr_evar_info : evar_info -> Pp.std_ppcmds
val pr_evar_map  : evar_map -> Pp.std_ppcmds
val pr_evar_defs : evar_defs -> Pp.std_ppcmds
val pr_sort_constraints : evar_map -> Pp.std_ppcmds
val pr_metaset : Metaset.t -> Pp.std_ppcmds
