
(***********************************************************************
    v      *   The Coq Proof Assistant  /  The Coq Development Team     
   <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud 
     \VV/  *************************************************************
      //   *      This file is distributed under the terms of the       
           *       GNU Lesser General Public License Version 2.1        
  ***********************************************************************)

open Util
open Names
open Term
open Sign
open Environ
open Libnames
open Mod_subst
open Termops

(********************************************************************
   Meta map *)

module Metamap : Map.S with type key = metavariable

module Metaset : Set.S with type elt = metavariable

val meta_exists : (metavariable -> bool) -> Metaset.t -> bool

type 'a freelisted = {
  rebus : 'a;
  freemetas : Metaset.t }

val metavars_of : constr -> Metaset.t
val mk_freelisted : constr -> constr freelisted
val map_fl : ('a -> 'b) -> 'a freelisted -> 'b freelisted

(** Status of an instance found by unification wrt to the meta it solves:
  - a supertype of the meta (e.g. the solution to ?X <= T is a supertype of ?X)
  - a subtype of the meta (e.g. the solution to T <= ?X is a supertype of ?X)
  - a term that can be eta-expanded n times while still being a solution
    (e.g. the solution [P] to [?X u v = P u v] can be eta-expanded twice)
*)

type instance_constraint =
    IsSuperType | IsSubType | ConvUpToEta of int | UserGiven

(** Status of the unification of the type of an instance against the type of
     the meta it instantiates:
   - CoerceToType means that the unification of types has not been done
     and that a coercion can still be inserted: the meta should not be
     substituted freely (this happens for instance given via the
     "with" binding clause).
   - TypeProcessed means that the information obtainable from the
     unification of types has been extracted.
   - TypeNotProcessed means that the unification of types has not been
     done but it is known that no coercion may be inserted: the meta
     can be substituted freely.
*)

type instance_typing_status =
    CoerceToType | TypeNotProcessed | TypeProcessed

(** Status of an instance together with the status of its type unification *)

type instance_status = instance_constraint * instance_typing_status

(** Clausal environments *)

type clbinding =
  | Cltyp of name * constr freelisted
  | Clval of name * (constr freelisted * instance_status) * constr freelisted

val map_clb : (constr -> constr) -> clbinding -> clbinding


(********************************************************************
  ** Kinds of existential variables ***)

(** Should the obligation be defined (opaque or transparent (default)) or
   defined transparent and expanded in the term? *)

type obligation_definition_status = Define of bool | Expand

(** Evars *)
type hole_kind =
  | ImplicitArg of global_reference * (int * identifier option) * bool (** Force inference *)
  | BinderType of name
  | QuestionMark of obligation_definition_status
  | CasesType
  | InternalHole
  | TomatchTypeParameter of inductive * int
  | GoalEvar
  | ImpossibleCase
  | MatchingVar of bool * identifier

(********************************************************************
  ** Existential variables and unification states ***)

(** A unification state (of type [evar_map]) is primarily a finite mapping
    from existential variables to records containing the type of the evar
   ([evar_concl]), the context under which it was introduced ([evar_hyps])
   and its definition ([evar_body]). [evar_extra] is used to add any other
   kind of information.
   It also contains conversion constraints, debugging information and
   information about meta variables. *)

(** Information about existential variables. *)
type evar = existential_key

val string_of_existential : evar -> string
val existential_of_int : int -> evar

type evar_body =
  | Evar_empty
  | Evar_defined of constr

type evar_info = {
  evar_concl : constr;
  evar_hyps : named_context_val;
  evar_body : evar_body;
  evar_filter : bool list;
  evar_source : hole_kind located;
  evar_extra : Store.t }

val eq_evar_info : evar_info -> evar_info -> bool

val make_evar : named_context_val -> types -> evar_info
val evar_concl : evar_info -> constr
val evar_context : evar_info -> named_context
val evar_filtered_context : evar_info -> named_context
val evar_hyps : evar_info -> named_context_val
val evar_body : evar_info -> evar_body
val evar_filter : evar_info -> bool list
val evar_unfiltered_env :  evar_info -> env
val evar_env :  evar_info -> env

(*** Unification state ***)
type evar_map

(** Unification state and existential variables *)

(** Assuming that the second map extends the first one, this says if
   some existing evar has been refined *)
val progress_evar_map : evar_map -> evar_map -> bool

val empty : evar_map
val is_empty : evar_map -> bool

val add : evar_map -> evar -> evar_info -> evar_map

val find : evar_map -> evar -> evar_info
val find_undefined : evar_map -> evar -> evar_info
val remove : evar_map -> evar -> evar_map
val mem : evar_map -> evar -> bool
val undefined_list : evar_map -> (evar * evar_info) list
val to_list : evar_map -> (evar * evar_info) list
val fold : (evar -> evar_info -> 'a -> 'a) -> evar_map -> 'a -> 'a
val fold_undefined : (evar -> evar_info -> 'a -> 'a) -> evar_map -> 'a -> 'a
val merge : evar_map -> evar_map -> evar_map
val define : evar -> constr -> evar_map -> evar_map

val is_evar : evar_map -> evar -> bool

val is_defined : evar_map -> evar -> bool
val is_undefined : evar_map -> evar -> bool

(** {6 ... } *)
(** [existential_value sigma ev] raises [NotInstantiatedEvar] if [ev] has
    no body and [Not_found] if it does not exist in [sigma] *)

exception NotInstantiatedEvar
val existential_value : evar_map -> existential -> constr
val existential_type : evar_map -> existential -> types
val existential_opt_value : evar_map -> existential -> constr option

(** Assume empty universe constraints in [evar_map] and [conv_pbs] *)
val subst_evar_defs_light : substitution -> evar_map -> evar_map

(** spiwack: this function seems to somewhat break the abstraction. *)
val evars_reset_evd  : evar_map ->  evar_map -> evar_map


(* spiwack: [is_undefined_evar] should be considered a candidate
                   for moving to evarutils *)
val is_undefined_evar :  evar_map -> constr -> bool
val undefined_evars : evar_map -> evar_map
(* [fold_undefined f m] iterates ("folds") function [f] over the undefined
    evars (that is, whose value is [Evar_empty]) of map [m].
    It optimizes the call of {!Evd.fold} to [f] and [undefined_evars m] *)
val fold_undefined : (evar -> evar_info -> 'a -> 'a) -> evar_map -> 'a -> 'a
val evar_declare :
  named_context_val -> evar -> types -> ?src:loc * hole_kind ->
      ?filter:bool list -> evar_map -> evar_map
val evar_source : existential_key -> evar_map -> hole_kind located

(* spiwack: this function seems to somewhat break the abstraction. 
   [evar_merge evd ev1] extends the evars of [evd] with [evd1] *)
val evar_merge : evar_map -> evar_map -> evar_map

(** Unification constraints *)
type conv_pb = Reduction.conv_pb
type evar_constraint = conv_pb * env * constr * constr
val add_conv_pb :  evar_constraint -> evar_map -> evar_map

module ExistentialMap : Map.S with type key = existential_key
module ExistentialSet : Set.S with type elt = existential_key
val extract_changed_conv_pbs : evar_map ->
      (ExistentialSet.t -> evar_constraint -> bool) ->
      evar_map * evar_constraint list
val extract_all_conv_pbs : evar_map -> evar_map * evar_constraint list


(** Metas *)
val find_meta : evar_map -> metavariable -> clbinding
val meta_list : evar_map -> (metavariable * clbinding) list
val meta_defined : evar_map -> metavariable -> bool

(** [meta_fvalue] raises [Not_found] if meta not in map or [Anomaly] if
   meta has no value *)
val meta_value     : evar_map -> metavariable -> constr
val meta_fvalue    : evar_map -> metavariable -> constr freelisted * instance_status
val meta_opt_fvalue : evar_map -> metavariable -> (constr freelisted * instance_status) option
val meta_type      : evar_map -> metavariable -> types
val meta_ftype     : evar_map -> metavariable -> types freelisted
val meta_name      : evar_map -> metavariable -> name
val meta_with_name : evar_map -> identifier -> metavariable
val meta_declare   :
  metavariable -> types -> ?name:name -> evar_map -> evar_map
val meta_assign    : metavariable -> constr * instance_status -> evar_map -> evar_map
val meta_reassign  : metavariable -> constr * instance_status -> evar_map -> evar_map

(** [meta_merge evd1 evd2] returns [evd2] extended with the metas of [evd1] *)
val meta_merge : evar_map -> evar_map -> evar_map

val undefined_metas : evar_map -> metavariable list
val metas_of : evar_map -> meta_type_map
val map_metas_fvalue : (constr -> constr) -> evar_map -> evar_map

type metabinding = metavariable * constr * instance_status

val retract_coercible_metas : evar_map -> metabinding list * evar_map
val subst_defined_metas : metabinding list -> constr -> constr option

(*********************************************************
   Sort variables *)

val new_sort_variable : evar_map -> sorts * evar_map
val is_sort_variable : evar_map -> sorts -> bool
val whd_sort_variable : evar_map -> constr -> constr
val set_leq_sort_variable : evar_map -> sorts -> sorts -> evar_map
val define_sort_variable : evar_map -> sorts -> sorts -> evar_map

(********************************************************************
   constr with holes *)
type open_constr = evar_map * constr

(********************************************************************
   The type constructor ['a sigma] adds an evar map to an object of
  type ['a] *)
type 'a sigma = {
  it : 'a ;
  sigma : evar_map}

val sig_it  : 'a sigma -> 'a
val sig_sig : 'a sigma -> evar_map

(*********************************************************
   Failure explanation *)

type unsolvability_explanation = SeveralInstancesFound of int

(********************************************************************
   debug pretty-printer: *)

val pr_evar_info : evar_info -> Pp.std_ppcmds
val pr_evar_map : evar_map -> Pp.std_ppcmds
val pr_sort_constraints : evar_map -> Pp.std_ppcmds
val pr_metaset : Metaset.t -> Pp.std_ppcmds


(*** /!\Deprecated /!\ **
   create an [evar_map] with empty meta map: *)
val create_evar_defs      : evar_map -> evar_map
val create_goal_evar_defs : evar_map -> evar_map
val is_defined_evar :  evar_map -> existential -> bool
val subst_evar_map : substitution -> evar_map -> evar_map
(*** /Deprecaded ***)
