
(* $Id$ *)

(*i*)
open Util
open Names
open Term
open Tacmach
open Proof_trees
(*i*)

(* The Type of Constructions clausale environments. *)

type 'a freelisted = {
  rebus : 'a;
  freemetas : Intset.t }

type clbinding = 
  | Cltyp of constr freelisted
  | Clval of constr freelisted * constr freelisted

type 'a clausenv = {
  templval : constr freelisted;
  templtyp : constr freelisted;
  namenv : identifier Intmap.t;
  env : clbinding Intmap.t;
  hook : 'a }

(* [templval] is the template which we are trying to fill out.
 * [templtyp] is its type.
 * [namenv] is a mapping from metavar numbers to names, for
 *          use in instanciating metavars by name.
 * [env] is the mapping from metavar numbers to their types
 *       and values.
 * [hook] is the pointer to the current walking context, for
 *        integrating existential vars and metavars. *)

type wc = walking_constraints (* for a better reading of the following *)

val unify : constr -> tactic
val unify_0 : 
  (int * constr) list -> wc -> constr -> constr 
    -> (int * constr) list * (constr * constr) list

val collect_metas : constr -> int list
val mk_clenv : 'a -> constr -> 'a clausenv
val mk_clenv_from : 'a -> constr * constr -> 'a clausenv
val mk_clenv_rename_from : 'a -> constr * constr -> 'a clausenv
val mk_clenv_hnf_constr_type_of : wc -> constr -> wc clausenv
val mk_clenv_printable_type_of : wc -> constr -> wc clausenv
val mk_clenv_type_of : wc -> constr -> wc clausenv

val connect_clenv : wc -> 'a clausenv -> wc clausenv
val clenv_change_head : constr * constr -> 'a clausenv -> 'a clausenv
val clenv_assign : int -> constr -> 'a clausenv -> 'a clausenv
val clenv_instance_term : wc clausenv -> constr -> constr
val clenv_pose : name * int * constr -> 'a clausenv -> 'a clausenv
val clenv_template : 'a clausenv -> constr freelisted
val clenv_template_type : 'a clausenv -> constr freelisted
val clenv_instance_type : wc clausenv -> int -> constr
val clenv_instance_template : wc clausenv -> constr
val clenv_instance_template_type : wc clausenv -> constr
val clenv_unify : constr -> constr -> wc clausenv -> wc clausenv
val clenv_fchain : int -> 'a clausenv -> wc clausenv -> wc clausenv
val clenv_refine : (wc -> tactic) -> wc clausenv -> tactic
val res_pf      : (wc -> tactic) -> wc clausenv -> tactic
val res_pf_cast : (wc -> tactic) -> wc clausenv -> tactic
val elim_res_pf : (wc -> tactic) -> wc clausenv -> tactic
val clenv_independent : 
  wc clausenv -> constr freelisted * constr freelisted -> int list
val clenv_missing : 
  wc clausenv -> constr freelisted * constr freelisted -> int list
val clenv_constrain_missing_args : constr list -> wc clausenv -> wc clausenv
val clenv_constrain_dep_args : constr list -> wc clausenv -> wc clausenv
val clenv_lookup_name : 'a clausenv -> identifier -> int
val clenv_match_args : (bindOcc * constr) list -> wc clausenv -> wc clausenv
val e_res_pf : (wc -> tactic) -> wc clausenv -> tactic
val clenv_type_of : wc clausenv -> constr -> constr
val clenv_unique_resolver : bool -> wc clausenv -> goal sigma -> wc clausenv

(* [abstract_list_all sig c t l]                           *)
(* abstracts the terms in l over c to get a term of type t *)
val abstract_list_all : goal sigma -> constr -> constr -> constr list -> constr

(* Exported for program.ml only *)
val clenv_add_sign : 
  (identifier * typed_type) -> wc clausenv -> wc clausenv
val constrain_clenv_to_subterm : 
  wc clausenv -> constr * constr -> wc clausenv * constr
val clenv_constrain_dep_args_of : 
  int -> constr list -> wc clausenv -> wc clausenv
val constrain_clenv_using_subterm_list : 
  bool -> wc clausenv -> constr list -> constr -> wc clausenv * constr list
val clenv_typed_unify : constr -> constr -> wc clausenv -> wc clausenv
