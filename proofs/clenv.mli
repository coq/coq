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
open Names
open Term
open Sign
open Tacmach
open Proof_type
open Evar_refiner
(*i*)

(* [new_meta] is a generator of unique meta variables *)
val new_meta : unit -> int

(* [exist_to_meta] generates new metavariables for each existential
   and performs the replacement in the given constr *)
val exist_to_meta :
  Evd.evar_map -> Pretyping.open_constr ->
  ((int * types) list * constr)

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

val unify : constr -> tactic
val unify_0 : 
  Reductionops.conv_pb -> wc -> constr -> constr 
    -> (int * constr) list * (constr * constr) list

val collect_metas : constr -> int list
val mk_clenv : 'a -> constr -> 'a clausenv
val mk_clenv_from : 'a -> constr * constr -> 'a clausenv
val mk_clenv_from_n : 'a -> int option -> constr * constr -> 'a clausenv
val mk_clenv_rename_from : wc -> constr * constr -> wc clausenv
val mk_clenv_rename_from_n : wc -> int option -> constr * constr -> wc clausenv
val mk_clenv_hnf_constr_type_of : wc -> constr -> wc clausenv
val mk_clenv_type_of : wc -> constr -> wc clausenv

val subst_clenv : (substitution -> 'a -> 'a) -> 
  substitution -> 'a clausenv -> 'a clausenv

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
val clenv_unify : 
  bool -> Reductionops.conv_pb -> constr -> constr ->
  wc clausenv -> wc clausenv
val clenv_fchain : int -> 'a clausenv -> wc clausenv -> wc clausenv
val clenv_refine : (wc -> tactic) -> wc clausenv -> tactic
val res_pf      : (wc -> tactic) -> wc clausenv -> tactic
val res_pf_cast : (wc -> tactic) -> wc clausenv -> tactic
val elim_res_pf : (wc -> tactic) -> wc clausenv -> tactic
val clenv_independent : wc clausenv -> int list
val clenv_missing : 'a clausenv -> int list
val clenv_constrain_missing_args : (* Used in user contrib Lannion *)
  constr list -> wc clausenv -> wc clausenv
(*
val clenv_constrain_dep_args : constr list -> wc clausenv -> wc clausenv
*)
val clenv_lookup_name : 'a clausenv -> identifier -> int
val clenv_match_args : constr Rawterm.explicit_substitution -> wc clausenv -> wc clausenv
val e_res_pf : (wc -> tactic) -> wc clausenv -> tactic
val clenv_type_of : wc clausenv -> constr -> constr
val clenv_unique_resolver : bool -> wc clausenv -> goal sigma -> wc clausenv

val make_clenv_binding_apply :
  named_context sigma -> int -> constr * constr ->
      types Rawterm.substitution -> named_context sigma clausenv
val make_clenv_binding :
  named_context sigma -> constr * constr ->
      types Rawterm.substitution -> named_context sigma clausenv

(* Exported for program.ml only *)
val clenv_add_sign : 
  (identifier * types) -> wc clausenv -> wc clausenv
val unify_to_subterm : 
  wc clausenv -> constr * constr -> wc clausenv * constr
val unify_to_subterm_list : 
  bool -> wc clausenv -> constr list -> constr -> wc clausenv * constr list
val clenv_typed_unify :
  Reductionops.conv_pb -> constr -> constr -> wc clausenv -> wc clausenv

val pr_clenv : 'a clausenv -> Pp.std_ppcmds

(*i This should be in another module i*)

(* [abstract_list_all env sigma t c l]                     *)
(* abstracts the terms in l over c to get a term of type t *)
val abstract_list_all :
  Environ.env -> Evd.evar_map -> constr -> constr -> constr list -> constr

