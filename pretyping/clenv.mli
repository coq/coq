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
open Evd
(*i*)

(* [new_meta] is a generator of unique meta variables *)
val new_meta : unit -> metavariable

(* [exist_to_meta] generates new metavariables for each existential
   and performs the replacement in the given constr *)
val exist_to_meta :
  Evd.evar_map -> Pretyping.open_constr -> (Termops.metamap * constr)

(* The Type of Constructions clausale environments. *)

type 'a clausenv = {
  templval : constr freelisted;
  templtyp : constr freelisted;
  namenv : identifier Metamap.t;
  env : meta_map;
  hook : 'a }

type wc = named_context sigma (* for a better reading of the following *)

(* [templval] is the template which we are trying to fill out.
 * [templtyp] is its type.
 * [namenv] is a mapping from metavar numbers to names, for
 *          use in instanciating metavars by name.
 * [env] is the mapping from metavar numbers to their types
 *       and values.
 * [hook] is the pointer to the current walking context, for
 *        integrating existential vars and metavars. *)

val collect_metas : constr -> metavariable list
val mk_clenv : 'a -> constr -> 'a clausenv
val mk_clenv_from : 'a -> constr * constr -> 'a clausenv
val mk_clenv_from_n : 'a -> int option -> constr * constr -> 'a clausenv
val mk_clenv_rename_from : wc -> constr * constr -> wc clausenv
val mk_clenv_rename_from_n : wc -> int option -> constr * constr -> wc clausenv
val mk_clenv_hnf_constr_type_of : wc -> constr -> wc clausenv
val mk_clenv_type_of : wc -> constr -> wc clausenv

val subst_clenv : (substitution -> 'a -> 'a) -> 
  substitution -> 'a clausenv -> 'a clausenv
val clenv_wtactic :
  (evar_map * meta_map -> evar_map * meta_map) -> wc clausenv -> wc clausenv

val connect_clenv : evar_info sigma -> 'a clausenv -> wc clausenv
val clenv_assign : metavariable -> constr -> 'a clausenv -> 'a clausenv
val clenv_instance_term : wc clausenv -> constr -> constr
val clenv_pose : name * metavariable * constr -> 'a clausenv -> 'a clausenv
val clenv_template : 'a clausenv -> constr freelisted
val clenv_template_type : 'a clausenv -> constr freelisted
val clenv_instance_type : wc clausenv -> metavariable -> constr
val clenv_instance_template : wc clausenv -> constr
val clenv_instance_template_type : wc clausenv -> constr
val clenv_instance : 'a clausenv -> constr freelisted -> constr
val clenv_type_of : wc clausenv -> constr -> constr
val clenv_fchain : metavariable -> 'a clausenv -> wc clausenv -> wc clausenv
val clenv_bchain : metavariable -> 'a clausenv -> wc clausenv -> wc clausenv

(* Unification with clenv *)
type arg_bindings = (int * constr) list

val clenv_unify : 
  bool -> Reductionops.conv_pb -> constr -> constr ->
  wc clausenv -> wc clausenv
val clenv_match_args :
  constr Rawterm.explicit_bindings -> wc clausenv -> wc clausenv
val clenv_constrain_with_bindings : arg_bindings -> wc clausenv -> wc clausenv

(* Bindings *)
val clenv_independent : wc clausenv -> metavariable list
val clenv_dependent : bool -> 'a clausenv -> metavariable list
val clenv_missing : 'a clausenv -> metavariable list
val clenv_constrain_missing_args : (* Used in user contrib Lannion *)
  constr list -> wc clausenv -> wc clausenv
(*
val clenv_constrain_dep_args : constr list -> wc clausenv -> wc clausenv
*)
val clenv_lookup_name : 'a clausenv -> identifier -> metavariable
val clenv_unique_resolver :
  bool -> wc clausenv -> evar_info sigma -> wc clausenv

val make_clenv_binding_apply :
  wc -> int -> constr * constr -> types Rawterm.bindings -> wc clausenv
val make_clenv_binding :
  wc -> constr * constr -> types Rawterm.bindings -> wc clausenv

(* Pretty-print *)
val pr_clenv : 'a clausenv -> Pp.std_ppcmds
