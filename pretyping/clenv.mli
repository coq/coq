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
open Evarutil
(*i*)

(* [new_meta] is a generator of unique meta variables *)
val new_meta : unit -> metavariable

(* [exist_to_meta] generates new metavariables for each existential
   and performs the replacement in the given constr *)
val exist_to_meta :
  evar_map -> Pretyping.open_constr -> (Termops.metamap * constr)

(***************************************************************)
(* The Type of Constructions clausale environments. *)

(* [templval] is the template which we are trying to fill out.
 * [templtyp] is its type.
 * [namenv] is a mapping from metavar numbers to names, for
 *          use in instanciating metavars by name.
 * [evd] is the mapping from metavar and evar numbers to their types
 *       and values.
 * [hook] is generally signature (named_context) and a sigma: the
 *        typing context
 *)
type 'a clausenv = {
  templval : constr freelisted;
  templtyp : constr freelisted;
  namenv : identifier Metamap.t;
  env : meta_map;
  hook : 'a }

type wc = named_context sigma (* for a better reading of the following *)

val subst_clenv : (substitution -> 'a -> 'a) -> 
  substitution -> 'a clausenv -> 'a clausenv

val clenv_nf_meta   : wc clausenv -> constr -> constr
val clenv_meta_type : wc clausenv -> int -> constr
val clenv_value     : wc clausenv -> constr
val clenv_type      : wc clausenv -> constr

val mk_clenv_from : evar_info sigma -> constr * constr -> wc clausenv
val mk_clenv_from_n :
  evar_info sigma -> int option -> constr * constr -> wc clausenv
val mk_clenv_rename_from_n :
  evar_info sigma -> int option -> constr * constr -> wc clausenv
val mk_clenv_type_of : evar_info sigma -> constr -> wc clausenv

(***************************************************************)
(* linking of clenvs *)

val connect_clenv : evar_info sigma -> 'a clausenv -> wc clausenv
val clenv_fchain : metavariable -> 'a clausenv -> wc clausenv -> wc clausenv

(***************************************************************)
(* Unification with clenvs *)

(* Unifies two terms in a clenv. The boolean is allow_K (see Unification) *)
val clenv_unify : 
  bool -> Reductionops.conv_pb -> constr -> constr ->
  wc clausenv -> wc clausenv

(* unifies the concl of the goal with the type of the clenv *)
val clenv_unique_resolver :
  bool -> wc clausenv -> evar_info sigma -> wc clausenv

(* same as above (allow_K=false) but replaces remaining metas
   with fresh evars *)
val evar_clenv_unique_resolver :
  wc clausenv -> evar_info sigma -> wc clausenv

(***************************************************************)
(* Bindings *)

(* bindings where the key is the position in the template of the
   clenv (dependent or not). Positions can be negative meaning to
   start from the rightmost argument of the template. *)
type arg_bindings = (int * constr) list

val clenv_independent : wc clausenv -> metavariable list
val clenv_missing : 'a clausenv -> metavariable list
val clenv_lookup_name : 'a clausenv -> identifier -> metavariable

(* defines metas corresponding to the name of the bindings *)
val clenv_match_args :
  constr Rawterm.explicit_bindings -> wc clausenv -> wc clausenv
val clenv_constrain_with_bindings : arg_bindings -> wc clausenv -> wc clausenv

(* start with a clenv to refine with a given term with bindings *)

(* 1- the arity of the lemma is fixed *)
val make_clenv_binding_apply :
  evar_info sigma -> int -> constr * constr -> constr Rawterm.bindings ->
   wc clausenv
val make_clenv_binding :
  evar_info sigma -> constr * constr -> constr Rawterm.bindings -> wc clausenv

(***************************************************************)
(* Pretty-print *)
val pr_clenv : 'a clausenv -> Pp.std_ppcmds

(***************************************************************)
(* Old or unused stuff... *)

val collect_metas : constr -> metavariable list
val mk_clenv : 'a -> constr -> 'a clausenv

val mk_clenv_rename_from : evar_info sigma -> constr * constr -> wc clausenv
val mk_clenv_hnf_constr_type_of : evar_info sigma -> constr -> wc clausenv

val clenv_wtactic :
  (evar_defs * meta_map -> evar_defs * meta_map) -> wc clausenv -> wc clausenv
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
val clenv_bchain : metavariable -> 'a clausenv -> wc clausenv -> wc clausenv
val clenv_dependent : bool -> 'a clausenv -> metavariable list
val clenv_constrain_missing_args : (* Used in user contrib Lannion *)
  constr list -> wc clausenv -> wc clausenv

