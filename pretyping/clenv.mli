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
 * [hook] is a signature (named_context) and a sigma: the
 *        typing context
 *)
type wc = named_context sigma (* for a better reading of the following *)
type clausenv = {
  templval : constr freelisted;
  templtyp : constr freelisted;
  namenv : identifier Metamap.t;
  env : meta_map;
  hook : wc }

val subst_clenv :
  (substitution -> wc -> wc) -> substitution -> clausenv -> clausenv

(* subject of clenv (instantiated) *)
val clenv_value     : clausenv -> constr
(* type of clanv (instantiated) *)
val clenv_type      : clausenv -> types
(* substitute resolved metas *)
val clenv_nf_meta   : clausenv -> constr -> constr
(* type of a meta in clenvś context *)
val clenv_meta_type : clausenv -> metavariable -> types

val mk_clenv_from : evar_info sigma -> constr * types -> clausenv
val mk_clenv_from_n :
  evar_info sigma -> int option -> constr * types -> clausenv
val mk_clenv_rename_from : evar_info sigma -> constr * types -> clausenv
val mk_clenv_rename_from_n :
  evar_info sigma -> int option -> constr * types -> clausenv
val mk_clenv_type_of : evar_info sigma -> constr -> clausenv

(***************************************************************)
(* linking of clenvs *)

val connect_clenv : evar_info sigma -> clausenv -> clausenv
val clenv_fchain : metavariable -> clausenv -> clausenv -> clausenv

(***************************************************************)
(* Unification with clenvs *)

(* Unifies two terms in a clenv. The boolean is allow_K (see Unification) *)
val clenv_unify : 
  bool -> Reductionops.conv_pb -> constr -> constr ->
  clausenv -> clausenv

(* unifies the concl of the goal with the type of the clenv *)
val clenv_unique_resolver :
  bool -> clausenv -> evar_info sigma -> clausenv

(* same as above (allow_K=false) but replaces remaining metas
   with fresh evars *)
val evar_clenv_unique_resolver :
  clausenv -> evar_info sigma -> clausenv

(***************************************************************)
(* Bindings *)

(* bindings where the key is the position in the template of the
   clenv (dependent or not). Positions can be negative meaning to
   start from the rightmost argument of the template. *)
type arg_bindings = (int * constr) list

val clenv_independent : clausenv -> metavariable list
val clenv_missing : clausenv -> metavariable list
val clenv_lookup_name : clausenv -> identifier -> metavariable

(* defines metas corresponding to the name of the bindings *)
val clenv_match_args :
  constr Rawterm.explicit_bindings -> clausenv -> clausenv
val clenv_constrain_with_bindings : arg_bindings -> clausenv -> clausenv

(* start with a clenv to refine with a given term with bindings *)

(* 1- the arity of the lemma is fixed *)
val make_clenv_binding_apply :
  evar_info sigma -> int -> constr * constr -> constr Rawterm.bindings ->
   clausenv
val make_clenv_binding :
  evar_info sigma -> constr * constr -> constr Rawterm.bindings -> clausenv

(***************************************************************)
(* Pretty-print *)
val pr_clenv : clausenv -> Pp.std_ppcmds

(***************************************************************)
(* Old or unused stuff... *)

val clenv_wtactic :
  (evar_defs * meta_map -> evar_defs * meta_map) -> clausenv -> clausenv

