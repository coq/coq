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
open Rawterm
open Term
open Sign
open Evd
open Environ
open Reductionops
(*i*)

(*s This modules provides useful functions for unification modulo evars *)

(***********************************************************)
(* Metas *)

(* [new_meta] is a generator of unique meta variables *)
val new_meta : unit -> metavariable
val mk_new_meta : unit -> constr

(* [new_untyped_evar] is a generator of unique evar keys *)
val new_untyped_evar : unit -> existential_key

(***********************************************************)
(* Creating a fresh evar given their type and context *)
val new_evar :
  evar_defs -> env -> ?src:loc * hole_kind -> ?filter:bool list -> types -> evar_defs * constr
(* the same with side-effects *)
val e_new_evar :
  evar_defs ref -> env -> ?src:loc * hole_kind -> ?filter:bool list -> types -> constr

(* Create a fresh evar in a context different from its definition context:
   [new_evar_instance sign evd ty inst] creates a new evar of context
   [sign] and type [ty], [inst] is a mapping of the evar context to
   the context where the evar should occur. This means that the terms 
   of [inst] are typed in the occurrence context and their type (seen
   as a telescope) is [sign] *)
val new_evar_instance :
 named_context_val -> evar_defs -> types -> ?src:loc * hole_kind -> ?filter:bool list -> constr list -> evar_defs * constr

(***********************************************************)
(* Instantiate evars *)

(* [evar_define env ev c] try to instantiate [ev] with [c] (typed in [env]),
   possibly solving related unification problems, possibly leaving open
   some problems that cannot be solved in a unique way;
   failed if the instance is not valid for the given [ev] *)
val evar_define : env -> existential -> constr -> evar_defs -> evar_defs

(***********************************************************)
(* Evars/Metas switching... *)

(* [evars_to_metas] generates new metavariables for each non dependent
   existential and performs the replacement in the given constr; it also
   returns the evar_map extended with dependent evars *)
val evars_to_metas : evar_map -> open_constr -> (evar_map * constr)

val non_instantiated : evar_map -> (evar * evar_info) list

(***********************************************************)
(* Unification utils *)

val is_ground_term :  evar_defs -> constr -> bool
val solve_simple_eqn :
  (env ->  evar_defs -> conv_pb -> constr -> constr -> evar_defs * bool)
  -> env ->  evar_defs -> conv_pb * existential * constr ->
    evar_defs * bool

(* [check_evars env initial_sigma extended_sigma c] fails if some
   new unresolved evar remains in [c] *)
val check_evars : env -> evar_map -> evar_defs -> constr -> unit

val define_evar_as_arrow : evar_defs -> existential -> evar_defs * types
val define_evar_as_lambda : evar_defs -> existential -> evar_defs * types
val define_evar_as_sort : evar_defs -> existential -> evar_defs * sorts

val is_unification_pattern_evar : existential -> constr list -> bool
val is_unification_pattern : constr -> constr array -> bool
val solve_pattern_eqn : env -> constr list -> constr -> constr

(***********************************************************)
(* Value/Type constraints *)

val judge_of_new_Type : unit -> unsafe_judgment

type type_constraint_type = (int * int) option * constr
type type_constraint = type_constraint_type option

type val_constraint = constr option

val empty_tycon : type_constraint
val mk_tycon_type : constr -> type_constraint_type
val mk_abstr_tycon_type : int -> constr -> type_constraint_type
val mk_tycon : constr -> type_constraint
val mk_abstr_tycon : int -> constr -> type_constraint
val empty_valcon : val_constraint
val mk_valcon : constr -> val_constraint

val split_tycon :
  loc -> env ->  evar_defs -> type_constraint -> 
    evar_defs * (name * type_constraint * type_constraint)

val valcon_of_tycon : type_constraint -> val_constraint

val lift_abstr_tycon_type : int -> type_constraint_type -> type_constraint_type

val lift_tycon_type : int -> type_constraint_type -> type_constraint_type
val lift_tycon : int -> type_constraint -> type_constraint

(***********************************************************)

(* [whd_ise] raise [Uninstantiated_evar] if an evar remains uninstantiated; *)
(* *[whd_evar]* and *[nf_evar]* leave uninstantiated evar as is *)

val nf_evar :  evar_map -> constr -> constr
val j_nf_evar :  evar_map -> unsafe_judgment -> unsafe_judgment
val jl_nf_evar :
   evar_map -> unsafe_judgment list -> unsafe_judgment list
val jv_nf_evar :
   evar_map -> unsafe_judgment array -> unsafe_judgment array
val tj_nf_evar :
   evar_map -> unsafe_type_judgment -> unsafe_type_judgment

val nf_evar_info : evar_map -> evar_info -> evar_info
val nf_evars : evar_map -> evar_map

(* Same for evar defs *)
val nf_isevar :  evar_defs -> constr -> constr
val j_nf_isevar :  evar_defs -> unsafe_judgment -> unsafe_judgment
val jl_nf_isevar :
   evar_defs -> unsafe_judgment list -> unsafe_judgment list
val jv_nf_isevar :
   evar_defs -> unsafe_judgment array -> unsafe_judgment array
val tj_nf_isevar :
   evar_defs -> unsafe_type_judgment -> unsafe_type_judgment

val nf_evar_defs : evar_defs -> evar_defs

(* Replacing all evars *)
exception Uninstantiated_evar of existential_key
val whd_ise :  evar_map -> constr -> constr
val whd_castappevar :  evar_map -> constr -> constr

(*********************************************************************)
(* debug pretty-printer: *)

val pr_tycon_type : env -> type_constraint_type -> Pp.std_ppcmds
val pr_tycon : env -> type_constraint -> Pp.std_ppcmds


(**********************************)
(* Removing hyps in evars'context *)
val clear_hyps_in_evi : evar_defs ref -> evar_info -> identifier list -> evar_info
