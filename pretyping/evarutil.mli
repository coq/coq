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

(***********************************************************)
(* Creating a fresh evar given their type and context *)
val new_evar :
  evar_defs -> env -> ?src:loc * hole_kind -> types -> evar_defs * constr
(* the same with side-effects *)
val e_new_evar :
  evar_defs ref -> env -> ?src:loc * hole_kind -> types -> constr

(* Create a fresh evar in a context different from its definition context:
   [new_evar_instance sign evd ty inst] creates a new evar of context
   [sign] and type [ty], [inst] is a mapping of the evar context to
   the context where the evar should occur. This means that the terms 
   of [inst] are typed in the occurrence context and their type (seen
   as a telescope) is [sign] *)
val new_evar_instance :
 named_context -> evar_defs -> types -> ?src:loc * hole_kind -> constr list ->
 evar_defs * constr

(* Builds the instance in the case where the occurrence context is the
   same as the evar context *)
val make_evar_instance : env -> constr list

val w_Declare : env -> evar -> types -> evar_defs -> evar_defs

(***********************************************************)
(* Instanciate evars *)

val w_Define : evar -> constr -> evar_defs -> evar_defs

(* suspicious env ? *)
val evar_define :
  env -> existential -> constr -> evar_defs -> evar_defs * evar list


(***********************************************************)
(* Evars/Metas switching... *)

(* [exist_to_meta] generates new metavariables for each existential
   and performs the replacement in the given constr *)
val exist_to_meta : evar_map -> open_constr -> (Termops.metamap * constr)

val non_instantiated : evar_map -> (evar * evar_info) list

(***********************************************************)
(* Unification utils *)

val has_undefined_evars :  evar_defs -> constr -> bool
val is_eliminator : constr -> bool
val head_is_embedded_evar :  evar_defs -> constr -> bool
val solve_simple_eqn :
  (env ->  evar_defs -> conv_pb -> constr -> constr -> evar_defs * bool)
  -> env ->  evar_defs -> conv_pb * existential * constr ->
    evar_defs * bool

val define_evar_as_arrow : evar_defs -> existential -> evar_defs * types
val define_evar_as_sort : evar_defs -> existential -> evar_defs * sorts

(***********************************************************)
(* Value/Type constraints *)

val judge_of_new_Type : unit -> unsafe_judgment

type type_constraint = constr option
type val_constraint = constr option

val empty_tycon : type_constraint
val mk_tycon : constr -> type_constraint
val empty_valcon : val_constraint
val mk_valcon : constr -> val_constraint

val split_tycon :
  loc -> env ->  evar_defs -> type_constraint -> 
    evar_defs * (name * type_constraint * type_constraint)

val valcon_of_tycon : type_constraint -> val_constraint

val lift_tycon : type_constraint -> type_constraint

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

(* Replacing all evars *)
exception Uninstantiated_evar of existential_key
val whd_ise :  evar_map -> constr -> constr
val whd_castappevar :  evar_map -> constr -> constr
