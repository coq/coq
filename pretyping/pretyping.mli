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
open Sign
open Term
open Environ
open Evd
open Rawterm
open Evarutil
(*i*)

type var_map = (identifier * unsafe_judgment) list

(* constr with holes *)
type open_constr = evar_map * constr


(* Generic call to the interpreter from rawconstr to constr, failing
   unresolved holes in the rawterm cannot be instantiated.

   In [understand_gen sigma env varmap typopt raw],

   sigma : initial set of existential variables (typically dependent subgoals)
   varmap : partial subtitution of variables (used for the tactic language)
   metamap : partial subtitution of meta (used for the tactic language)
   typopt : is not None, this is the expected type for raw (used to define evars)
*)
val understand_gen :
  evar_map -> env -> var_map
    -> expected_type:(constr option) -> rawconstr -> constr

val understand_gen_ltac :
  evar_map -> env -> var_map * (identifier * identifier option) list
    -> expected_type:(constr option) -> rawconstr -> constr

(* Generic call to the interpreter from rawconstr to constr, turning
   unresolved holes into metas. Returns also the typing context of
   these metas. Work as [understand_gen] for the rest. *)
val understand_gen_tcc :
  evar_map -> env -> var_map
    -> constr option -> rawconstr -> open_constr

(* Standard call to get a constr from a rawconstr, resolving implicit args *)
val understand : evar_map -> env -> rawconstr -> constr

(* Idem but the rawconstr is intended to be a type *)
val understand_type : evar_map -> env -> rawconstr -> constr

(* Idem but returns the judgment of the understood term *)
val understand_judgment : evar_map -> env -> rawconstr -> unsafe_judgment

(* Idem but returns the judgment of the understood type *)
val understand_type_judgment : evar_map -> env -> rawconstr 
  -> unsafe_type_judgment

(* To embed constr in rawconstr *)
val constr_in : constr -> Dyn.t
val constr_out : Dyn.t -> constr

(*i*)
(* Internal of Pretyping...
 * Unused outside, but useful for debugging
 *)
val pretype : 
  type_constraint -> env -> evar_defs -> 
    var_map * (identifier * identifier option) list ->
    rawconstr -> unsafe_judgment

val pretype_type : 
  val_constraint -> env -> evar_defs ->
    var_map * (identifier * identifier option) list ->
    rawconstr -> unsafe_type_judgment
(*i*)

val interp_sort : rawsort -> sorts

val interp_elimination_sort : rawsort -> sorts_family
