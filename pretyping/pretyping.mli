(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

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

type meta_map = (int * unsafe_judgment) list
type var_map = (identifier * unsafe_judgment) list

(* constr with holes *)
type open_constr = (existential * types) list * constr


(* Generic call to the interpreter from rawconstr to constr, failing
   unresolved holes in the rawterm cannot be instantiated.

   In [understand_gen sigma env varmap metamap typopt raw],

   sigma : initial set of existential variables (typically dependent subgoals)
   varmap : partial subtitution of variables (used for the tactic language)
   metamap : partial subtitution of meta (used for the tactic language)
   typopt : is not None, this is the expected type for raw (used to define evars)
*)
val understand_gen :
  'a evar_map -> env -> var_map -> meta_map 
    -> expected_type:(constr option) -> rawconstr -> constr


(* Generic call to the interpreter from rawconstr to constr, turning
   unresolved holes into metas. Returns also the typing context of
   these metas. Work as [understand_gen] for the rest. *)
val understand_gen_tcc :
  'a evar_map -> env -> var_map -> meta_map 
    -> constr option -> rawconstr -> open_constr

(* Standard call to get a constr from a rawconstr, resolving implicit args *)
val understand : 'a evar_map -> env -> rawconstr -> constr

(* Idem but the rawconstr is intended to be a type *)
val understand_type : 'a evar_map -> env -> rawconstr -> constr

(* Idem but returns the judgment of the understood term *)
val understand_judgment : 'a evar_map -> env -> rawconstr -> unsafe_judgment

(* Idem but returns the judgment of the understood type *)
val understand_type_judgment : 'a evar_map -> env -> rawconstr 
  -> unsafe_type_judgment

(* To embed constr in rawconstr *)
val constr_in : constr -> Dyn.t
val constr_out : Dyn.t -> constr

(*i*)
(* Internal of Pretyping...
 * Unused outside, but useful for debugging
 *)
val pretype : 
  type_constraint -> env -> 'a evar_defs -> var_map -> meta_map ->
    rawconstr -> unsafe_judgment

val pretype_type : 
  val_constraint -> env -> 'a evar_defs -> var_map -> meta_map ->
    rawconstr -> unsafe_type_judgment
(*i*)
