(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)
open Environ
open Tacmach
open Term
open Evd
open Names
open Util
open Tacinterp

val mkMetas : int -> constr list

val evar_dependencies : evar_map -> int -> Intset.t
val sort_dependencies : (int * evar_info * Intset.t) list -> (int * evar_info * Intset.t) list

(* env, id, evars, number of function prototypes to try to clear from
   evars contexts, object and type *)
val eterm_obligations : env -> identifier -> evar_map -> evar_map -> int ->
  ?status:obligation_definition_status -> constr -> types -> 
  (identifier * types * loc * obligation_definition_status * Intset.t * 
      tactic option) array
    (* Existential key, obl. name, type as product, location of the original evar, associated tactic,
       status and dependencies as indexes into the array *)
  * ((existential_key * identifier) list * ((identifier -> constr) -> constr -> constr)) * constr * types
    (* Translations from existential identifiers to obligation identifiers 
       and for terms with existentials to closed terms, given a 
       translation from obligation identifiers to constrs, new term, new type *)
