
(* $Id$ *)

(*i*)
open Names
open Sign
open Term
open Environ
open Evd
open Rawterm
open Evarutil
(*i*)

(* Typing with Trad, and re-checking with Mach *)
(*i
val infconstruct_type :
  'c evar_map -> (env * env) ->
    Coqast.t -> typed_type * information
val infconstruct :
  'c evar_map -> (env * env) ->
    Coqast.t -> unsafe_judgment * information

(* Typing, re-checking with universes constraints *)
val fconstruct_with_univ :
  'c evar_map -> env -> Coqast.t -> unsafe_judgment
val fconstruct_with_univ_sp : 'c evar_map -> env
  -> section_path -> constr -> Impuniv.universes * unsafe_judgment
val fconstruct_type_with_univ_sp : 'c evar_map -> env
  -> section_path -> constr -> Impuniv.universes * typed_type
val infconstruct_with_univ_sp :
  'c evar_map -> (env * env)
  -> section_path -> constr -> Impuniv.universes * (unsafe_judgment * information)
val infconstruct_type_with_univ_sp :
  'c evar_map -> (env * env)
  -> section_path -> constr 
  -> Impuniv.universes * (typed_type * information)
i*)

(* Low level typing functions, for terms with de Bruijn indices and Metas *)

(* Raw calls to the inference machine of Trad: boolean says if we must fail
 * on unresolved evars, or replace them by Metas *)
val ise_resolve : bool -> unit evar_map -> (int * constr) list ->
  env -> rawconstr -> unsafe_judgment
val ise_resolve_type : bool -> unit evar_map -> (int * constr) list ->
  env -> rawconstr -> typed_type

(* Call [ise_resolve] with empty metamap and [fail_evar=true]. The boolean says
 * if we must coerce to a type *)
val ise_resolve1 : bool -> unit evar_map -> env -> rawconstr -> constr

(* progmach.ml tries to type ill-typed terms: does not perform the conversion
 * test in application.
 *)
val ise_resolve_nocheck : unit evar_map -> (int * constr) list ->
  env -> rawconstr -> unsafe_judgment


(* Internal of Trad...
 * Unused outside Trad, but useful for debugging
 *)
val pretype : 
  trad_constraint -> env -> unit evar_defs -> rawconstr 
    -> unsafe_judgment
