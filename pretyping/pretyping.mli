
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

(* Raw calls to the inference machine of Trad: boolean says if we must fail
   on unresolved evars, or replace them by Metas ; the [unsafe_judgment] list
   allows us to extend env with some bindings *)
val ise_infer_gen : bool -> 'a evar_map -> (int * constr) list ->
  env -> (identifier * unsafe_judgment) list ->
  (int * unsafe_judgment) list -> rawconstr -> unsafe_judgment

(* Standard call to get an unsafe judgment from a rawconstr, resolving
   implicit args *)
val ise_infer : 'a evar_map -> env -> rawconstr -> unsafe_judgment

(* Standard call to get an unsafe type judgment from a rawconstr, resolving
   implicit args *)
val ise_infer_type : 'a evar_map -> env -> rawconstr -> unsafe_type_judgment

(* Standard call to get a constr from a rawconstr, resolving implicit args *)
val ise_resolve      : 'a evar_map -> env -> rawconstr -> constr

(* Idem but the rawconstr is intended to be a type *)
val ise_resolve_type : 'a evar_map -> env -> rawconstr -> constr

val ise_resolve2 : 'a evar_map -> env -> (identifier * unsafe_judgment) list ->
  (int * unsafe_judgment) list -> rawconstr -> constr

val ise_resolve_casted_gen :
  bool -> 'a evar_map -> env -> (identifier * unsafe_judgment) list ->
    (int * unsafe_judgment) list -> constr -> rawconstr -> constr
val ise_resolve_casted : 'a evar_map -> env -> constr -> rawconstr -> constr

(* progmach.ml tries to type ill-typed terms: does not perform the conversion
 * test in application.
 *)
val ise_infer_nocheck : 'a evar_map -> (int * constr) list ->
  env -> rawconstr -> unsafe_judgment

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

(*i*)
(* Internal of Pretyping...
 * Unused outside, but useful for debugging
 *)
val pretype : 
  type_constraint -> env -> 'a evar_defs ->
    (identifier * unsafe_judgment) list -> (int * unsafe_judgment) list ->
    rawconstr -> unsafe_judgment

val pretype_type : 
  val_constraint -> env -> 'a evar_defs ->
    (identifier * unsafe_judgment) list -> (int * unsafe_judgment) list ->
    rawconstr -> unsafe_judgment
(*i*)
