
(* $Id$ *)

(*i*)
open Names
open Sign
open Term
open Environ
open Evd
open Rawterm
(*i*)

val type_of_com : context -> Coqast.t -> typed_type

val constr_of_com_casted : 'c evar_map -> context -> Coqast.t -> constr ->
  constr

val constr_of_com1 : bool -> 'c evar_map -> context -> Coqast.t -> constr
val constr_of_com : 'c evar_map -> context -> Coqast.t -> constr
val constr_of_com_sort : 'c evar_map -> context -> Coqast.t -> constr

val fconstr_of_com1 : bool -> 'c evar_map -> context -> Coqast.t -> constr
val fconstr_of_com : 'c evar_map -> context -> Coqast.t -> constr
val fconstr_of_com_sort : 'c evar_map -> context -> Coqast.t -> constr


(* Typing with Trad, and re-checking with Mach *)
(*i
val fconstruct :'c evar_map -> context -> Coqast.t -> judgement
val fconstruct_type :
  'c evar_map -> context -> Coqast.t -> type_judgement

val infconstruct_type :
  'c evar_map -> (context * context) ->
    Coqast.t -> type_judgement * information
val infconstruct :
  'c evar_map -> (context * context) ->
    Coqast.t -> judgement * information

(* Typing, re-checking with universes constraints *)
val fconstruct_with_univ :
  'c evar_map -> context -> Coqast.t -> judgement
val fconstruct_with_univ_sp : 'c evar_map -> context
  -> section_path -> constr -> Impuniv.universes * judgement
val fconstruct_type_with_univ_sp : 'c evar_map -> context
  -> section_path -> constr -> Impuniv.universes * type_judgement
val infconstruct_with_univ_sp :
  'c evar_map -> (context * context)
  -> section_path -> constr -> Impuniv.universes * (judgement * information)
val infconstruct_type_with_univ_sp :
  'c evar_map -> (context * context)
  -> section_path -> constr 
  -> Impuniv.universes * (type_judgement * information)
i*)

(* Low level typing functions, for terms with de Bruijn indices and Metas *)

(* Raw calls to the inference machine of Trad: boolean says if we must fail
 * on unresolved evars, or replace them by Metas *)
val ise_resolve : bool -> 'c evar_map -> (int * constr) list ->
  context -> rawconstr -> unsafe_judgment
val ise_resolve_type : bool -> 'c evar_map -> (int * constr) list ->
  context -> rawconstr -> typed_type

(* Call ise_resolve with empty metamap and fail_evar=true. The boolean says
 * if we must coerce to a type *)
val ise_resolve1 : bool -> 'c evar_map -> context -> rawconstr -> constr

(* progmach.ml tries to type ill-typed terms: does not perform the conversion
 * test in application.
 *)
val ise_resolve_nocheck : 'c evar_map -> (int * constr) list ->
  context -> rawconstr -> unsafe_judgment


(* Internal of Trad...
 * Unused outside Trad, but useful for debugging
 *)
val pretype : bool * (constr option * constr option) -> 'c evar_map ref
  -> context -> rawconstr -> unsafe_judgment
