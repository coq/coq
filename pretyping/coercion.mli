
(* $Id$ *)

(*i*)
open Evd
open Term
open Sign
open Environ
open Evarutil
(*i*)

(* Coercions. *)

val inh_app_fun :
  env -> 'a evar_defs -> unsafe_judgment -> unsafe_judgment
val inh_tosort_force :
  env -> 'a evar_defs -> unsafe_judgment -> unsafe_judgment
val inh_tosort :
  env -> 'a evar_defs -> unsafe_judgment -> unsafe_judgment
val inh_ass_of_j : 
  env -> 'a evar_defs -> unsafe_judgment -> unsafe_type_judgment

val inh_conv_coerce_to : Rawterm.loc ->
  env -> 'a evar_defs -> unsafe_judgment -> typed_type -> unsafe_judgment

val inh_apply_rel_list : bool -> Rawterm.loc -> env -> 'a evar_defs ->
  unsafe_judgment list -> unsafe_judgment -> constr option
    -> unsafe_judgment
