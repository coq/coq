
(* $Id$ *)

(*i*)
open Evd
open Term
open Sign
open Environ
open Evarutil
(*i*)

(*s Coercions. *)

val inh_app_fun :
  env -> 'a evar_defs -> unsafe_judgment -> unsafe_judgment
val inh_tosort_force :
  env -> 'a evar_defs -> unsafe_judgment -> unsafe_judgment

(* [inh_tosort env sigma j] insert a coercion into [j], if needed, in
   such a way [t] reduces to a sort; it fails if no coercion is applicable *)
val inh_tosort :
  env -> 'a evar_defs -> unsafe_judgment -> unsafe_judgment

val inh_ass_of_j :
  env -> 'a evar_defs -> unsafe_judgment -> unsafe_type_judgment

(* [inh_conv_coerce_to loc env sigma j t] insert a coercion into [j],
   if needed, in such a way it [t] and [j.uj_type] are convertible; it
   fails if no coercion is applicable *)
val inh_conv_coerce_to : Rawterm.loc ->
  env -> 'a evar_defs -> unsafe_judgment -> constr -> unsafe_judgment

(* [inh_apply_rel_list loc env isevars args f tycon] tries to type [(f
   args)] of type [tycon] (if any) by inserting coercions in front of
   each arg$_i$, if necessary *)
val inh_apply_rel_list : Rawterm.loc -> env -> 'a evar_defs ->
  unsafe_judgment list -> unsafe_judgment -> constr option
    -> unsafe_judgment
