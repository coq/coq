
open Evd
open Term
open Sign
open Environ
open Evarutil


val inh_app_fun : 'a evar_defs -> 'b -> unsafe_judgment -> unsafe_judgment
val inh_tosort_force : 'a evar_defs -> 'b -> unsafe_judgment -> unsafe_judgment
val inh_tosort : 'a evar_defs -> 'b -> unsafe_judgment -> unsafe_judgment
val inh_ass_of_j : 'a evar_defs -> var_context ->
  unsafe_judgment -> typed_type
val inh_coerce_to : 'a evar_defs -> var_context ->
  constr -> unsafe_judgment -> unsafe_judgment
val inh_cast_rel : 'a evar_defs -> var_context ->
  unsafe_judgment -> unsafe_judgment -> unsafe_judgment
val inh_apply_rel_list : bool -> 'a evar_defs -> var_context ->
  unsafe_judgment list -> unsafe_judgment -> 'b * ('c * constr option) 
    -> unsafe_judgment
