
(* $Id$ *)

(*i*)
open Evd
open Term
open Sign
open Environ
open Evarutil
(*i*)

(*s Coercions. *)

(* [inh_app_fun env isevars j] coerces [j] to a function; i.e. it
   inserts a coercion into [j], if needed, in such a way it gets as
   type a product; it returns [j] if no coercion is applicable *)
val inh_app_fun :
  env -> 'a evar_defs -> unsafe_judgment -> unsafe_judgment

(* [inh_coerce_to_sort env isevars j] coerces [j] to a type; i.e. it
   inserts a coercion into [j], if needed, in such a way it gets as
   type a sort; it fails if no coercion is applicable *)
val inh_coerce_to_sort :
  env -> 'a evar_defs -> unsafe_judgment -> unsafe_type_judgment

(* [inh_conv_coerce_to loc env isevars j t] coerces [j] to an object of type 
   [t]; i.e. it inserts a coercion into [j], if needed, in such a way [t] and
   [j.uj_type] are convertible; it fails if no coercion is applicable *)
val inh_conv_coerce_to : Rawterm.loc -> 
  env -> 'a evar_defs -> unsafe_judgment -> constr -> unsafe_judgment

(* [inh_apply_rel_list loc env isevars args f tycon] tries to type [(f
   args)] of type [tycon] (if any) by inserting coercions in front of
   each arg$_i$, if necessary *)
val inh_apply_rel_list : Rawterm.loc -> env -> 'a evar_defs ->
  (Rawterm.loc * unsafe_judgment) list ->
    (Rawterm.loc * unsafe_judgment) -> constr option -> unsafe_judgment

