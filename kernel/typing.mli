
(* $Id$ *)

(*i*)
open Pp
open Names
open Term
open Univ
open Evd
open Sign
open Constant
open Inductive
open Environ
open Typeops
(*i*)

(*s Safe environments. *)

type 'a environment

val empty_environment : 'a environment

val evar_map : 'a environment -> 'a evar_map
val universes : 'a environment -> universes
val metamap : 'a environment -> (int * constr) list
val context : 'a environment -> context

val push_var : identifier * constr -> 'a environment -> 'a environment
val push_rel : name * constr -> 'a environment -> 'a environment
val add_constant : 
  section_path -> constant_entry -> 'a environment -> 'a environment
val add_parameter :
  section_path -> constr -> 'a environment -> 'a environment
val add_mind : 
  section_path -> mutual_inductive_entry -> 'a environment -> 'a environment

val lookup_var : identifier -> 'a environment -> name * typed_type
val lookup_rel : int -> 'a environment -> name * typed_type
val lookup_constant : section_path -> 'a environment -> constant_body
val lookup_mind : section_path -> 'a environment -> mutual_inductive_body
val lookup_mind_specif : constr -> 'a environment -> mind_specif
val lookup_meta : int -> 'a environment -> constr

(*s Typing without information. *)

type judgment

val j_val : judgment -> constr
val j_type : judgment -> constr
val j_kind : judgment -> constr

val safe_machine : 'a environment -> constr -> judgment * universes
val safe_machine_type : 'a environment -> constr -> typed_type

val fix_machine : 'a environment -> constr -> judgment * universes
val fix_machine_type : 'a environment -> constr -> typed_type

val unsafe_machine : 'a environment -> constr -> judgment * universes
val unsafe_machine_type : 'a environment -> constr -> typed_type

val type_of : 'a environment -> constr -> constr

val type_of_type : 'a environment -> constr -> constr

val unsafe_type_of : 'a environment -> constr -> constr


(*s Typing with information (extraction). *)

type information = Logic | Inf of judgment


