
(* $Id$ *)

(*i*)
open Names
open Term
open Constant
open Inductive
open Abstraction
open Evd
open Univ
open Sign
(*i*)

(* Unsafe environments. We define here a datatype for environments. 
   Since typing is not yet defined, it is not possible to check the
   informations added in environments, and that is what we speak here
   of ``unsafe'' environments. *)

type 'a unsafe_env

val empty_env : 'a unsafe_env

val evar_map : 'a unsafe_env -> 'a evar_map
val universes : 'a unsafe_env -> universes
val metamap : 'a unsafe_env -> (int * constr) list
val context : 'a unsafe_env -> context

val push_var : identifier * typed_type -> 'a unsafe_env -> 'a unsafe_env
val push_rel : name * typed_type -> 'a unsafe_env -> 'a unsafe_env
val set_universes : universes -> 'a unsafe_env -> 'a unsafe_env
val add_constant : 
  section_path -> constant_body -> 'a unsafe_env -> 'a unsafe_env
val add_mind : 
  section_path -> mutual_inductive_body -> 'a unsafe_env -> 'a unsafe_env
val add_abstraction : 
  section_path -> abstraction_body -> 'a unsafe_env -> 'a unsafe_env

val new_meta : unit -> int

val lookup_var : identifier -> 'a unsafe_env -> name * typed_type
val lookup_rel : int -> 'a unsafe_env -> name * typed_type
val lookup_constant : section_path -> 'a unsafe_env -> constant_body
val lookup_mind : section_path -> 'a unsafe_env -> mutual_inductive_body
val lookup_mind_specif : constr -> 'a unsafe_env -> mind_specif
val lookup_meta : int -> 'a unsafe_env -> constr

val id_of_global : 'a unsafe_env -> sorts oper -> identifier
val id_of_name_using_hdchar : 'a unsafe_env -> constr -> name -> identifier
val named_hd : 'a unsafe_env -> constr -> name -> name
val prod_name : 'a unsafe_env -> name * constr * constr -> constr

val translucent_abst : 'a unsafe_env -> constr -> bool
val evaluable_abst : 'a unsafe_env -> constr -> bool
val abst_value : 'a unsafe_env -> constr -> constr

val defined_const : 'a unsafe_env -> constr -> bool
val translucent_const : 'a unsafe_env -> constr -> bool
val evaluable_const : 'a unsafe_env -> constr -> bool

val is_existential : constr -> bool

(*s Modules. *)

type compiled_env

val export : 'a unsafe_env -> string -> compiled_env
val import : compiled_env -> 'a unsafe_env -> 'a unsafe_env

(*s Unsafe judgments. We introduce here the pre-type of judgments, which is
  actually only a datatype to store a term with its type and the type of its
  type. *)

type unsafe_judgment = { 
  uj_val : constr;
  uj_type : constr;
  uj_kind : constr }

val cast_of_judgment : unsafe_judgment -> constr
