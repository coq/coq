
(* $Id$ *)

(*i*)
open Names
open Term
open Constant
open Inductive
open Abstraction
open Univ
open Sign
(*i*)

(* Unsafe environments. We define here a datatype for environments. 
   Since typing is not yet defined, it is not possible to check the
   informations added in environments, and that is what we speak here
   of ``unsafe'' environments. *)

type unsafe_env

val empty_env : unsafe_env

val universes : unsafe_env -> universes
val context : unsafe_env -> context

val push_var : identifier * typed_type -> unsafe_env -> unsafe_env
val change_hyps : 
  (typed_type signature -> typed_type signature) -> unsafe_env -> unsafe_env

val push_rel : name * typed_type -> unsafe_env -> unsafe_env

val set_universes : universes -> unsafe_env -> unsafe_env
val add_constraints : constraints -> unsafe_env -> unsafe_env
val add_constant : 
  section_path -> constant_body -> unsafe_env -> unsafe_env
val add_mind : 
  section_path -> mutual_inductive_body -> unsafe_env -> unsafe_env
val add_abstraction : 
  section_path -> abstraction_body -> unsafe_env -> unsafe_env

val new_meta : unit -> int

val lookup_var : identifier -> unsafe_env -> name * typed_type
val lookup_rel : int -> unsafe_env -> name * typed_type
val lookup_constant : section_path -> unsafe_env -> constant_body
val lookup_mind : section_path -> unsafe_env -> mutual_inductive_body
val lookup_mind_specif : constr -> unsafe_env -> mind_specif

val id_of_global : unsafe_env -> sorts oper -> identifier
val id_of_name_using_hdchar : unsafe_env -> constr -> name -> identifier
val named_hd : unsafe_env -> constr -> name -> name
val prod_name : unsafe_env -> name * constr * constr -> constr

val translucent_abst : unsafe_env -> constr -> bool
val evaluable_abst : unsafe_env -> constr -> bool
val abst_value : unsafe_env -> constr -> constr

val defined_constant : unsafe_env -> constr -> bool
val evaluable_constant : unsafe_env -> constr -> bool

(*s Modules. *)

type compiled_env

val export : unsafe_env -> string -> compiled_env
val import : compiled_env -> unsafe_env -> unsafe_env

(*s Unsafe judgments. We introduce here the pre-type of judgments, which is
  actually only a datatype to store a term with its type and the type of its
  type. *)

type unsafe_judgment = { 
  uj_val : constr;
  uj_type : constr;
  uj_kind : constr }

val cast_of_judgment : unsafe_judgment -> constr
