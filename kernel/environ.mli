
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

type env

val empty_env : env

val universes : env -> universes
val context : env -> context
val var_context : env -> var_context

val push_var : identifier * typed_type -> env -> env
val change_hyps : 
  (typed_type signature -> typed_type signature) -> env -> env
val change_name_rel : env -> int -> identifier -> env

val push_rel : name * typed_type -> env -> env

val set_universes : universes -> env -> env
val add_constraints : constraints -> env -> env
val add_constant : 
  section_path -> constant_body -> env -> env
val add_mind : 
  section_path -> mutual_inductive_body -> env -> env
val add_abstraction : 
  section_path -> abstraction_body -> env -> env

val new_meta : unit -> int

val lookup_var : identifier -> env -> name * typed_type
val lookup_rel : int -> env -> name * typed_type
val lookup_constant : section_path -> env -> constant_body
val lookup_mind : section_path -> env -> mutual_inductive_body
val lookup_mind_specif : inductive -> env -> mind_specif

val id_of_global : env -> sorts oper -> identifier

val id_of_name_using_hdchar : env -> constr -> name -> identifier
val named_hd : env -> constr -> name -> name
val prod_name : env -> name * constr * constr -> constr
val lambda_create : env -> constr * constr -> constr

val translucent_abst : env -> constr -> bool
val evaluable_abst : env -> constr -> bool
val abst_value : env -> constr -> constr

val defined_constant : env -> constr -> bool
val evaluable_constant : env -> constr -> bool

(*s Modules. *)

type compiled_env

val export : env -> string -> compiled_env
val import : compiled_env -> env -> env

(*s Unsafe judgments. We introduce here the pre-type of judgments, which is
  actually only a datatype to store a term with its type and the type of its
  type. *)

type unsafe_judgment = { 
  uj_val : constr;
  uj_type : constr;
  uj_kind : constr }

val cast_of_judgment : unsafe_judgment -> constr
