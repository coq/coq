
(* $Id$ *)

open Names
open Term
open Sign

(* Inductive types (internal representation). *)

type recarg = 
  | Param of int 
  | Norec 
  | Mrec of int 
  | Imbr of section_path * int * (recarg list)

type mutual_inductive_packet = {
  mind_consnames : identifier array;
  mind_typename : identifier;
  mind_lc : constr;
  mind_arity : typed_type;
  mind_kelim : sorts list;
  mind_listrec : (recarg list) array;
  mind_finite : bool }

type mutual_inductive_body = {
  mind_kind : path_kind;
  mind_ntypes : int;
  mind_hyps : typed_type signature;
  mind_packets : mutual_inductive_packet array;
  mind_singl : constr option;
  mind_nparams : int }

val mind_type_finite : mutual_inductive_body -> int -> bool


(*s To give a more efficient access to the informations related to a given
  inductive type, we introduce the following type [mind_specif], which
  contains all the informations about the inductive type, including its
  instanciation arguments. *)

type mind_specif = {
  mis_sp : section_path;
  mis_mib : mutual_inductive_body;
  mis_tyi : int;
  mis_args : constr array;
  mis_mip : mutual_inductive_packet }

val mis_ntypes : mind_specif -> int
val mis_nconstr : mind_specif -> int
val mis_nparams : mind_specif -> int
val mis_kelim : mind_specif -> sorts list
val mis_recargs : mind_specif -> (recarg list) array array

val mind_nth_type_packet : 
  mutual_inductive_body -> int -> mutual_inductive_packet


(*s Declaration of inductive types. *)

type mutual_inductive_entry = {
  mind_entry_nparams : int;
  mind_entry_finite : bool;
  mind_entry_inds : (identifier * constr * identifier list * constr) list }

type inductive_error =
  | NonPos of int   
  | NotEnoughArgs of int
  | NotConstructor  
  | NonPar of int * int
  | SameNamesTypes of identifier
  | SameNamesConstructors of identifier * identifier
  | NotAnArity of identifier
  | BadEntry

exception InductiveError of inductive_error

val mind_check_names : mutual_inductive_entry -> unit

val mind_extract_params : int -> constr -> (name * constr) list * constr
val mind_extract_and_check_params : 
  mutual_inductive_entry -> (name * constr) list

val mind_check_lc : (name * constr) list -> mutual_inductive_entry -> unit
