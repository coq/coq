
(* $Id$ *)

(*i*)
open Names
open Univ
open Term
open Sign
(*i*)

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
  mind_constraints : constraints;
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
val mis_recarg : mind_specif -> (recarg list) array
val mis_typename : mind_specif -> identifier
val mis_is_recursive : mind_specif -> bool

val mind_nth_type_packet : 
  mutual_inductive_body -> int -> mutual_inductive_packet


(*s Declaration of inductive types. *)

type mutual_inductive_entry = {
  mind_entry_nparams : int;
  mind_entry_finite : bool;
  mind_entry_inds : (identifier * constr * identifier list * constr) list }

(*s The different kinds of errors that may result of a malformed inductive
  definition. *)

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

(*s The following functions are utility functions to check and to
  decompose a declaration. *)

(* [mind_check_names] checks the names of an inductive types declaration
   i.e. that all the types and constructors names are distinct. 
   It raises an exception [InductiveError _] if it is not the case. *)

val mind_check_names : mutual_inductive_entry -> unit

(* [mind_extract_and_check_params] extracts the parameters of an inductive
   types declaration. It raises an exception [InductiveError _] if there is
   not enough abstractions in any of the terms of the field 
   [mind_entry_inds]. *)

val mind_extract_and_check_params : 
  mutual_inductive_entry -> (name * constr) list

val mind_extract_params : int -> constr -> (name * constr) list * constr

val mind_check_lc : (name * constr) list -> mutual_inductive_entry -> unit
