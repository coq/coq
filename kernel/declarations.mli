
(* $Id$ *)

(*i*)
open Names
open Univ
open Term
open Sign
(*i*)

(*s Constants (internal representation). *)

type lazy_constant_value =
  | Cooked of constr
  | Recipe of (unit -> constr)

type constant_value = lazy_constant_value ref

type constant_body = {
  const_kind : path_kind;
  const_body : constant_value option;
  const_type : typed_type;
  const_hyps : typed_type signature;
  const_constraints : constraints;
  mutable const_opaque : bool }

val is_defined : constant_body -> bool

val is_opaque : constant_body -> bool

val cook_constant : constant_value -> constr

(*s Constant declaration. *)

type constant_entry = {
  const_entry_body : lazy_constant_value;
  const_entry_type : constr option }

(*s Inductive types (internal representation). *)

type recarg = 
  | Param of int 
  | Norec 
  | Mrec of int 
  | Imbr of inductive_path * (recarg list)

(* [mind_typename] is the name of the inductive; [mind_arity] is
   the arity generalized over global parameters; [mind_lc] is the list
   of types of constructors generalized over global parameters and
   relative to the global context enriched with the arities of the
   inductives *) 

type one_inductive_body = {
  mind_consnames : identifier array;
  mind_typename : identifier;
  mind_lc : typed_type array;
  mind_arity : typed_type;
  mind_sort : sorts;
  mind_nrealargs : int;
  mind_kelim : sorts list;
  mind_listrec : (recarg list) array;
  mind_finite : bool }

type mutual_inductive_body = {
  mind_kind : path_kind;
  mind_ntypes : int;
  mind_hyps : typed_type signature;
  mind_packets : one_inductive_body array;
  mind_constraints : constraints;
  mind_singl : constr option;
  mind_nparams : int }

val mind_type_finite : mutual_inductive_body -> int -> bool

val mind_nth_type_packet : 
  mutual_inductive_body -> int -> one_inductive_body

(*s Declaration of inductive types. *)

type mutual_inductive_entry = {
  mind_entry_nparams : int;
  mind_entry_finite : bool;
  mind_entry_inds : (identifier * constr * identifier list * constr list) list}

