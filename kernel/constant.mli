
(* $Id$ *)

(*i*)
open Names
open Univ
open Term
open Sign
(*i*)

(* Constants (internal representation). *)

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

type constant_entry= {
  const_entry_body : lazy_constant_value;
  const_entry_type : constr option }

