
(* $Id$ *)

open Names
open Univ
open Generic
open Term
open Sign

type constant_entry = {
  const_entry_body : constr;
  const_entry_type : constr option }

type constant_body = {
  const_kind : path_kind;
  const_body : constr option;
  const_type : typed_type;
  const_hyps : typed_type signature;
  const_constraints : constraints;
  mutable const_opaque : bool }

let is_defined cb = 
  match cb.const_body with Some _ -> true | _ -> false

let is_opaque cb = cb.const_opaque
