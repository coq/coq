
(* $Id$ *)

open Names
open Generic
open Term
open Sign

type discharge_recipe = {
  d_expand : section_path list;
  d_modify : (sorts oper * sorts oper modification) list;
  d_abstract : identifier list;
  d_from : section_path }

type recipe =
  | Cooked of constr
  | Recipe of discharge_recipe

type constant_entry = {
  const_entry_body : constr;
  const_entry_type : constr }

type constant_body = {
  const_kind : path_kind;
  const_body : recipe ref option;
  const_type : typed_type;
  const_hyps : typed_type signature;
  mutable const_opaque : bool }

let is_defined cb = 
  match cb.const_body with Some _ -> true | _ -> false

let is_opaque cb = cb.const_opaque
