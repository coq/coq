
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

type constant_body = {
  const_kind : path_kind;
  const_body : recipe ref option;
  const_type : typed_type;
  const_hyps : context;
  mutable const_opaque : bool;
  mutable const_eval : ((int * constr) list * int * bool) option option;
}

type constant_entry = section_path * constant_body

let is_defined cb = 
  match cb.const_body with Some _ -> true | _ -> false

let is_opaque cb = cb.const_opaque
