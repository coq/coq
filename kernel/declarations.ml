
(* $Id$ *)

open Names
open Univ
open Term
open Sign

(* Constant entries *)

type constant_body = {
  const_kind : path_kind;
  const_body : constr option;
  const_type : types;
  const_hyps : section_context;
  const_constraints : constraints;
  mutable const_opaque : bool }

let is_defined cb = 
  match cb.const_body with Some _ -> true | _ -> false

let is_opaque cb = cb.const_opaque

(*s Global and local constant declaration. *)

type constant_entry = {
  const_entry_body : constr;
  const_entry_type : constr option }

type local_entry =
  | LocalDef of constr
  | LocalAssum of constr

(* Inductive entries *)

type recarg = 
  | Param of int 
  | Norec 
  | Mrec of int 
  | Imbr of inductive_path * recarg list

type one_inductive_body = {
  mind_consnames : identifier array;
  mind_typename : identifier;
  mind_nf_lc : types array;
  mind_nf_arity : types;
  (* lc and arity as given by user if not in nf; useful e.g. for Ensemble.v *)
  mind_user_lc : types array option;
  mind_user_arity : types option;
  mind_sort : sorts;
  mind_nrealargs : int;
  mind_kelim : sorts list;
  mind_listrec : (recarg list) array;
  mind_finite : bool;
  mind_nparams : int;
  mind_params_ctxt : rel_context }

type mutual_inductive_body = {
  mind_kind : path_kind;
  mind_ntypes : int;
  mind_hyps : section_context;
  mind_packets : one_inductive_body array;
  mind_constraints : constraints;
  mind_singl : constr option }

let mind_type_finite mib i = mib.mind_packets.(i).mind_finite

let mind_user_lc mip = match mip.mind_user_lc with
  | None -> mip.mind_nf_lc
  | Some lc -> lc

let mind_user_arity mip = match mip.mind_user_arity with
  | None -> mip.mind_nf_arity
  | Some a -> a

(*s Declaration. *)

type one_inductive_entry = {
  mind_entry_nparams : int;
  mind_entry_params : (identifier * local_entry) list;
  mind_entry_typename : identifier;
  mind_entry_arity : constr;
  mind_entry_consnames : identifier list;
  mind_entry_lc : constr list }

type mutual_inductive_entry = {
  mind_entry_finite : bool;
  mind_entry_inds : one_inductive_entry list }

let mind_nth_type_packet mib n = mib.mind_packets.(n)

let mind_arities_context mib =
  Array.to_list
    (Array.map  (* No need to lift, arities contain no de Bruijn *)
       (fun mip -> (Name mip.mind_typename, None, mind_user_arity mip))
       mib.mind_packets)
