
(* $Id$ *)

open Pp
open Util
open Names
open Generic
open Term
open Sign
open Constant
open Inductive
open Environ

let is_id_inst ids args =
  let is_id id = function
    | VAR id' -> id = id'
    | _ -> false
  in
  List.for_all2 is_id ids args

let instantiate_constr ids c args =
  if is_id_inst ids args then
    c
  else
    replace_vars (List.combine ids (List.map make_substituend args)) c

let instantiate_type ids tty args =
  { body = instantiate_constr ids tty.body args;
    typ = tty.typ }

(* Constants. *)

(* constant_type gives the type of a constant *)
let constant_type env k =
  let (sp,args) = destConst k in
  let cb = lookup_constant sp env in
  instantiate_type 
    (ids_of_sign cb.const_hyps) cb.const_type (Array.to_list args)

let constant_value env k =
  let (sp,args) = destConst k in
  let cb = lookup_constant sp env in
  if not cb.const_opaque & defined_constant env k then
    match cb.const_body with
      Some { contents = Cooked body } -> 
        instantiate_constr 
	  (ids_of_sign cb.const_hyps) body (Array.to_list args)
    | Some { contents = Recipe _ } ->
        anomalylabstrm "termenv__constant_value"
          [< 'sTR "a transparent constant which was not cooked" >]
    | None -> anomalylabstrm "termenv__constant_value"
          [< 'sTR "a defined constant as no body." >]
  else failwith "opaque"

let const_abst_opt_value env c =
  match c with
    | DOPN(Const sp,_) ->
	if evaluable_constant env c then Some (constant_value env c) else None
    | DOPN(Abst sp,_) ->
	if evaluable_abst env c then Some (abst_value env c) else None
    | _ -> invalid_arg "const_abst_opt_value"

let mis_lc env mis =
  instantiate_constr (ids_of_sign mis.mis_mib.mind_hyps) mis.mis_mip.mind_lc
    (Array.to_list mis.mis_args)

