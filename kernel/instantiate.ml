
(* $Id$ *)

open Pp
open Util
open Names
(* open Generic *)
open Term
open Sign
open Evd
open Declarations
open Environ

let is_id_inst inst =
  let is_id = function
    | id, VAR id' -> id = id'
    | _ -> false
  in
  List.for_all is_id inst

let instantiate_constr sign c args =
  let inst = instantiate_vars sign args in
  if is_id_inst inst then
    c
  else
    replace_vars inst c

let instantiate_type sign tty args =
  typed_app (fun c -> instantiate_constr sign c args) tty

(* Constants. *)

(* constant_type gives the type of a constant *)
let constant_type env sigma (sp,args) =
  let cb = lookup_constant sp env in
  (* TODO: check args *)
  instantiate_type cb.const_hyps cb.const_type (Array.to_list args)

type const_evaluation_error = NotDefinedConst | OpaqueConst

exception NotEvaluableConst of const_evaluation_error

let constant_value env cst =
  let (sp,args) = destConst cst in
  let cb = lookup_constant sp env in
  if cb.const_opaque then raise (NotEvaluableConst OpaqueConst) else
  if not (is_defined cb) then raise (NotEvaluableConst NotDefinedConst) else
  match cb.const_body with
    | Some v -> 
	let body = cook_constant v in
        instantiate_constr cb.const_hyps body (Array.to_list args)
    | None ->
	anomalylabstrm "termenv__constant_value"
	  [< 'sTR "a defined constant with no body." >]

(* Existentials. *)

let name_of_existential n = id_of_string ("?" ^ string_of_int n)

let existential_type sigma (n,args) =
  let info = Evd.map sigma n in
  let hyps = evar_hyps info in
  (* TODO: check args [this comment was in Typeops] *)
  instantiate_constr hyps info.evar_concl (Array.to_list args)

let existential_value sigma (n,args) =
  let info = Evd.map sigma n in
  let hyps = evar_hyps info in
  match info.evar_body with
    | Evar_defined c ->
	instantiate_constr hyps c (Array.to_list args)
    | Evar_empty ->
	anomaly "a defined existential with no body"

let const_evar_opt_value env sigma c =
  match c with
    | DOPN(Const sp,_) ->
	if evaluable_constant env c then Some (constant_value env c) else None
    | DOPN(Evar ev,args) ->
	if Evd.is_defined sigma ev then 
	  Some (existential_value sigma (ev,args)) 
	else 
	  None
    | _ -> invalid_arg "const_abst_opt_value"

