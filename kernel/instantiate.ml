
(* $Id$ *)

open Pp
open Util
open Names
open Generic
open Term
open Sign
open Evd
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
      | Some v -> 
	  let body = cook_constant v in
          instantiate_constr 
	    (ids_of_sign cb.const_hyps) body (Array.to_list args)
      | None -> 
	  anomalylabstrm "termenv__constant_value"
	    [< 'sTR "a defined constant with no body." >]
  else 
    failwith "opaque"


let mis_lc mis =
  instantiate_constr (ids_of_sign mis.mis_mib.mind_hyps) mis.mis_mip.mind_lc
    (Array.to_list mis.mis_args)

let mis_lc_without_abstractions mis = 
  let rec strip_DLAM = function
    | (DLAM (n,c1)) -> strip_DLAM c1 
    | (DLAMV (n,v)) -> v
    | _ -> assert false
  in 
  strip_DLAM (mis_lc mis)

let mis_type_mconstructs mispec =
  let specif = mis_lc mispec
  and ntypes = mis_ntypes mispec
  and nconstr = mis_nconstr mispec in
  let make_Ik k = DOPN(MutInd(mispec.mis_sp,k),mispec.mis_args) 
  and make_Ck k = DOPN(MutConstruct((mispec.mis_sp,mispec.mis_tyi),k+1),
		       mispec.mis_args) in
  (Array.init nconstr make_Ck, 
   sAPPVList specif (list_tabulate make_Ik ntypes))

(* Existentials. *)

let name_of_existential n = id_of_string ("?" ^ string_of_int n)

let existential_type sigma c =
  let (n,args) = destEvar c in
  let info = Evd.map sigma n in
  let hyps = evar_hyps info in
  instantiate_constr (ids_of_sign hyps) info.evar_concl
    (Array.to_list args)

let existential_value sigma c =
  let (n,args) = destEvar c in
  let info = Evd.map sigma n in
  let hyps = evar_hyps info in
  match info.evar_body with
    | Evar_defined c ->
	instantiate_constr (ids_of_sign hyps) c (Array.to_list args)
    | Evar_empty ->
	anomaly "a defined existential with no body"

let const_abst_opt_value env sigma c =
  match c with
    | DOPN(Const sp,_) ->
	if evaluable_constant env c then Some (constant_value env c) else None
    | DOPN(Evar ev,_) ->
	if Evd.is_defined sigma ev then 
	  Some (existential_value sigma c) 
	else 
	  None
    | DOPN(Abst sp,_) ->
	if evaluable_abst env c then Some (abst_value env c) else None
    | _ -> invalid_arg "const_abst_opt_value"

let mis_typed_arity mis =
  let idhyps = ids_of_sign mis.mis_mib.mind_hyps 
  and largs = Array.to_list mis.mis_args in
  instantiate_type idhyps mis.mis_mip.mind_arity largs

let mis_arity mispec =
  let { body = b; typ = t } = mis_typed_arity mispec in
  DOP2 (Cast, b, DOP0 (Sort t))

