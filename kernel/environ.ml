(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Util
open Names
open Sign
open Univ
open Term
open Declarations
open Pre_env
open Csymtable

(* The type of environments. *)

type named_context_val = Pre_env.named_context_val

type env = Pre_env.env

let pre_env env = env

let empty_named_context_val = empty_named_context_val

let empty_env = empty_env

let engagement env = env.env_stratification.env_engagement
let universes env = env.env_stratification.env_universes
let named_context env = env.env_named_context
let named_context_val env = env.env_named_context,env.env_named_vals
let rel_context env = env.env_rel_context

let empty_context env = 
  env.env_rel_context = empty_rel_context 
  && env.env_named_context = empty_named_context

(* Rel context *)
let lookup_rel n env =
  Sign.lookup_rel n env.env_rel_context

let evaluable_rel n env =
  try
    match lookup_rel n env with
        (_,Some _,_) -> true
      | _ -> false
  with Not_found -> 
    false

let nb_rel env = env.env_nb_rel

let push_rel = push_rel

let push_rel_context ctxt x = Sign.fold_rel_context push_rel ctxt ~init:x
    
let push_rec_types (lna,typarray,_) env =
  let ctxt =
    array_map2_i
      (fun i na t -> (na, None, type_app (lift i) t)) lna typarray in
  Array.fold_left (fun e assum -> push_rel assum e) env ctxt
    
let reset_rel_context env =
  { env with
    env_rel_context = empty_rel_context;
    env_rel_val = [];
    env_nb_rel = 0 }

let fold_rel_context f env ~init =
  let rec fold_right env =
    match env.env_rel_context with
    | [] -> init
    | rd::rc ->
	let env = 
	  { env with
	    env_rel_context = rc;
	    env_rel_val = List.tl env.env_rel_val;
	    env_nb_rel = env.env_nb_rel - 1 } in
	f env rd (fold_right env) 
  in fold_right env

(* Named context *)

let named_context_of_val = fst

(* [map_named_val f ctxt] apply [f] to the body and the type of
   each declarations.
   *** /!\ ***   [f t] should be convertible with t *)  
let map_named_val f (ctxt,ctxtv) = 
  let ctxt =
    List.map (fun (id,body,typ) -> (id, option_map f body, f typ)) ctxt in
  (ctxt,ctxtv)

let empty_named_context = empty_named_context 

let push_named = push_named
let push_named_context_val = push_named_context_val

let val_of_named_context ctxt =
  List.fold_right push_named_context_val ctxt empty_named_context_val


let lookup_named id env = Sign.lookup_named id env.env_named_context
let lookup_named_val id (ctxt,_) = Sign.lookup_named id ctxt

let eq_named_context_val c1 c2 =
   c1 == c2 || named_context_of_val c1 = named_context_of_val c2

(* A local const is evaluable if it is defined  *)

let named_type id env =
  let (_,_,t) = lookup_named id env in t

let named_body id env =
  let (_,b,_) = lookup_named id env in b

let evaluable_named id env =
  try 
    match named_body id env with
    |Some _      -> true
    | _          -> false
  with Not_found -> false
      
let reset_with_named_context (ctxt,ctxtv) env =
  { env with
    env_named_context = ctxt;
    env_named_vals = ctxtv;
    env_rel_context = empty_rel_context;
    env_rel_val = [];
    env_nb_rel = 0 }

let reset_context = reset_with_named_context empty_named_context_val
 
let fold_named_context f env ~init =
  let rec fold_right env =
    match env.env_named_context with
    | [] -> init
    | d::ctxt ->
	let env = 
	  reset_with_named_context (ctxt,List.tl env.env_named_vals) env in
	f env d (fold_right env) 
  in fold_right env

let fold_named_context_reverse f ~init env =
  Sign.fold_named_context_reverse f ~init:init (named_context env)
 
(* Global constants *)

let lookup_constant = lookup_constant

let add_constant kn cs env =
  let new_constants = 
    Cmap.add kn (cs,ref None) env.env_globals.env_constants in
  let new_globals = 
    { env.env_globals with 
	env_constants = new_constants } in 
  { env with env_globals = new_globals }

(* constant_type gives the type of a constant *)
let constant_type env kn =
  let cb = lookup_constant kn env in
  cb.const_type  

type const_evaluation_result = NoBody | Opaque

exception NotEvaluableConst of const_evaluation_result

let constant_value env kn =
  let cb = lookup_constant kn env in
  if cb.const_opaque then raise (NotEvaluableConst Opaque);
  match cb.const_body with
    | Some l_body -> Declarations.force l_body
    | None -> raise (NotEvaluableConst NoBody)

let constant_opt_value env cst =
  try Some (constant_value env cst)
  with NotEvaluableConst _ -> None

(* A global const is evaluable if it is defined and not opaque *)
let evaluable_constant cst env =
  try let _  = constant_value env cst in true
  with Not_found | NotEvaluableConst _ -> false

(* Mutual Inductives *)
let lookup_mind = lookup_mind
let scrape_mind = scrape_mind


let add_mind kn mib env =
  let new_inds = KNmap.add kn mib env.env_globals.env_inductives in
  let new_globals = 
    { env.env_globals with 
	env_inductives = new_inds } in
  { env with env_globals = new_globals }

(* Universe constraints *)
let set_universes g env =
  if env.env_stratification.env_universes == g then env
  else
    { env with env_stratification = 
      { env.env_stratification with env_universes = g } }

let add_constraints c env =
  if c == Constraint.empty then 
    env 
  else
    let s = env.env_stratification in
    { env with env_stratification = 
      { s with env_universes = merge_constraints c s.env_universes } }

let set_engagement c env = (* Unsafe *)
  { env with env_stratification =
    { env.env_stratification with env_engagement = Some c } }

(* Lookup of section variables *)
let lookup_constant_variables c env =
  let cmap = lookup_constant c env in
  Sign.vars_of_named_context cmap.const_hyps

let lookup_inductive_variables (kn,i) env =
  let mis = lookup_mind kn env in
  Sign.vars_of_named_context mis.mind_hyps

let lookup_constructor_variables (ind,_) env =
  lookup_inductive_variables ind env

(* Returns the list of global variables in a term *)

let vars_of_global env constr =
  match kind_of_term constr with
      Var id -> [id]
    | Const kn -> lookup_constant_variables kn env
    | Ind ind -> lookup_inductive_variables ind env
    | Construct cstr -> lookup_constructor_variables cstr env
    | _ -> []

let global_vars_set env constr = 
  let rec filtrec acc c =
    let vl = vars_of_global env c in
    let acc = List.fold_right Idset.add vl acc in
      fold_constr filtrec acc c
  in 
    filtrec Idset.empty constr

(* like [global_vars] but don't get through evars *)
let global_vars_set_drop_evar env constr = 
  let fold_constr_drop_evar f acc c = match kind_of_term c with
    | (Rel _ | Meta _ | Var _   | Sort _ | Const _ | Ind _
      | Construct _) -> acc
    | Cast (c,_,t) -> f (f acc c) t
    | Prod (_,t,c) -> f (f acc t) c
    | Lambda (_,t,c) -> f (f acc t) c
    | LetIn (_,b,t,c) -> f (f (f acc b) t) c
    | App (c,l) -> Array.fold_left f (f acc c) l
    | Evar (_,l) -> acc
    | Case (_,p,c,bl) -> Array.fold_left f (f (f acc p) c) bl
    | Fix (_,(lna,tl,bl)) ->
	let fd = array_map3 (fun na t b -> (na,t,b)) lna tl bl in
	  Array.fold_left (fun acc (na,t,b) -> f (f acc t) b) acc fd
    | CoFix (_,(lna,tl,bl)) ->
	let fd = array_map3 (fun na t b -> (na,t,b)) lna tl bl in
	  Array.fold_left (fun acc (na,t,b) -> f (f acc t) b) acc fd in
  let rec filtrec acc c =
    let vl = vars_of_global env c in
    let acc = List.fold_right Idset.add vl acc in
      fold_constr_drop_evar filtrec acc c
  in 
    filtrec Idset.empty constr

(* [keep_hyps env ids] keeps the part of the section context of [env] which 
   contains the variables of the set [ids], and recursively the variables 
   contained in the types of the needed variables. *)

let keep_hyps env needed =
  let really_needed =
    Sign.fold_named_context_reverse
      (fun need (id,copt,t) ->
        if Idset.mem id need then
          let globc = 
	    match copt with
	      | None -> Idset.empty
	      | Some c -> global_vars_set env c in
	  Idset.union
            (global_vars_set env t) 
	    (Idset.union globc need)
        else need)
      ~init:needed
      (named_context env) in
  Sign.fold_named_context
    (fun (id,_,_ as d) nsign ->
      if Idset.mem id really_needed then add_named_decl d nsign
      else nsign)
    (named_context env)
    ~init:empty_named_context

(* Modules *)

let add_modtype ln mtb env = 
  let new_modtypes = KNmap.add ln mtb env.env_globals.env_modtypes in
  let new_globals = 
    { env.env_globals with 
	env_modtypes = new_modtypes } in
  { env with env_globals = new_globals }

let shallow_add_module mp mb env = 
  let new_mods = MPmap.add mp mb env.env_globals.env_modules in
  let new_globals = 
    { env.env_globals with 
	env_modules = new_mods } in
  { env with env_globals = new_globals }

let lookup_module mp env = 
  MPmap.find mp env.env_globals.env_modules

let lookup_modtype ln env = 
  KNmap.find ln env.env_globals.env_modtypes

(*s Judgments. *)

type unsafe_judgment = { 
  uj_val : constr;
  uj_type : types }

let make_judge v tj =
  { uj_val = v;
    uj_type = tj }

let j_val j = j.uj_val
let j_type j = j.uj_type

type unsafe_type_judgment = { 
  utj_val : constr;
  utj_type : sorts }

(*s Compilation of global declaration *)


let compile_constant_body = Cbytegen.compile_constant_body false

exception Hyp_not_found

let rec apply_to_hyp (ctxt,vals) id f =
  let rec aux rtail ctxt vals =
    match ctxt, vals with
    | (idc,c,ct as d)::ctxt, v::vals ->
	if idc = id then
	  (f ctxt d rtail)::ctxt, v::vals
	else 
	  let ctxt',vals' = aux (d::rtail) ctxt vals in
	  d::ctxt', v::vals'
    | [],[] -> raise Hyp_not_found
    | _, _ -> assert false
  in aux [] ctxt vals

let rec apply_to_hyp_and_dependent_on (ctxt,vals) id f g =
  let rec aux ctxt vals =
    match ctxt,vals with
    | (idc,c,ct as d)::ctxt, v::vals ->
	if idc = id then
	  let sign = ctxt,vals in
	  push_named_context_val (f d sign) sign 
	else 
	  let (ctxt,vals as sign) = aux ctxt vals in
	  push_named_context_val (g d sign) sign
    | [],[] -> raise Hyp_not_found
    | _,_ -> assert false
  in aux ctxt vals

let insert_after_hyp (ctxt,vals) id d check =
  let rec aux ctxt vals =
    match  ctxt, vals with
    | (idc,c,ct)::ctxt', v::vals' ->
	if idc = id then begin
	  check ctxt; 
	  push_named_context_val d (ctxt,vals) 
	end else 
	  let ctxt,vals = aux ctxt vals in
	  d::ctxt, v::vals
    | [],[] -> raise Hyp_not_found
    | _, _ -> assert false
  in aux ctxt vals

(* To be used in Logic.clear_hyps *)
let remove_hyps ids check (ctxt, vals) =
  let ctxt,vals,rmv = 
    List.fold_right2 (fun (id,_,_ as d) v (ctxt,vals,rmv) ->
      if List.mem id ids then 
	(ctxt,vals,id::rmv)
      else 	  
	let nd = check d in
	  (nd::ctxt,v::vals,rmv))
		     ctxt vals ([],[],[])
  in ((ctxt,vals),rmv)

