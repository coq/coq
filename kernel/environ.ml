(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Author: Jean-Christophe Filliâtre as part of the rebuilding of Coq
   around a purely functional abstract type-checker, Aug 1999 *)
(* Cleaning and lightening of the kernel by Bruno Barras, Nov 2001 *)
(* Flag for predicativity of Set by Hugo Herbelin in Oct 2003 *)
(* Support for virtual machine by Benjamin Grégoire in Oct 2004 *)
(* Support for retroknowledge by Arnaud Spiwack in May 2007 *)
(* Support for assumption dependencies by Arnaud Spiwack in May 2007 *)

(* Miscellaneous maintenance by Bruno Barras, Hugo Herbelin, Jean-Marc
   Notin, Matthieu Sozeau *)

(* This file defines the type of environments on which the
   type-checker works, together with simple related functions *)

open Errors
open Util
open Names
open Term
open Context
open Vars
open Univ
open Declarations
open Pre_env

(* The type of environments. *)

type named_context_val = Pre_env.named_context_val

type env = Pre_env.env

let pre_env env = env
let env_of_pre_env env = env
let oracle env = env.env_conv_oracle
let set_oracle env o = { env with env_conv_oracle = o }

let empty_named_context_val = empty_named_context_val

let empty_env = empty_env

let engagement env = env.env_stratification.env_engagement
let universes env = env.env_stratification.env_universes
let named_context env = env.env_named_context
let named_context_val env = env.env_named_context,env.env_named_vals
let rel_context env = env.env_rel_context

let empty_context env =
  match env.env_rel_context, env.env_named_context with
  | [], [] -> true
  | _ -> false

(* Rel context *)
let lookup_rel n env =
  lookup_rel n env.env_rel_context

let evaluable_rel n env =
  match lookup_rel n env with
  | (_,Some _,_) -> true
  | _ -> false

let nb_rel env = env.env_nb_rel

let push_rel = push_rel

let push_rel_context ctxt x = Context.fold_rel_context push_rel ctxt ~init:x

let push_rec_types (lna,typarray,_) env =
  let ctxt = Array.map2_i (fun i na t -> (na, None, lift i t)) lna typarray in
  Array.fold_left (fun e assum -> push_rel assum e) env ctxt

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
let named_vals_of_val = snd

(* [map_named_val f ctxt] apply [f] to the body and the type of
   each declarations.
   *** /!\ ***   [f t] should be convertible with t *)
let map_named_val f (ctxt,ctxtv) =
  let rec map ctx = match ctx with
  | [] -> []
  | (id, body, typ) :: rem ->
    let body' = Option.smartmap f body in
    let typ' = f typ in
    let rem' = map rem in
    if body' == body && typ' == typ && rem' == rem then ctx
    else (id, body', typ') :: rem'
  in
  (map ctxt, ctxtv)

let empty_named_context = empty_named_context

let push_named = push_named
let push_named_context = List.fold_right push_named
let push_named_context_val = push_named_context_val

let val_of_named_context ctxt =
  List.fold_right push_named_context_val ctxt empty_named_context_val


let lookup_named id env = Context.lookup_named id env.env_named_context
let lookup_named_val id (ctxt,_) = Context.lookup_named id ctxt

let eq_named_context_val c1 c2 =
   c1 == c2 || named_context_equal (named_context_of_val c1) (named_context_of_val c2)

(* A local const is evaluable if it is defined  *)

let named_type id env =
  let (_,_,t) = lookup_named id env in t

let named_body id env =
  let (_,b,_) = lookup_named id env in b

let evaluable_named id env =
  match named_body id env with
  | Some _      -> true
  | _          -> false

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
  Context.fold_named_context_reverse f ~init:init (named_context env)

(* Global constants *)

let lookup_constant = lookup_constant

let no_link_info () = ref NotLinked

let add_constant_key kn cb linkinfo env =
  let new_constants =
    Cmap_env.add kn (cb,(linkinfo, ref None)) env.env_globals.env_constants in
  let new_globals =
    { env.env_globals with
	env_constants = new_constants } in
  { env with env_globals = new_globals }

let add_constant kn cb env =
  add_constant_key kn cb (no_link_info ()) env

(* constant_type gives the type of a constant *)
let constant_type env kn =
  let cb = lookup_constant kn env in
    cb.const_type

type const_evaluation_result = NoBody | Opaque

exception NotEvaluableConst of const_evaluation_result

let constant_value env kn =
  let cb = lookup_constant kn env in
  match cb.const_body with
    | Def l_body -> Mod_subst.force_constr l_body
    | OpaqueDef _ -> raise (NotEvaluableConst Opaque)
    | Undef _ -> raise (NotEvaluableConst NoBody)

let constant_opt_value env cst =
  try Some (constant_value env cst)
  with NotEvaluableConst _ -> None

(* A global const is evaluable if it is defined and not opaque *)
let evaluable_constant cst env =
  try let _  = constant_value env cst in true
  with NotEvaluableConst _ -> false

(* Mutual Inductives *)
let lookup_mind = lookup_mind

let add_mind_key kn mind_key env =
  let new_inds = Mindmap_env.add kn mind_key env.env_globals.env_inductives in
  let new_globals =
    { env.env_globals with
	env_inductives = new_inds } in
  { env with env_globals = new_globals }

let add_mind kn mib env =
  let li = no_link_info () in add_mind_key kn (mib, li) env

(* Universe constraints *)

let add_constraints c env =
  if is_empty_constraint c then
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
  Context.vars_of_named_context cmap.const_hyps

let lookup_inductive_variables (kn,i) env =
  let mis = lookup_mind kn env in
  Context.vars_of_named_context mis.mind_hyps

let lookup_constructor_variables (ind,_) env =
  lookup_inductive_variables ind env

(* Returns the list of global variables in a term *)

let vars_of_global env constr =
  match kind_of_term constr with
      Var id -> Id.Set.singleton id
    | Const kn -> lookup_constant_variables kn env
    | Ind ind -> lookup_inductive_variables ind env
    | Construct cstr -> lookup_constructor_variables cstr env
    | _ -> raise Not_found

let global_vars_set env constr =
  let rec filtrec acc c =
    let acc =
      match kind_of_term c with
      | Var _ | Const _ | Ind _ | Construct _ ->
	  Id.Set.union (vars_of_global env c) acc
      | _ ->
	  acc in
    fold_constr filtrec acc c
  in
    filtrec Id.Set.empty constr


(* [keep_hyps env ids] keeps the part of the section context of [env] which
   contains the variables of the set [ids], and recursively the variables
   contained in the types of the needed variables. *)

let really_needed env needed =
  Context.fold_named_context_reverse
    (fun need (id,copt,t) ->
      if Id.Set.mem id need then
        let globc =
          match copt with
            | None -> Id.Set.empty
            | Some c -> global_vars_set env c in
        Id.Set.union
          (global_vars_set env t)
          (Id.Set.union globc need)
      else need)
    ~init:needed
    (named_context env)

let keep_hyps env needed =
  let really_needed = really_needed env needed in
  Context.fold_named_context
    (fun (id,_,_ as d) nsign ->
      if Id.Set.mem id really_needed then add_named_decl d nsign
      else nsign)
    (named_context env)
    ~init:empty_named_context

(* Modules *)

let add_modtype mtb env =
  let mp = mtb.typ_mp in
  let new_modtypes = MPmap.add mp mtb env.env_globals.env_modtypes in
  let new_globals = { env.env_globals with env_modtypes = new_modtypes } in
  { env with env_globals = new_globals }

let shallow_add_module mb env =
  let mp = mb.mod_mp in
  let new_mods = MPmap.add mp mb env.env_globals.env_modules in
  let new_globals = { env.env_globals with env_modules = new_mods } in
  { env with env_globals = new_globals }

let lookup_module mp env =
    MPmap.find mp env.env_globals.env_modules


let lookup_modtype mp env = 
  MPmap.find mp env.env_globals.env_modtypes

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

let compile_constant_body = Cbytegen.compile_constant_body

exception Hyp_not_found

let apply_to_hyp (ctxt,vals) id f =
  let rec aux rtail ctxt vals =
    match ctxt, vals with
    | (idc,c,ct as d)::ctxt, v::vals ->
	if Id.equal idc id then
	  (f ctxt d rtail)::ctxt, v::vals
	else
	  let ctxt',vals' = aux (d::rtail) ctxt vals in
	  d::ctxt', v::vals'
    | [],[] -> raise Hyp_not_found
    | _, _ -> assert false
  in aux [] ctxt vals

let apply_to_hyp_and_dependent_on (ctxt,vals) id f g =
  let rec aux ctxt vals =
    match ctxt,vals with
    | (idc,c,ct as d)::ctxt, v::vals ->
	if Id.equal idc id then
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
	if Id.equal idc id then begin
	  check ctxt;
	  push_named_context_val d (ctxt,vals)
	end else
	  let ctxt,vals = aux ctxt vals in
	  d::ctxt, v::vals
    | [],[] -> raise Hyp_not_found
    | _, _ -> assert false
  in aux ctxt vals


(* To be used in Logic.clear_hyps *)
let remove_hyps ids check_context check_value (ctxt, vals) =
  let rec remove_hyps ctxt vals = match ctxt, vals with
  | [], [] -> [], []
  | d :: rctxt, (nid, v) :: rvals ->
    let (id, _, _) = d in
    let ans = remove_hyps rctxt rvals in
    if Id.Set.mem id ids then ans
    else
      let (rctxt', rvals') = ans in
      let d' = check_context d in
      let v' = check_value v in
      if d == d' && v == v' && rctxt == rctxt' && rvals == rvals' then
        ctxt, vals
      else (d' :: rctxt', (nid, v') :: rvals')
  | _ -> assert false
  in
  remove_hyps ctxt vals

(*spiwack: the following functions assemble the pieces of the retroknowledge
   note that the "consistent" register function is available in the module
   Safetyping, Environ only synchronizes the proactive and the reactive parts*)

open Retroknowledge

(* lifting of the "get" functions works also for "mem"*)
let retroknowledge f env =
  f env.retroknowledge

let registered env field =
    retroknowledge mem env field

(* spiwack: this unregistration function is not in operation yet. It should
            not be used *)
(* this unregistration function assumes that no "constr" can hold two different
   places in the retroknowledge. There is no reason why it shouldn't be true,
   but in case someone needs it, remember to add special branches to the
   unregister function *)
let unregister env field =
  match field with
    | KInt31 (_,Int31Type) ->
	(*there is only one matching kind due to the fact that Environ.env
          is abstract, and that the only function which add elements to the
          retroknowledge is Environ.register which enforces this shape *)
	(match kind_of_term (retroknowledge find env field) with
	   | Ind i31t -> let i31c = mkConstruct (i31t, 1) in
	     {env with retroknowledge =
		 remove (retroknowledge clear_info env i31c) field}
	   | _ -> assert false)
    |_ -> {env with retroknowledge =
	   try
	     remove (retroknowledge clear_info env
                       (retroknowledge find env field)) field
	   with Not_found ->
	     retroknowledge remove env field}



(* the Environ.register function syncrhonizes the proactive and reactive
   retroknowledge. *)
let register =

  (* subfunction used for static decompilation of int31 (after a vm_compute,
     see pretyping/vnorm.ml for more information) *)
  let constr_of_int31 =
    let nth_digit_plus_one i n = (* calculates the nth (starting with 0)
                                    digit of i and adds 1 to it
                                    (nth_digit_plus_one 1 3 = 2) *)
      if Int.equal (i land (1 lsl n)) 0 then
        1
      else
        2
    in
      fun ind -> fun digit_ind -> fun tag ->
	let array_of_int i =
	  Array.init 31 (fun n -> mkConstruct
			   (digit_ind, nth_digit_plus_one i (30-n)))
	in
	  mkApp(mkConstruct(ind, 1), array_of_int tag)
  in

  (* subfunction which adds the information bound to the constructor of
     the int31 type to the reactive retroknowledge *)
  let add_int31c retroknowledge c =
    let rk = add_vm_constant_static_info retroknowledge c
                                         Cbytegen.compile_structured_int31
    in
    let rk =
      add_vm_constant_dynamic_info rk c Cbytegen.dynamic_int31_compilation
    in
    let rk =
      add_native_constant_static_info rk c Nativelambda.compile_static_int31
    in
    add_native_constant_dynamic_info rk c Nativelambda.compile_dynamic_int31
  in

  (* subfunction which adds the compiling information of an
     int31 operation which has a specific vm instruction (associates
     it to the name of the coq definition in the reactive retroknowledge) *)
  let add_int31_op retroknowledge v n op prim kn =
    let rk =
      add_vm_compiling_info retroknowledge v (Cbytegen.op_compilation n op kn)
    in
    add_native_compiling_info rk v (Nativelambda.compile_prim prim kn)
  in

  let add_int31_before_match rk grp v =
    let rk = add_vm_before_match_info rk v Cbytegen.int31_escape_before_match in
    match kind_of_term (Retroknowledge.find rk (KInt31 (grp,Int31Bits))) with
    | Ind i31bit_type ->
    add_native_before_match_info rk v (Nativelambda.before_match_int31 i31bit_type)
    | _ ->
       anomaly ~label:"Environ.register" (Pp.str "Int31Bits should be an inductive type")
  in

fun env field value ->
  (* subfunction which shortens the (very often use) registration of binary
     operators to the reactive retroknowledge. *)
  let add_int31_binop_from_const op prim =
    match kind_of_term value with
      | Const kn ->  retroknowledge add_int31_op env value 2
	                               op prim kn
      | _ -> anomaly ~label:"Environ.register" (Pp.str "should be a constant")
  in
  let add_int31_unop_from_const op prim =
    match kind_of_term value with
      | Const kn ->  retroknowledge add_int31_op env value 1
	                               op prim kn
      | _ -> anomaly ~label:"Environ.register" (Pp.str "should be a constant")
  in
  (* subfunction which completes the function constr_of_int31 above
     by performing the actual retroknowledge operations *)
  let add_int31_decompilation_from_type rk =
    (* invariant : the type of bits is registered, otherwise the function
       would raise Not_found. The invariant is enforced in safe_typing.ml *)
    match field with
      | KInt31 (grp, Int31Type) ->
	  (match kind_of_term (Retroknowledge.find rk (KInt31 (grp,Int31Bits))) with
	    | Ind i31bit_type ->
		(match kind_of_term value with
		  | Ind i31t ->
		      Retroknowledge.add_vm_decompile_constant_info rk
		               value (constr_of_int31 i31t i31bit_type)
		  | _ -> anomaly ~label:"Environ.register" (Pp.str "should be an inductive type"))
	    | _ -> anomaly ~label:"Environ.register" (Pp.str "Int31Bits should be an inductive type"))
      | _ -> anomaly ~label:"Environ.register" (Pp.str "add_int31_decompilation_from_type called with an abnormal field")
  in
  {env with retroknowledge =
  let retroknowledge_with_reactive_info =
  match field with
    | KInt31 (grp, Int31Type) ->
        let i31c = match kind_of_term value with
                     | Ind i31t -> mkConstruct (i31t, 1)
		     | _ -> anomaly ~label:"Environ.register" (Pp.str "should be an inductive type")
	in
	add_int31_decompilation_from_type
	  (add_int31_before_match
	     (retroknowledge add_int31c env i31c) grp value)
    | KInt31 (_, Int31Plus) -> add_int31_binop_from_const Cbytecodes.Kaddint31
							  Primitives.Int31add
    | KInt31 (_, Int31PlusC) -> add_int31_binop_from_const Cbytecodes.Kaddcint31
							   Primitives.Int31addc
    | KInt31 (_, Int31PlusCarryC) -> add_int31_binop_from_const Cbytecodes.Kaddcarrycint31
								Primitives.Int31addcarryc
    | KInt31 (_, Int31Minus) -> add_int31_binop_from_const Cbytecodes.Ksubint31
							   Primitives.Int31sub
    | KInt31 (_, Int31MinusC) -> add_int31_binop_from_const Cbytecodes.Ksubcint31
							    Primitives.Int31subc
    | KInt31 (_, Int31MinusCarryC) -> add_int31_binop_from_const
	                                Cbytecodes.Ksubcarrycint31 Primitives.Int31subcarryc
    | KInt31 (_, Int31Times) -> add_int31_binop_from_const Cbytecodes.Kmulint31
							   Primitives.Int31mul
    | KInt31 (_, Int31TimesC) -> add_int31_binop_from_const Cbytecodes.Kmulcint31
							    Primitives.Int31mulc
    | KInt31 (_, Int31Div21) -> (* this is a ternary operation *)
                                (match kind_of_term value with
				 | Const kn ->
				     retroknowledge add_int31_op env value 3
	                               Cbytecodes.Kdiv21int31 Primitives.Int31div21 kn
				 | _ -> anomaly ~label:"Environ.register" (Pp.str "should be a constant"))
    | KInt31 (_, Int31Div) -> add_int31_binop_from_const Cbytecodes.Kdivint31
							 Primitives.Int31div
    | KInt31 (_, Int31AddMulDiv) -> (* this is a ternary operation *)
                                (match kind_of_term value with
				 | Const kn ->
				     retroknowledge add_int31_op env value 3
	                               Cbytecodes.Kaddmuldivint31 Primitives.Int31addmuldiv kn
				 | _ -> anomaly ~label:"Environ.register" (Pp.str "should be a constant"))
    | KInt31 (_, Int31Compare) -> add_int31_binop_from_const Cbytecodes.Kcompareint31
							     Primitives.Int31compare
    | KInt31 (_, Int31Head0) -> add_int31_unop_from_const Cbytecodes.Khead0int31
							  Primitives.Int31head0
    | KInt31 (_, Int31Tail0) -> add_int31_unop_from_const Cbytecodes.Ktail0int31
							  Primitives.Int31tail0
    | KInt31 (_, Int31Lor) -> add_int31_binop_from_const Cbytecodes.Klorint31
							 Primitives.Int31lor
    | KInt31 (_, Int31Land) -> add_int31_binop_from_const Cbytecodes.Klandint31
							  Primitives.Int31land
    | KInt31 (_, Int31Lxor) -> add_int31_binop_from_const Cbytecodes.Klxorint31
							  Primitives.Int31lxor
    | _ -> env.retroknowledge
  in
  Retroknowledge.add_field retroknowledge_with_reactive_info field value
  }
