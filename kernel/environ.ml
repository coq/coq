(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
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

open Util
open Names
open Sign
open Univ
open Term
open Declarations
open Pre_env

(* The type of environments. *)

type named_context_val = Pre_env.named_context_val

type env = Pre_env.env

let pre_env env = env
let env_of_pre_env env = env

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
  lookup_rel n env.env_rel_context

let evaluable_rel n env =
  match lookup_rel n env with
  | (_,Some _,_) -> true
  | _ -> false

let nb_rel env = env.env_nb_rel

let push_rel = push_rel

let push_rel_context ctxt x = Sign.fold_rel_context push_rel ctxt ~init:x

let push_rec_types (lna,typarray,_) env =
  let ctxt = array_map2_i (fun i na t -> (na, None, lift i t)) lna typarray in
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
  let ctxt =
    List.map (fun (id,body,typ) -> (id, Option.map f body, f typ)) ctxt in
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
  Sign.fold_named_context_reverse f ~init:init (named_context env)

(* Global constants *)

let lookup_constant = lookup_constant

let add_constant kn cs env =
  let new_constants =
    Cmap_env.add kn (cs,ref None) env.env_globals.env_constants in
  let new_globals =
    { env.env_globals with
	env_constants = new_constants } in
  { env with env_globals = new_globals }

(* constant_type gives the type of a constant *)
let constant_type env kn =
  let cb = lookup_constant kn env in
    cb.const_type

type const_evaluation_result = CteNoBody | CteOpaque | CtePrim of Native.op

exception NotEvaluableConst of const_evaluation_result

let constant_value1 env kn = (lookup_constant kn env).const_body 

let constant_value_def env kn =
  match constant_value1 env kn with
  | Def l_body -> Declarations.force l_body
  | Opaque None -> raise (NotEvaluableConst CteNoBody)
  | Opaque (Some _) -> raise (NotEvaluableConst CteOpaque)
  | Primitive op -> raise (NotEvaluableConst (CtePrim op))

let constant_opt_value1 env cst =
  try Some (constant_value_def env cst)
  with NotEvaluableConst _ -> None

(* A global const is evaluable if it is defined and not opaque *)
let evaluable_constant1 cst env =
  try let _  = constant_value_def env cst in true
  with NotEvaluableConst _ -> false

let evaluable_constant_prim cst env =
  try let _  = constant_value_def env cst in true
  with NotEvaluableConst (CtePrim _) -> true
  | NotEvaluableConst _ -> false
(* Mutual Inductives *)
let lookup_mind = lookup_mind
  
let add_mind kn mib env =
  let new_inds = Mindmap_env.add kn mib env.env_globals.env_inductives in
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
    | _ -> raise Not_found

let global_vars_set env constr =
  let rec filtrec acc c =
    let acc =
      match kind_of_term c with
      | Var _ | Const _ | Ind _ | Construct _ ->
	  List.fold_right Idset.add (vars_of_global env c) acc
      | _ ->
	  acc in
    fold_constr filtrec acc c
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
  let new_modtypes = MPmap.add ln mtb env.env_globals.env_modtypes in
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
let remove_hyps ids check_context check_value (ctxt, vals) =
  List.fold_right2 (fun (id,_,_ as d) (id',v) (ctxt,vals) ->
      if List.mem id ids then
	(ctxt,vals)
      else
	let nd = check_context d in
	let nv = check_value v in
	  (nd::ctxt,(id',nv)::vals))
		     ctxt vals ([],[])




(* Reduction of native operators *)
open Native

let retroknowledge env = env.env_retroknowledge

let add_retroknowledge env (pt,c) = 
  match pt with
  | Retro_type PT_int31 ->
      let cte = destConst c in
      let retro = retroknowledge env in
      let retro = 
	match retro.retro_int31 with
	| None -> { retro with retro_int31 = Some (cte,c) }
	| Some(cte',_) -> assert (cte = cte'); retro in
      { env with env_retroknowledge = retro }
  | Retro_type PT_array ->
      let cte = destConst c in
      let retro = retroknowledge env in
      let retro = 
	match retro.retro_array with
	| None -> { retro with retro_array = Some (cte,c) }
	| Some(cte',_) -> assert (cte = cte'); retro in
      { env with env_retroknowledge = retro }
  | Retro_ind pit ->
      let ind = destInd c in
      let retro = retroknowledge env in
      let retro =
	match pit with
	| PIT_bool ->
	    let r = 
	      match retro.retro_bool with
	      | None -> ((ind,1), (ind,2))
	      | Some (((ind',_),_) as t) -> assert (ind = ind'); t in
	    { retro with retro_bool = Some r }
	| PIT_carry ->
	    let r =
	      match retro.retro_carry with
	      | None -> ((ind,1), (ind,2))
	      | Some (((ind',_),_) as t) -> assert (ind = ind'); t in
	    { retro with retro_carry = Some r }
	| PIT_pair ->
	    let r =
	      match retro.retro_pair with
	      | None -> (ind,1)
	      | Some ((ind',_) as t) -> assert (ind = ind'); t in
	    { retro with retro_pair = Some r }
	| PIT_cmp ->
	    let r = 
	      match retro.retro_cmp with
	      | None -> ((ind,1), (ind,2), (ind,3)) 
	      | Some (((ind',_),_,_) as t) -> assert (ind = ind'); t in
	    { retro with retro_cmp = Some r } 
      in
      { env with env_retroknowledge = retro }
  | Retro_inline ->
      let kn = destConst c in
      let (cb,r) = Cmap_env.find kn env.env_globals.env_constants in
      let cb = {cb with const_inline_code = true} in 
      let new_constants =
	Cmap_env.add kn (cb,r) env.env_globals.env_constants in
      let new_globals =
	{ env.env_globals with
	  env_constants = new_constants } in
      { env with env_globals = new_globals }

module type RedNativeEntries =
  sig
    type elem
    type args
    module Parray : PARRAY

    val get : args -> int -> elem
    val get_int :  elem -> Uint31.t
    val get_parray : elem -> elem * elem Parray.t
    val mkInt : env -> Uint31.t -> elem
    val mkBool : env -> bool -> elem
    val mkCarry : env -> bool -> elem -> elem (* true if carry *)
    val mkPair : env -> elem -> elem -> elem
    val mkLt : env -> elem
    val mkEq : env -> elem
    val mkGt : env -> elem
    val mkArray : env -> elem -> elem Parray.t -> elem
    val mkClos : name -> constr -> constr -> elem array -> elem

  end

module type RedNative =
 sig
   type elem
   type args
   val red_prim : env -> prim_op -> args -> elem
   val red_caml_prim : env -> caml_prim -> args -> elem
   val red_iterator : env -> iterator -> constr -> args -> elem
      (* the constr represente the iterator *)
   val red_op : env -> op -> constr -> args -> elem option
 end

module RedNative (E:RedNativeEntries) :
    RedNative with type elem = E.elem
    with type args = E.args =
  struct
    type elem = E.elem
    type args = E.args

    let get_int args i = E.get_int (E.get args i)
      
    let get_int1 args = get_int args 0

    let get_int2 args = get_int args 0, get_int args 1 
 
    let get_int3 args = 
      get_int args 0, get_int args 1, get_int args 2

    let get_parray args i = E.get_parray (E.get args i)

    let red_prim env op args =
      match op with  
      | Int31head0      -> 
	  let i = get_int1 args in E.mkInt env (Uint31.head0 i)
      | Int31tail0      ->
	  let i = get_int1 args in E.mkInt env (Uint31.tail0 i)
      | Int31add        ->
	  let i1, i2 = get_int2 args in E.mkInt env (Uint31.add i1 i2)
      | Int31sub        ->
	  let i1, i2 = get_int2 args in E.mkInt env (Uint31.sub i1 i2)
      | Int31mul        ->
	  let i1, i2 = get_int2 args in E.mkInt env (Uint31.mul i1 i2)
      | Int31div        ->
	  let i1, i2 = get_int2 args in E.mkInt env (Uint31.div i1 i2)
      | Int31mod        ->
	  let i1, i2 = get_int2 args in E.mkInt env (Uint31.rem i1 i2)
      | Int31lsr        ->
	  let i1, i2 = get_int2 args in E.mkInt env (Uint31.l_sr i1 i2)
      | Int31lsl        ->
	  let i1, i2 = get_int2 args in E.mkInt env (Uint31.l_sl i1 i2)
      | Int31land       ->
	  let i1, i2 = get_int2 args in E.mkInt env (Uint31.l_and i1 i2)
      | Int31lor        ->
	  let i1, i2 = get_int2 args in E.mkInt env (Uint31.l_or i1 i2)
      | Int31lxor       ->
	  let i1, i2 = get_int2 args in E.mkInt env (Uint31.l_xor i1 i2)
      | Int31addc       ->
	  let i1, i2 = get_int2 args in 
	  let s = Uint31.add i1 i2 in
	  E.mkCarry env (Uint31.lt s i1) (E.mkInt env s)
      | Int31subc       ->
	  let i1, i2 = get_int2 args in 
	  let s = Uint31.sub i1 i2 in
	  E.mkCarry env (Uint31.lt i1 i2) (E.mkInt env s)
      | Int31addCarryC  ->
	  let i1, i2 = get_int2 args in 
	  let s = Uint31.add (Uint31.add i1 i2) (Uint31.of_int 1) in
	  E.mkCarry env (Uint31.le s i1) (E.mkInt env s)
      | Int31subCarryC  ->
	  let i1, i2 = get_int2 args in 
	  let s = Uint31.sub (Uint31.sub i1 i2) (Uint31.of_int 1) in
	  E.mkCarry env (Uint31.le i1 i2) (E.mkInt env s)
      | Int31mulc       ->
	  let i1, i2 = get_int2 args in 
	  let (h, l) = Uint31.mulc i1 i2 in
	  E.mkPair env (E.mkInt env h) (E.mkInt env l)
      | Int31diveucl    ->
	  let i1, i2 = get_int2 args in 
	  let q,r = Uint31.div i1 i2, Uint31.rem i1 i2 in
	  E.mkPair env (E.mkInt env q) (E.mkInt env r)
      | Int31div21      ->
	  let i1, i2, i3 = get_int3 args in 
	  let q,r = Uint31.div21 i1 i2 i3 in
	  E.mkPair env (E.mkInt env q) (E.mkInt env r)
      | Int31addMulDiv  ->
	  let p, i, j = get_int3 args in 
	  let p' = Uint31.to_int p in
	  E.mkInt env 
	    (Uint31.l_or 
	       (Uint31.l_sl i p) 
	       (Uint31.l_sr j (Uint31.of_int (31 - p'))))
      | Int31eq         ->
	  let i1, i2 = get_int2 args in 
	  E.mkBool env (Uint31.eq i1 i2)
      | Int31lt         ->
	  let i1, i2 = get_int2 args in 
	  E.mkBool env (Uint31.lt i1 i2)
      | Int31le         ->
	  let i1, i2 = get_int2 args in 
	  E.mkBool env (Uint31.le i1 i2)
      | Int31compare    ->
	  let i1, i2 = get_int2 args in 
	  match Uint31.compare i1 i2 with
	  | x when x < 0 ->  E.mkLt env
	  | 0 -> E.mkEq env
	  | _ -> E.mkGt env
	  	  
    let red_caml_prim env op args =
      match op with
      | Int31print      -> 
	  let i = get_int1 args in
	  Printf.fprintf stdout "%s\n" (Uint31.to_string i);flush stdout;
	  E.mkInt env i
      | ArrayMake       ->
	  let t = E.get args 0 in
	  let i = get_int args 1 in
	  let d = E.get args 2 in
	  E.mkArray env t (E.Parray.make i d)
      | ArrayGet        ->
	  let (_,p) = get_parray args 1 in
	  let i = get_int args 2 in
	  E.Parray.get p i
      | ArrayGetdefault ->
	  let (_,p) = get_parray args 1 in
	  E.Parray.default p 
      | ArraySet        ->
	  let (t,p) = get_parray args 1 in
	  let i = get_int args 2 in
	  let a = E.get args 3 in
	  let p' = E.Parray.set p i a in
	  E.mkArray env t p'
      | ArrayCopy       ->
	  let t, p = get_parray args 1 in
	  let p' = E.Parray.copy p in
          E.mkArray env t p'
      | ArrayReroot     -> 
	  let ar = E.get args 1 in
	  let _, p = E.get_parray ar in
	  let _ = E.Parray.reroot p in
	  ar
      | ArrayLength     ->
	  let (_,p) = get_parray args 1 in
	  E.mkInt env (E.Parray.length p)

    (* Reduction des iterateurs *)
    (* foldi_cont A B f min max cont 
     *     ---> min < max
     *       lam a. f min (foldi A B f (min + 1) max cont) a  
     *    ---> min = max
     *       lam a. f min cont a
     *    ---> min > max
     *       lam a. cont a 
     *)


    let red_iterator env op it args =
      match op with
      | Int31foldi ->
	  let _A = E.get args 0 in
	  let _B = E.get args 1 in
	  let f = E.get args 2 in
	  let min = get_int args 3 in
	  let max = get_int args 4 in
	  let cont = E.get args 5 in
	  let subst = (*[|_A;_B;f;E.get args 3 (* min *);
			E.get args 4 (* max *);cont|] *)  
                      [|cont; E.get args 4 (* max *);
			E.get args 3;f;_B;_A|] in
          (* _A->#1;_B->#2;f->#3;min->#4;max ->#5;cont->#6 *)
	  let name = Name (id_of_string "a") in
	  let typ =  mkRel 1 (*_A*) in
	  (* a->#1;_A->#2;_B->#3;f->#4;min->#5;max ->#6;cont->#7 *)
	  let body =
	    if Uint31.lt min max then 
	      begin
		let minp1 = Uint31.add min (Uint31.of_int 1) in
		mkApp (mkRel 4(*f*),
		       [|mkRel 5 (* min *);
			 mkApp (it,
				[|mkRel 2 (* _A *);
				  mkRel 3 (* _B *);
				  mkRel 4 (* f *);
				  mkInt minp1; (* min + 1 *)
				  mkRel 6 (* max *);
				  mkRel 7 (* cont *)
				|]);
			 mkRel 1 (* a*)
		       |])
	      end
	    else 
	      if Uint31.eq min max then 
		mkApp(mkRel 4(*f *),
		      [| mkRel 5; (* min *)
			 mkRel 7; (* cont *)
			 mkRel 1  (* a *)
		       |])
	      else 
		mkApp(mkRel 7,[|mkRel 1|])
	  in
	  E.mkClos name typ body subst
      | Int31foldi_down ->
	  let _A = E.get args 0 in
	  let _B = E.get args 1 in
	  let f = E.get args 2 in
	  let min = get_int args 4 in
	  let max = get_int args 3 in
	  let cont = E.get args 5 in
	  let subst = [|cont; E.get args 3 (* max *);
			E.get args 4;f;_B;_A|] in
          (* _A->#1;_B->#2;f->#3;min->#4;max ->#5;cont->#6 *)
	  let name = Name (id_of_string "a") in
	  let typ =  mkRel 1 (*_A*) in
	  (* a->#1;_A->#2;_B->#3;f->#4;min->#5;max ->#6;cont->#7 *)
	  let body =
	    if Uint31.lt min max then 
	      begin
		let maxp1 = Uint31.sub max (Uint31.of_int 1) in
		mkApp (mkRel 4(*f*),
		       [|mkRel 6 (* max *);
			 mkApp (it,
				[|mkRel 2 (* _A *);
				  mkRel 3 (* _B *);
				  mkRel 4 (* f *);
				  mkInt maxp1; (* max + 1 *)
				  mkRel 5 (* min *);
				  mkRel 7 (* cont *)
				|]);
			 mkRel 1 (* a*)
		       |])
	      end
	    else 
	      if Uint31.eq min max then 
		mkApp(mkRel 4(*f *),
		      [| mkRel 5; (* min *)
			 mkRel 7; (* cont *)
			 mkRel 1  (* a *)
		       |])
	      else 
		mkApp(mkRel 7,[|mkRel 1|])
	  in
	  E.mkClos name typ body subst



    let red_op env op f args =
      try 
	let r =
	  match op with
	  | Ocaml_prim op -> red_caml_prim env op args
	  | Oiterator op -> red_iterator env op f args
	  | Oprim op -> red_prim env op args
	in Some r
      with _ -> None
  	  
  end
