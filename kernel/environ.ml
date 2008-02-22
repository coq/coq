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
  let ctxt = array_map2_i (fun i na t -> (na, None, lift i t)) lna typarray in
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

let lookup_modtype ln env = 
  MPmap.find ln env.env_globals.env_modtypes


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
  let ctxt,vals,rmv = 
    List.fold_right2 (fun (id,_,_ as d) (id',v) (ctxt,vals,rmv) ->
      if List.mem id ids then 
	(ctxt,vals,id::rmv)
      else 	  
	let nd = check_context d in
	let nv = check_value v in
	  (nd::ctxt,(id',nv)::vals,rmv))
		     ctxt vals ([],[],[])
  in ((ctxt,vals),rmv)






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
	(match retroknowledge find env field with 
	   | Ind i31t -> let i31c = Construct (i31t, 1) in
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
      if (land) i ((lsl) 1 n) = 0 then
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
    add_vm_constant_dynamic_info rk c Cbytegen.dynamic_int31_compilation
  in

  (* subfunction which adds the compiling information of an
     int31 operation which has a specific vm instruction (associates
     it to the name of the coq definition in the reactive retroknowledge) *)
  let add_int31_op retroknowledge v n op kn =
    add_vm_compiling_info retroknowledge v (Cbytegen.op_compilation n op kn)
  in

fun env field value ->
  (* subfunction which shortens the (very often use) registration of binary
     operators to the reactive retroknowledge. *)
  let add_int31_binop_from_const op =
    match value with
      | Const kn ->  retroknowledge add_int31_op env value 2 
	                               op kn
      | _ -> anomaly "Environ.register: should be a constant"
  in
  let add_int31_unop_from_const op =
    match value with
      | Const kn ->  retroknowledge add_int31_op env value 1
	                               op kn
      | _ -> anomaly "Environ.register: should be a constant"
  in
  (* subfunction which completes the function constr_of_int31 above
     by performing the actual retroknowledge operations *)
  let add_int31_decompilation_from_type rk = 
    (* invariant : the type of bits is registered, otherwise the function 
       would raise Not_found. The invariant is enforced in safe_typing.ml *)
    match field with
      | KInt31 (grp, Int31Type) -> 
	  (match Retroknowledge.find rk (KInt31 (grp,Int31Bits)) with
	    | Ind i31bit_type ->  
		(match value with 
		  | Ind i31t -> 
		      Retroknowledge.add_vm_decompile_constant_info rk
		               value (constr_of_int31 i31t i31bit_type)
		  | _ -> anomaly "Environ.register: should be an inductive type")
	    | _ -> anomaly "Environ.register: Int31Bits should be an inductive type")
      | _ -> anomaly "Environ.register: add_int31_decompilation_from_type called with an abnormal field"
  in
  {env with retroknowledge = 
  let retroknowledge_with_reactive_info = 
  match field with
    | KInt31 (_, Int31Type) -> 
        let i31c = match value with
                     | Ind i31t -> (Construct (i31t, 1))
		     | _ -> anomaly "Environ.register: should be an inductive type"
	in
	add_int31_decompilation_from_type 
	  (add_vm_before_match_info 
	     (retroknowledge add_int31c env i31c) 
	     value Cbytegen.int31_escape_before_match)
    | KInt31 (_, Int31Plus) -> add_int31_binop_from_const Cbytecodes.Kaddint31
    | KInt31 (_, Int31PlusC) -> add_int31_binop_from_const Cbytecodes.Kaddcint31
    | KInt31 (_, Int31PlusCarryC) -> add_int31_binop_from_const Cbytecodes.Kaddcarrycint31
    | KInt31 (_, Int31Minus) -> add_int31_binop_from_const Cbytecodes.Ksubint31
    | KInt31 (_, Int31MinusC) -> add_int31_binop_from_const Cbytecodes.Ksubcint31
    | KInt31 (_, Int31MinusCarryC) -> add_int31_binop_from_const 
	                                           Cbytecodes.Ksubcarrycint31
    | KInt31 (_, Int31Times) -> add_int31_binop_from_const Cbytecodes.Kmulint31
    | KInt31 (_, Int31TimesC) -> add_int31_binop_from_const Cbytecodes.Kmulcint31
    | KInt31 (_, Int31Div21) -> (* this is a ternary operation *)
                                (match value with
				 | Const kn ->
				     retroknowledge add_int31_op env value 3 
	                               Cbytecodes.Kdiv21int31 kn
				 | _ -> anomaly "Environ.register: should be a constant")
    | KInt31 (_, Int31Div) -> add_int31_binop_from_const Cbytecodes.Kdivint31
    | KInt31 (_, Int31AddMulDiv) -> (* this is a ternary operation *)
                                (match value with
				 | Const kn ->
				     retroknowledge add_int31_op env value 3 
	                               Cbytecodes.Kaddmuldivint31 kn
				 | _ -> anomaly "Environ.register: should be a constant")
    | KInt31 (_, Int31Compare) -> add_int31_binop_from_const Cbytecodes.Kcompareint31
    | KInt31 (_, Int31Head0) -> add_int31_unop_from_const Cbytecodes.Khead0int31
    | KInt31 (_, Int31Tail0) -> add_int31_unop_from_const Cbytecodes.Ktail0int31 
    | _ -> env.retroknowledge 
  in
  Retroknowledge.add_field retroknowledge_with_reactive_info field value
  }


(**************************************************************)
(* spiwack: the following definitions are used by the function 
   [assumptions] which gives as an output the set of all
   axioms and sections variables on which a given term depends
   in a context (expectingly the Global context) *)

type assumption =
  | Variable of identifier*constr (* A section variable and its type *)
  | Axiom of constant*constr      (* An axiom and its type*)


(* Defines a set of [assumption] *)
module OrderedAssumption = 
struct 
  type t = assumption
  let compare = compare
end

module AssumptionSet = Set.Make (OrderedAssumption)

(* infix definition of set-union for redability purposes *)
let ( ** ) s1 s2  = AssumptionSet.union s1 s2

let rec assumptions t env =   
 (* Goes recursively into the terms to see if it depends on assumptions
    the 3 important cases are : - Const _ where we need to first unfold
    the constant and return the needed assumptions of its body in the 
    environment,
                                - Rel _ which means the term is a variable
    which has been bound earlier by a Lambda or a Prod (returns [] ),
                                - Var _ which means that the term refers
    to a section variable or a "Let" definition, in the former it is
    an assumption of [t], in the latter is must be unfolded like a Const.
    The other cases are straightforward recursion.*)
  match kind_of_term t with
    | Var id -> (* a Var can be either a variable, or a "Let" definition.*)
                (match named_body id env with
                | None ->
                      AssumptionSet.singleton (Variable (id,named_type id env))
		| Some bdy -> assumptions bdy env)
    | Meta _ | Evar _ -> Util.anomaly "Environ.assumption: does not expect a meta or an evar"
    | Cast (e1,_,e2) | Prod (_,e1,e2) | Lambda (_,e1,e2) -> 
                   (assumptions e1 env)**(assumptions e2 env)
    | LetIn (_,e1,e2,e3) ->(assumptions e1 env)**
                           (assumptions e2 env)**
                           (assumptions e3 env)
    | App (e1, e_array) -> (assumptions e1 env)**
                   (Array.fold_right (fun e s -> (assumptions e env)**s)
                                      e_array AssumptionSet.empty)
    | Case (_,e1,e2,e_array) -> (assumptions e1 env)**
                                (assumptions e2 env)**
                   (Array.fold_right (fun e s -> (assumptions e env)**s)
                                      e_array AssumptionSet.empty)
    | Fix (_,(_, e1_array, e2_array)) | CoFix (_,(_,e1_array, e2_array)) ->
                   Array.fold_right (fun e s -> (assumptions e env)**s)
                                      e1_array
                   (Array.fold_right (fun e s -> (assumptions e env)**s)
                                      e2_array AssumptionSet.empty)
    | Const kn -> 
	let cb = lookup_constant kn env in
        (match cb.Declarations.const_body with
        | None -> 
	    let ctype = 
	      match cb.Declarations.const_type with
		| PolymorphicArity (ctx,a) -> mkArity (ctx, Type a.poly_level)
		| NonPolymorphicType t -> t
	    in
	    AssumptionSet.singleton (Axiom (kn,ctype))
        | Some body -> assumptions (Declarations.force body) env)
    | _ -> AssumptionSet.empty (* closed atomic types + rel *)

(* /spiwack *)



