
(* $Id$ *)

open Util
open Names
open Generic
open Term
open Environ
open Reduction
open Type_errors
open Typeops

let vect_lift = Array.mapi lift
let vect_lift_type = Array.mapi (fun i t -> typed_app (lift i) t)

type 'a mach_flags = {
  fix : bool;
  nocheck : bool }

(* The typing machine without information, without universes but with
   existential variables. *)

let rec execute mf env sigma cstr =
  match kind_of_term cstr with
    | IsMeta _ ->
	anomaly "the kernel does not understand metas"
    | IsEvar _ ->
	anomaly "the kernel does not understand existential variables"
	
    | IsRel n -> 
	relative env n

    | IsVar id -> 
	make_judge cstr (snd (lookup_var id env))
	  
    | IsAbst _ ->
        if evaluable_abst env cstr then 
	  execute mf env sigma (abst_value env cstr)
        else 
	  error "Cannot typecheck an unevaluable abstraction"
	      
    | IsConst _ ->
        make_judge cstr (type_of_constant env sigma cstr)
	  
    | IsMutInd _ ->
	make_judge cstr (type_of_inductive env sigma cstr)
	  
    | IsMutConstruct _ -> 
	let (typ,kind) = destCast (type_of_constructor env sigma cstr) in
        { uj_val = cstr; uj_type = typ; uj_kind = kind }
	  
    | IsMutCase (_,p,c,lf) ->
        let cj = execute mf env sigma c in
        let pj = execute mf env sigma p in
        let lfj = execute_array mf env sigma lf in
        type_of_case env sigma pj cj lfj
  
    | IsFix (vn,i,lar,lfi,vdef) ->
        if (not mf.fix) && array_exists (fun n -> n < 0) vn then
          error "General Fixpoints not allowed";
        let larv,vdefv = execute_fix mf env sigma lar lfi vdef in
        let fix = mkFix vn i larv lfi vdefv in
        check_fix env sigma Spset.empty fix;
	make_judge fix larv.(i)
	  
    | IsCoFix (i,lar,lfi,vdef) ->
        let (larv,vdefv) = execute_fix mf env sigma lar lfi vdef in
        let cofix = mkCoFix i larv lfi vdefv in
        check_cofix env sigma Spset.empty cofix;
	make_judge cofix larv.(i)
	  
    | IsSort (Prop c) -> 
	type_of_prop_or_set c

    | IsSort (Type u) ->
	let (j,_) = type_of_type u in j
	  
    | IsAppL a ->
	let la = Array.length a in
	if la = 0 then error_cant_execute CCI env cstr;
	let hd = a.(0)
	and tl = Array.to_list (Array.sub a 1 (la - 1)) in
	let j = execute mf env sigma hd in
        let jl = execute_list mf env sigma tl in
	let (j,_) = apply_rel_list env sigma mf.nocheck jl j in
	j
	    
    | IsLambda (name,c1,c2) -> 
        let j = execute mf env sigma c1 in
        let var = assumption_of_judgment env sigma j in
	let env1 = push_rel (name,var) env in
        let j' = execute mf env1 sigma c2 in 
        let (j,_) = abs_rel env1 sigma name var j' in
	j
	  
    | IsProd (name,c1,c2) ->
        let j = execute mf env sigma c1 in
        let var = assumption_of_judgment env sigma j in
	let env1 = push_rel (name,var) env in
        let j' = execute mf env1 sigma c2 in
	let (j,_) = gen_rel env1 sigma name var j' in
	j
	  
    | IsCast (c,t) ->
        let cj = execute mf env sigma c in
        let tj = execute mf env sigma t in
        cast_rel env sigma cj tj
	  
      | _ -> error_cant_execute CCI env cstr
	  
and execute_fix mf env sigma lar lfi vdef =
  let larj = execute_array mf env sigma lar in
  let lara = Array.map (assumption_of_judgment env sigma) larj in
  let nlara = 
    List.combine (List.rev lfi) (Array.to_list (vect_lift_type lara)) in
  let env1 = 
    List.fold_left (fun env nvar -> push_rel nvar env) env nlara in
  let vdefj = execute_array mf env1 sigma vdef in
  let vdefv = Array.map j_val_only vdefj in
  let cst3 = type_fixpoint env1 sigma lfi lara vdefj in
  (lara,vdefv)

and execute_array mf env sigma v =
  let jl = execute_list mf env sigma (Array.to_list v) in
  Array.of_list jl

and execute_list mf env sigma = function
  | [] -> 
      []
  | c::r -> 
      let j = execute mf env sigma c in 
      let jr = execute_list mf env sigma r in
      j::jr


let safe_machine env sigma constr = 
  let mf = { fix = false; nocheck = false } in
  execute mf env sigma constr


(* Type of a constr *)

let type_of env sigma c = 
  let j = safe_machine env sigma c in 
  nf_betaiota env sigma j.uj_type

(* The typed type of a judgment. *)

let execute_type env sigma constr = 
  let j = safe_machine env sigma constr in
  assumption_of_judgment env sigma j
