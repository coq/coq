
(* $Id$ *)

open Util
open Names
(*i open Generic i*)
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
    | IsMeta n ->
	error "execute: found a non-instanciated goal"

    | IsEvar _ ->
	let ty = type_of_existential env sigma cstr in
	let jty = execute mf env sigma ty in
	let jty = assumption_of_judgment env sigma jty in
	{ uj_val = cstr; uj_type = jty }
	
    | IsRel n -> 
	relative env sigma n

    | IsVar id -> 
      (try
         make_judge cstr (snd (lookup_var id env))
       with Not_found ->
         error ("execute: variable " ^ (string_of_id id) ^ " not defined"))
	  
    | IsAbst _ ->
        if evaluable_abst env cstr then 
	  execute mf env sigma (abst_value env cstr)
        else 
	  error "Cannot typecheck an unevaluable abstraction"
	      
    | IsConst c ->
        make_judge cstr (type_of_constant env sigma c)
	  
    | IsMutInd ind ->
	make_judge cstr (type_of_inductive env sigma ind)
	  
    | IsMutConstruct cstruct -> 
	make_judge cstr (type_of_constructor env sigma cstruct)
	  
    | IsMutCase (ci,p,c,lf) ->
        let cj = execute mf env sigma c in
        let pj = execute mf env sigma p in
        let lfj = execute_array mf env sigma lf in
        type_of_case env sigma ci pj cj lfj
  
    | IsFix ((vn,i as vni),(lar,lfi,vdef)) ->
        if (not mf.fix) && array_exists (fun n -> n < 0) vn then
          error "General Fixpoints not allowed";
        let larjv,vdefv = execute_fix mf env sigma lar lfi vdef in
 	let larv = Array.map body_of_type larjv in
	let fix = vni,(larv,lfi,vdefv) in
        check_fix env sigma fix;
	make_judge (mkFix fix) larjv.(i)
	  
    | IsCoFix (i,(lar,lfi,vdef)) ->
        let (larjv,vdefv) = execute_fix mf env sigma lar lfi vdef in
	let larv = Array.map body_of_type larjv in
        let cofix = i,(larv,lfi,vdefv) in
        check_cofix env sigma cofix;
	make_judge (mkCoFix cofix) larjv.(i)
	  
    | IsSort (Prop c) -> 
	judge_of_prop_contents c

    | IsSort (Type u) ->
	let (j,_) = judge_of_type u in j
	  
    | IsAppL (f,args) ->
	let j = execute mf env sigma f in
        let jl = execute_list mf env sigma args in
	let (j,_) = apply_rel_list env sigma mf.nocheck jl j in
	j
	    
    | IsLambda (name,c1,c2) -> 
        let j = execute mf env sigma c1 in
	let var = assumption_of_judgment env sigma j in
	let env1 = push_rel_decl (name,var) env in
        let j' = execute mf env1 sigma c2 in 
        let (j,_) = abs_rel env1 sigma name var j' in
	j
	  
    | IsProd (name,c1,c2) ->
        let j = execute mf env sigma c1 in
        let varj = type_judgment env sigma j in
	let var = assumption_of_type_judgment varj in
	let env1 = push_rel_decl (name,var) env in
        let j' = execute mf env1 sigma c2 in
	let (j,_) = gen_rel env1 sigma name varj j' in
	j

     | IsLetIn (name,c1,c2,c3) ->
        let j1 = execute mf env sigma c1 in
        let j2 = execute mf env sigma c2 in
	let { uj_val = b; uj_type = t } = cast_rel env sigma j1 j2 in
        let j3 = execute mf (push_rel_def (name,b,t) env) sigma c3 in
	{ uj_val = mkLetIn (name, j1.uj_val, j2.uj_val, j3.uj_val) ;
	  uj_type = typed_app (subst1 j1.uj_val) j3.uj_type }
  
    | IsCast (c,t) ->
        let cj = execute mf env sigma c in
        let tj = execute mf env sigma t in
        cast_rel env sigma cj tj
	  
    | IsXtra _ -> anomaly "Typing: found an Extra"
	  
and execute_fix mf env sigma lar lfi vdef =
  let larj = execute_array mf env sigma lar in
  let lara = Array.map (assumption_of_judgment env sigma) larj in
  let nlara = 
    List.combine (List.rev lfi) (Array.to_list (vect_lift_type lara)) in
  let env1 = 
    List.fold_left (fun env nvar -> push_rel_decl nvar env) env nlara in
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

let unsafe_machine env sigma constr =
  let mf = { fix = false; nocheck = true } in
  execute mf env sigma constr

(* Type of a constr *)

let type_of env sigma c = 
  let j = safe_machine env sigma c in 
  nf_betaiota env sigma (body_of_type j.uj_type)

(* The typed type of a judgment. *)

let execute_type env sigma constr = 
  let j = execute { fix=false; nocheck=true } env sigma constr in
  assumption_of_judgment env sigma j

let execute_rec_type env sigma constr = 
  let j = execute { fix=false; nocheck=false } env sigma constr in
  assumption_of_judgment env sigma j

