
(* $Id$ *)

open Pp
open Util
open Names
open Univ
open Generic
open Term
open Himsg
open Reduction
open Sign
open Environ
open Machops

(* Fonctions temporaires pour relier la forme castée de la forme jugement *)

let tjudge_of_cast env = function
  | DOP2 (Cast, b, t) ->
      (match whd_betadeltaiota env t with
	 | DOP0 (Sort s) -> {body=b; typ=s}
	 | DOP2 (Cast, b',t') -> anomaly "Supercast (tjudge_of_cast) [Mach]"
	 | _ -> anomaly "Not a type (tjudge_of_cast) [Mach]")
  | _ -> anomaly "Not casted (tjudge_of_cast)"
	
let tjudge_of_judge env j =
  { body = j.uj_val;
    typ = match whd_betadeltaiota env j.uj_type with
      (* Nécessaire pour ZFC *)
      | DOP0 (Sort s) -> s
      | DOP0 Implicit -> anomaly "Tiens, un implicit"
      | _ -> anomaly "Not a type (tjudge_ofjudge)" }

let vect_lift = Array.mapi lift
let vect_lift_type = Array.mapi (fun i t -> typed_app (lift i) t)

(*s The machine flags. 
   [fix] indicates if we authorize general fixpoints ($\mathit{recarg} < 0$)
   like [Acc_rec.fw].
   [nocheck] indicates if we can skip some verifications to accelerate
   the type inference. *)

type 'a mach_flags = {
  fix : bool;
  nocheck : bool }

(* The typing machine without information. *)

let rec execute mf env cstr =
  let u0 = universes env in
  match kind_of_term cstr with
    | IsMeta n ->
       	let metaty =
          try lookup_meta n env
          with Not_found -> error "A variable remains non instanciated" 
	in
        (match kind_of_term metaty with
           | IsCast (typ,kind) -> 
	       ({ uj_val = cstr; uj_type = typ; uj_kind = kind}, u0)
           | _ ->
	       let (jty,u1) = execute mf env metaty in
	       let k = hnf_constr env jty.uj_type in
	       ({ uj_val = cstr; uj_type = metaty; uj_kind = k }, u1))
	
    | IsRel n -> 
	(relative env n, u0)

    | IsVar id -> 
	(make_judge cstr (snd (lookup_var id env)), u0)
	  
    | IsAbst _ ->
        if evaluable_abst env cstr then 
	  execute mf env (abst_value env cstr)
        else 
	  error "Cannot typecheck an unevaluable abstraction"
	      
    | IsConst _ ->
        (make_judge cstr (type_of_constant_or_existential env cstr), u0)
	  
    | IsMutInd _ ->
	(make_judge cstr (type_of_inductive env cstr), u0)
	  
    | IsMutConstruct _ -> 
	let (typ,kind) = destCast (type_of_constructor env cstr) in
        ({ uj_val = cstr; uj_type = typ; uj_kind = kind } , u0)
	  
    | IsMutCase (_,p,c,lf) ->
        let (cj,u1) = execute mf env c in
	let env1 = set_universes u1 env in
        let (pj,u2) = execute mf env1 p in
	let env2 = set_universes u2 env1 in
        let (lfj,u3) = execute_array mf env2 lf in
	let env3 = set_universes u3 env2 in
        (type_of_case env3 pj cj lfj, u3)
  
    | IsFix (vn,i,lar,lfi,vdef) ->
        if (not mf.fix) && array_exists (fun n -> n < 0) vn then
          error "General Fixpoints not allowed";
        let (larv,vdefv,u1) = execute_fix mf env lar lfi vdef in
        let fix = mkFix vn i larv lfi vdefv in
        check_fix env fix;
	(make_judge fix larv.(i), u1)
	  
    | IsCoFix (i,lar,lfi,vdef) ->
        let (larv,vdefv,u1) = execute_fix mf env lar lfi vdef in
        let cofix = mkCoFix i larv lfi vdefv in
        check_cofix env cofix;
	(make_judge cofix larv.(i), u1)
	  
    | IsSort (Prop c) -> 
	(type_of_prop_or_set c, u0)

    | IsSort (Type u) ->
	type_of_type u u0
	  
    | IsAppL a ->
	let la = Array.length a in
	if la = 0 then error_cant_execute CCI env cstr;
	let hd = a.(0)
	and tl = Array.to_list (Array.sub a 1 (la - 1)) in
	let (j,u1) = execute mf env hd in
	let env1 = set_universes u1 env in
        let (jl,u2) = execute_list mf env1 tl in
	let env2 = set_universes u2 env1 in
	apply_rel_list env2 mf.nocheck jl j
	    
    | IsLambda (name,c1,c2) -> 
        let (j,u1) = execute mf env c1 in
        let var = assumption_of_judgement env j in
	let env1 = push_rel (name,var) (set_universes u1 env) in
        let (j',u2) = execute mf env1 c2 in 
	let env2 = set_universes u2 env1 in
        abs_rel env2 name var j'
	  
    | IsProd (name,c1,c2) ->
        let (j,u1) = execute mf env c1 in
        let var = assumption_of_judgement env j in
	let env1 = push_rel (name,var) (set_universes u1 env) in
        let (j',u2) = execute mf env1 c2 in
	let env2 = set_universes u2 env1 in
        gen_rel env2 name var j'
	  
    | IsCast (c,t) ->
        let (cj,u1) = execute mf env c in
	let env1 = set_universes u1 env in
        let (tj,u2) = execute mf env1 t in
	let env2 = set_universes u2 env1 in
        (cast_rel env2 cj tj, u2)
	  
      | _ -> error_cant_execute CCI env cstr
	  
and execute_fix mf env lar lfi vdef =
  let (larj,u1) = execute_array mf env lar in
  let env1 = set_universes u1 env in
  let lara = Array.map (assumption_of_judgement env1) larj in
  let nlara = 
    List.combine (List.rev lfi) (Array.to_list (vect_lift_type lara)) in
  let env2 = 
    List.fold_left (fun env nvar -> push_rel nvar env) env1 nlara in
  let (vdefj,u2) = execute_array mf env2 vdef in
  let env3 = set_universes u2 env2 in
  let vdefv = Array.map j_val_only vdefj in
  let u3 = type_fixpoint env3 lfi lara vdefj in
  (lara,vdefv,u3)

and execute_array mf env v =
  let (jl,u1) = execute_list mf env (Array.to_list v) in
  (Array.of_list jl, u1)

and execute_list mf env = function
  | [] -> ([], universes env)
  | c::r -> 
      let (j,u') = execute mf env c in 
      let (jr,u'') = execute_list mf (set_universes u' env) r in
      (j::jr, u'')


(* The typed type of a judgment. *)

let execute_type mf env constr = 
  let (j,_) = execute mf env constr in
  typed_type_of_judgment env j


(* Exported machines.  First safe machines, with no general fixpoint
   allowed (the flag [fix] is not set) and all verifications done (the
   flag [nocheck] is not set). *)

let safe_machine env constr = 
  let mf = { fix = false; nocheck = false } in
  execute mf env constr

let safe_machine_type env constr = 
  let mf = { fix = false; nocheck = false } in
  execute_type mf env constr

(* Machines with general fixpoint. *)

let fix_machine env constr = 
  let mf = { fix = true; nocheck = false } in
  execute mf env constr

let fix_machine_type env constr = 
  let mf = { fix = true; nocheck = false } in
  execute_type mf env constr

(* Fast machines without any verification. *)

let unsafe_machine env constr = 
  let mf = { fix = true; nocheck = true } in
  execute mf env constr

let unsafe_machine_type env constr = 
  let mf = { fix = true; nocheck = true } in
  execute_type mf env constr


(* ``Type of'' machines. *)

let type_of env c = 
  let (j,_) = safe_machine env c in nf_betaiota env j.uj_type

let type_of_type env c = 
  let tt = safe_machine_type env c in DOP0 (Sort tt.typ)

let unsafe_type_of env c = 
  let (j,_) = unsafe_machine env c in nf_betaiota env j.uj_type

let unsafe_type_of_type env c = 
  let tt = unsafe_machine_type env c in DOP0 (Sort tt.typ)


(*s Machines with information. *)

(*i
let implicit_judgment = {body=mkImplicit;typ=implicit_sort}

let add_inf_rel (na,inf) env =
  match inf with
      Logic -> add_rel (na,implicit_judgment) env
    | Inf j -> add_rel (na,tjudge_of_judge j) env


let fw_mutind sigma fenv k =
  let (sp,x,args) = destMutInd k in
  let mis = mind_specif_of_mind k in
    match mis_singl mis with 
	Some a -> Some (a,true)
      | None ->
	  if is_info_cast_type sigma (mis_arity mis) then
	    let infK =
              global_reference fenv (fwsp_of sp) (id_of_global (MutInd (sp,x)))
	    in Some (infK,false)
	  else None

let inf_of_mind sigma fenv mind = 
  try
    match fw_mutind sigma fenv mind with
        Some (infK,singl) -> Inf(cast_fmachine (sigma,[]) fenv infK)
      | None -> Logic
  with
      Not_found | Failure _ -> 
	anomaly "cannot convert an inductive to an finductive"

let inf_mconstructor (sigma,metamap) fenv k = 
  let (sp,x,i,cl) = destMutConstruct k in
  let mind = mkMutInd sp x cl in 
    (match fw_mutind sigma fenv mind with
         None -> Logic
       | Some(infi,singl) ->
	   (match mind_lamexp mind with
	      | Some clamexp ->
		  if singl
		  then Inf(cast_fmachine (sigma,[]) fenv clamexp)
		  else
		    let (infsp, infx, infcl) = destMutInd infi in
		    let infmconstructor = mkMutConstruct infsp infx i infcl in
		    let infval = subst1 infmconstructor clamexp in
		      Inf (cast_fmachine (sigma,fst metamap) fenv infval)
	      | _ -> assert false))


exception DefinedExtraction

(* when c is an evaluable constant with an extraction which 
   contains an implicit, gives the value of the c constant
   otherwise raise DefinedExtraction
*)

let value_implicit_const sigma c cinf = 
  match c with DOPN(Const(_),_) -> 
    if evaluable_const sigma c then 
      let cv = const_value sigma cinf in 
	if is_implicit cv (* or contains_implicit sigma cv *)
	then const_value sigma c 
	else raise DefinedExtraction
    else raise DefinedExtraction
    | _ -> raise DefinedExtraction

let unsafe_infmachine (sigma,metamap) env fenv c = 
  let rec infexec env fenv cstr = match cstr with
       DOP2(Cast,c,DOP0(Sort(Prop(Null)))) -> Logic
    |  DOP2(Cast,c,DOP2(Cast,_,DOP0(Sort(Prop(Null))))) -> Logic
    |  DOP2(Cast,c,_) -> infexec env fenv c
    |  DOP0(Meta n) ->
         (match List.assoc n (snd metamap) with
             Logic -> Logic
           | Inf j -> Inf{uj_val=DOP0(Meta n);
                          uj_type=j.uj_val;
                          uj_kind = hnf_constr sigma j.uj_type})

    | Rel n ->
        inf_rel fenv
          (contents_of_type sigma (snd (lookup_rel n env))) n

    | VAR str ->
        inf_var fenv
          (contents_of_type sigma (snd(lookup_glob str env))) str

    | DOPN(Const _,_) -> inf_of_const sigma (env,fenv) cstr

    | DOPN(Abst _,_) ->
        if evaluable_abst cstr then infexec env fenv (abst_value cstr)
        else error "cannot extract from an unevaluable abstraction"

    | DOP0(Sort s) -> inf_sort s

    | DOPN(AppL,tl) ->
        let c1 =  (hd_vect tl)
        and cl = tl_vect tl in
          let funinf = infexec env fenv c1 in
            (match funinf with Logic -> Logic
	      | Inf(j) -> let cinf = j.uj_val in
             (* try to expand constants corresponding 
		    to non extractable terms *)
	      (try if is_extraction_expanded() then 
		 let valcte = value_implicit_const sigma c1 cinf 
		 in infexec env fenv (whd_betaiota (appvect(valcte,cl))) 
	       else raise DefinedExtraction
               with DefinedExtraction -> 
		 let argsinf = Array.map (infexec env fenv) cl
		 in it_vect inf_apply funinf argsinf))

    | DOP2(Lambda,c1,DLAM(name,c2)) ->
        let varinf = infexec env fenv c1 in
        let bodyinf = infexec (add_rel (name,tjudge_of_cast sigma c1) env)
                        (add_inf_rel (name,varinf) fenv) c2
        in inf_abs_rel name bodyinf varinf

    | DOP2(Prod,c1,DLAM(name,c2)) ->
        let c1inf = infexec env fenv c1 in
        let c2inf = infexec (add_rel (name,tjudge_of_cast sigma c1) env)
                      (add_inf_rel (name,c1inf) fenv) c2
        in inf_gen_rel name c2inf c1inf

    | DOPN(MutInd _,_) -> inf_of_mind sigma fenv cstr

    | DOPN(MutConstruct _,_) ->
        inf_mconstructor (sigma,metamap) fenv cstr

    | DOPN(Fix(vn,i),cl) ->
        let lar = Array.sub cl 0 ((Array.length cl) - 1) in
        let inflar = Array.map (infexec env fenv) lar in
        let infAi = inflar.(i) in 
          (match infAi with 
              Logic   -> Logic 
            | Inf aij ->
                let (lfi,ldefs) = decomp_all_DLAMV_name (last_vect cl) in
                let (new_env,new_fenv) =
                  it_vect2
                    (fun (ne,nfe) fk ak -> 
                       (add_rel (fk,tjudge_of_cast sigma ak) ne,
                        let infAk = infexec ne nfe ak
                        in (add_inf_rel (fk,infAk) nfe)))
                    (env,fenv)
                    (Array.of_list (List.rev lfi)) (vect_lift lar) in 
(* a special function to localize the recursive index in the extracted term *)
                let rec exec_def ne nfe n def = 
                  (match hnf_constr sigma def with 
                      DOP2(Lambda,c1,DLAM(name,c2)) ->
                        let varinf = infexec ne nfe c1 in
                        let ne' = (add_rel (name,tjudge_of_cast sigma c1) ne) 
                        and nfe' = add_inf_rel (name,varinf) nfe in
                          if n = 0 then
                            let infc2 = infexec ne' nfe' c2 
                            in let infdef = inf_abs_rel name infc2 varinf
                               and index =
                                 if varinf = Logic then -1
                        (* the recursive call was on a non-informative term *) 
                                 else 0 in (infdef,index)
                          else
                            let bodyinf,countl = 
                              exec_def (add_rel (name,tjudge_of_cast sigma c1) ne) 
                                (add_inf_rel (name,varinf) nfe) (n-1) c2 in
                            let (infabs,abs) =
                              inf_abs_rel_count name bodyinf varinf
                            in (infabs,
                                if abs = ERASE then countl
                                else if countl<0 then countl-1
                                else countl+1)
                    | _ -> anomaly "exec_def : should be a lambda") in
                let infdefs_ind =
                  map2_vect (exec_def new_env new_fenv) vn ldefs
                in inf_fix sigma i aij.uj_type lfi inflar infdefs_ind)

    | DOPN(CoFix i,cl) ->
        let lar    = Array.sub cl 0 ((Array.length cl) - 1) in 
        let inflar = Array.map (infexec env fenv) lar in
        let infAi  = inflar.(i) in
          (match infAi with 
              Logic   -> Logic 
            | Inf aij -> 
                let lfi,ldefs = decomp_all_DLAMV_name (last_vect cl) in 
                let (new_env,new_fenv) = 
                  it_vect2 (fun (ne,nfe) fk ak -> 
                              (add_rel (fk,tjudge_of_cast sigma ak) ne, 
                               let infAk = infexec ne nfe ak
                               in (add_inf_rel (fk,infAk) nfe)))
                    (env,fenv) 
                    (Array.of_list (List.rev lfi)) (vect_lift lar) in 
                                   
                let infdefs = Array.map (infexec new_env new_fenv) ldefs 
                in  inf_cofix sigma i aij.uj_type lfi inflar infdefs)

    | DOPN(MutCase _,_) ->
        let (ci,p,c,lf) = destCase cstr in
        let pinf = infexec env fenv p in 
          (match pinf with
              Logic  -> Logic 
            | Inf pj -> 
		if is_extraction_expanded() then 
		  let (d,l) = whd_betadeltaiota_stack sigma c [] in 
                 (match d with (DOPN(MutConstruct(_,_),_)) ->
		    let cstr' = 
		      DOPN(MutCase(ci),Array.append [|p;applist(d,l)|] lf)
		    in infexec env fenv (whd_betaiota cstr')
		    | _ -> 
                  let cinf = infexec env fenv c
                  and lfinf = Array.map (infexec env fenv) lf
                  in inf_mutcase fenv sigma pj ci cinf lfinf
		 )
               else let cinf = infexec env fenv c
                  and lfinf = Array.map (infexec env fenv) lf
                  in inf_mutcase fenv sigma pj ci cinf lfinf)
	 
    | _ -> error "Cannot extract information"
  in infexec env fenv c


let core_infmachine meta env fenv c =
  try unsafe_infmachine meta env fenv c
  with (UserError _ | Failure _) -> Logic

(* WITH INFORMATION *)
(* does not check anymore that extracted terms are well-formed *)
let judgement_infmachine meta env fenv c ct = 
  try
    match unsafe_infmachine meta env fenv c with
        Inf infj ->
          let inftyp =
            try unsafe_infmachine meta env fenv ct
            with (UserError _ | Failure _) ->
              (warning "Failed to extract in type"; Logic)
          in (match inftyp with
                  Inf infjt ->
                    Inf{uj_val=infj.uj_val;
                        uj_type=infjt.uj_val;
                        uj_kind=infj.uj_kind}
                | Logic -> Inf infj)
      | Logic -> Logic
  with (UserError _ | Failure _) -> (warning "Failed to extract"; Logic)

let infmachine_type nocheck (sigma,metamap) env fenv constr =
  let constr_metamap = List.map (fun (id,(c,_)) -> (id,c)) metamap in
  let inf_metamap = List.map (fun (id,(_,i)) -> (id,i)) metamap in
  let t = core_fmachine_type nocheck (sigma,constr_metamap) env constr in
  let inf = 
    if is_info_type sigma t then (* Case the term is informative *)
      let uniarc = get_uniarc () in
      let infjt =
        judgement_infmachine
          (sigma,(constr_metamap,inf_metamap)) env fenv 
	  t.body 
	  (DOP0 (Sort t.typ)) in
      let _ = set_uniarc uniarc in
        infjt
    else Logic

  in hash_jpair_type
       ({body = strip_all_casts t.body; typ = t.typ},
        (inf_app (fun j -> {uj_val = nf_beta j.uj_val;
                            uj_type = nf_beta j.uj_type;
                            uj_kind = j.uj_kind }) inf))

let infmachine nocheck (sigma,metamap) env fenv constr =
  let constr_metamap = List.map (fun (id,(c,_)) -> (id,c)) metamap in
  let inf_metamap = List.map (fun (id,(_,i)) -> (id,i)) metamap in
  let j = core_fmachine nocheck (sigma,constr_metamap) env constr in
  let inf = 
    if is_info_judge sigma j then (* Case the term is informative *)
      let uniarc = get_uniarc () in
      let jt = cast_fmachine (sigma,constr_metamap) env j.uj_type in
      let infjt =
        judgement_infmachine
          (sigma,(constr_metamap,inf_metamap)) env fenv j.uj_val jt.uj_val in
      let _ = set_uniarc uniarc in
        infjt
    else Logic

  in hash_jpair
       ({uj_val = strip_all_casts j.uj_val;
         uj_type = strip_all_casts j.uj_type;
         uj_kind = j.uj_kind},
        (inf_app (fun j -> {uj_val = nf_beta j.uj_val;
                            uj_type = nf_beta j.uj_type;
                            uj_kind = j.uj_kind }) inf))


let jsign_of_sign sigma sign =
  sign_it
    (fun id a (sign,fsign) ->
      let sign' = add_sign (id,a) sign in
      let fsign' =
        match infmachine_type true (sigma,[]) (gLOB sign) (gLOB fsign) a.body
 	with
          (_,Logic) -> fsign
        | (_,Inf ft) -> add_sign (id,tjudge_of_judge ft) fsign
      in (sign',fsign'))
    sign (([],[]),([],[]))


let fsign_of_sign sigma sign = snd (jsign_of_sign sigma sign)

let infexemeta_type sigma metamap (env,fenv) c =
  infmachine_type true (sigma,metamap) env fenv c

let infexecute_rec_type sigma (env,fenv) c =
  infmachine_type false (sigma,[]) env fenv c

let infexecute_type sigma (sign,fsign) c =
  infmachine_type false (sigma,[]) (gLOB sign) (gLOB fsign) c

let infexemeta sigma metamap (env,fenv) c =
  infmachine true (sigma,metamap) env fenv c

let infexecute_rec sigma (env,fenv) c =
  infmachine false (sigma,[]) env fenv c

let infexecute sigma (sign,fsign) c =
  infmachine false (sigma,[]) (gLOB sign) (gLOB fsign) c

(* A adapter pour les nouveaux env
let fvar_type sigma (sign,fsign) v = 
  let na = destVar v in
  let varty = (snd(lookup_sign na sign))
  in match (snd(infexemeta sigma [] (gLOB sign, gLOB fsign) varty)) with
      Inf ft -> ft.uj_val
    | Logic -> invalid_arg "Fvar with a non-informative type (1)!"

*)

(* MACHINE WITH UNIVERSES *)
(* Il vaudrait mieux typer dans le graphe d'univers de Constraintab,
   recuperer le graphe local, et restaurer l'acien graphe global *)

let whd_instuni = function
    DOP0(Sort(Type(u))) ->
      let u = (if u = dummy_univ then new_univ() else u)
      in DOP0(Sort(Type(u)))
  | c -> c

(* Instantiate universes: replace all dummy_univ by fresh universes.
   This is already done by the machine.
   Indtypes instantiates the universes itself, because in the case of
   large constructor, additionnal constraints must be considered. *)
let instantiate_universes c = strong whd_instuni c


(* sp est le nom de la constante pour laquelle il faut que c soit bien type.
   Cela sert a eviter un clash entre le noms d'univers de 2 modules compiles
   independamment.
   Au lieu de sp, Lib.cwd() serait peut-etre suffisant.
   Cela eviterai de donner un section-path quand on veut typer. *)
let fexecute_type_with_univ sigma sign sp c =
  with_universes (fexecute_type sigma sign) (sp,initial_universes,c) 


let fexecute_with_univ sigma sign sp c =
  with_universes (fexecute sigma sign) (sp,initial_universes,c) 


let infexecute_type_with_univ sigma psign sp c =
  with_universes (infexecute_type sigma psign) (sp,initial_universes,c) 


let infexecute_with_univ sigma psign sp c =
  with_universes (infexecute sigma psign) (sp,initial_universes,c) 
i*)
