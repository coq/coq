
(* $Id$ *)

open Pp
open Util
open Names
open Evd
open Generic
open Term
open Sign
open Environ
open Reduction
open Proof_trees
open Typeops
open Coqast
open Declare

type refiner_error =
  | BadType of constr * constr * constr
  | OccurMeta of constr
  | CannotApply of constr * constr

exception RefinerError of refiner_error

let conv_leq_goal env arg ty conclty =
  if not (is_conv_leq env ty conclty) then 
    raise (RefinerError (BadType (arg,ty,conclty)))

let type_of env hyps c =
  failwith "TODO: typage avec VE"

let execute_type env ty =
  failwith "TODO: typage type avec VE"

let rec mk_refgoals env goal goalacc conclty trm =
  let hyps = goal.goal_ev.evar_hyps in
  match trm with
    | DOP0(Meta mv) ->
	if occur_meta conclty then
          error "Cannot refine to conclusions with meta-variables";
	let ctxt = goal.goal_ctxtty in 
	(mk_goal ctxt hyps (nf_betaiota env conclty))::goalacc, conclty

    | DOP2(Cast,t,ty) ->
	let _ = type_of env hyps ty in
	conv_leq_goal env trm ty conclty;
	mk_refgoals env goal goalacc ty t

    | DOPN(AppL,cl) ->
	let (acc',hdty) = mk_hdgoals env goal goalacc (array_hd cl) in
	let (acc'',conclty') = 
	  mk_arggoals env goal acc' hdty (array_list_of_tl cl) in
	let _ = conv_leq_goal env trm conclty' conclty in
        (acc'',conclty')

    | DOPN(MutCase _,_) as mc -> 
	let (_,p,c,lf) = destCase mc in
	let (acc',lbrty,conclty') = mk_casegoals env goal goalacc p c in
	let acc'' = 
	  array_fold_left2
            (fun lacc ty fi -> fst (mk_refgoals env goal lacc ty fi))
            acc' lbrty lf 
	in
	let _ = conv_leq_goal env trm conclty' conclty in 
	(acc'',conclty')

    | t -> 
	if occur_meta t then raise (RefinerError (OccurMeta t));
      	let t'ty = type_of env hyps t in
	conv_leq_goal env t t'ty conclty;
        (goalacc,t'ty)

(* Same as mkREFGOALS but without knowing te type of the term. Therefore,
 * Metas should be casted. *)

and mk_hdgoals env goal goalacc trm =
  let hyps = goal.goal_ev.evar_hyps in
  match trm with
    | DOP2(Cast,DOP0(Meta mv),ty) ->
	let _ = type_of env hyps ty in
	let ctxt = goal.goal_ctxtty in  
	(mk_goal ctxt hyps (nf_betaiota env ty))::goalacc,ty
	  
    | DOPN(AppL,cl) ->
	let (acc',hdty) = mk_hdgoals env goal goalacc (array_hd cl) in
	mk_arggoals env goal acc' hdty (array_list_of_tl cl)
	
    | DOPN(MutCase _,_) as mc -> 
	let (_,p,c,lf) = destCase mc in
	let (acc',lbrty,conclty') = mk_casegoals env goal goalacc p c in
	let acc'' = 
	  array_fold_left2
            (fun lacc ty fi -> fst (mk_refgoals env goal lacc ty fi))
            acc' lbrty lf 
	in
	(acc'',conclty')

    | t -> goalacc,type_of env hyps t

and mk_arggoals env goal goalacc funty = function
  | [] -> goalacc,funty
  | harg::tlargs ->
      (match whd_betadeltaiota env funty with
	 | DOP2(Prod,c1,b) ->
	     let (acc',hargty) = mk_refgoals env goal goalacc c1 harg in
	     mk_arggoals env goal acc' (sAPP b harg) tlargs
	 | t -> raise (RefinerError (CannotApply (t,harg))))

and mk_casegoals env goal goalacc p c= 
  let (acc',ct) = mk_hdgoals env goal goalacc c in 
  let (acc'',pt) = mk_hdgoals env goal acc' p in
  let (_,lbrty,conclty) = type_case_branches env ct pt p c in
  (acc'',lbrty,conclty)


(* Will only be used on terms given to the Refine rule which have meta 
varaibles only in Application and Case *)

let collect_meta_variables c = 
  let rec collrec acc = function
    | DOP0(Meta mv) -> mv::acc
    | DOP2(Cast,c,t) -> collrec acc c
    | DOPN(AppL,cl) -> Array.fold_left collrec acc cl
    | DOPN(MutCase _,_) as mc -> 
	let (_,p,c,lf) = destCase mc in
	Array.fold_left collrec (collrec (collrec acc p) c) lf
    | _ -> acc
  in 
  List.rev(collrec [] c)

let new_meta_variables = 
  let rec newrec = function
    | DOP0(Meta _) -> DOP0(Meta (new_meta()))
    | DOP2(Cast,c,t) -> DOP2(Cast, newrec c, t)
    | DOPN(AppL,cl) -> DOPN(AppL, Array.map newrec cl)
    | DOPN(MutCase _,_) as mc ->
        let (ci,p,c,lf) = destCase mc in
        mkMutCaseA ci (newrec p) (newrec c) (Array.map newrec lf)
    | x -> x
  in 
  newrec

let mk_assumption env c = execute_type env c
				   
let sign_before id = 
  let rec aux = function
    | [],[] -> error "no such hypothesis"
    | sign -> 
	if fst(hd_sign sign) = id then tl_sign sign else aux (tl_sign sign)
  in 
  aux

let error_use_instantiate () =
  errorlabstrm "Logic.prim_refiner"
    [< 'sTR"cannot intro when there are open metavars in the domain type";
       'sPC; 'sTR"- use Instantiate" >]
    
(* Auxiliary functions for primitive MOVE tactic
 *
 * [move_after with_dep toleft (left,(hfrom,typfrom),right) hto] moves
 * hyp [hfrom] just after the hyp [hto] which belongs to the hyps on the 
 * left side [left] of the full signature if [toleft=true] or to the hyps 
 * on the right side [right] if [toleft=false].
 * If [with_dep] then dependent hypotheses are moved accordingly. *)

let split_sign hfrom hto l =
  let rec splitrec left toleft = function
    | [] -> error ("No such hypothesis : " ^ (string_of_id hfrom))
    | (hyp,typ) as h :: right ->
      	if hyp = hfrom then 
	  (left,right,typ,toleft) 
      	else 
	  splitrec (h::left) (toleft or (hyp = hto)) right
  in 
  splitrec [] false l

let move_after with_dep toleft (left,htfrom,right) hto =
  let test_dep (hyp,typ) (hyp2,typ2) =
    if toleft then 
      occur_var hyp2 typ.body
    else 
      occur_var hyp typ2.body 
  in
  let rec moverec first middle = function
    | [] -> error ("No such hypothesis : " ^ (string_of_id hto))
    | (hyp,typ) as ht :: right ->
	let (first',middle') =
      	  if List.exists (test_dep ht) middle then 
	    if with_dep & (hyp <> hto) then 
	      (first, (hyp,typ)::middle)
            else 
	      error 
		("Cannot move "^(string_of_id (fst htfrom))^" after "
		 ^(string_of_id hto)
		 ^(if toleft then ": it occurs in " else ": it depends on ")
		 ^(string_of_id hyp))
          else 
	    ((hyp,typ)::first, middle)
	in
      	if hyp = hto then 
	  (List.rev first')@(List.rev middle')@right
      	else 
	  moverec first' middle' right
  in
  if toleft then 
    List.rev_append (moverec [] [htfrom] left) right
  else 
    List.rev_append left (moverec [] [htfrom] right)
    
(* Primitive tactics are handled here *)

let prim_refiner r env goal =
  let ev = goal.goal_ev in
  let sign = ev.evar_hyps in
  let cl = ev.evar_concl in
  let info = goal.goal_ctxtty in
  match r with
    | { name = Intro; newids = [id] } ->
    	if mem_sign sign id then error "New variable is already declared";
        (match strip_outer_cast cl with
	   | DOP2(Prod,c1,b) ->
	       if occur_meta c1 then error_use_instantiate();
	       let a = mk_assumption env sign c1
	       and v = VAR id in
	       let sg = mk_goal info (add_sign (id,a) sign) (sAPP b v) in 
	       [sg]
	   | _ -> error "Introduction needs a product")
	
    | { name = Intro_after; newids = [id]; hypspecs = [whereid] } ->
    	if mem_sign sign id then error "New variable is already declared";
        (match strip_outer_cast cl with
	   | DOP2(Prod,c1,b) ->
	       if occur_meta c1 then error_use_instantiate();
	       if not (List.for_all
                         (mem_sign (sign_prefix whereid sign))
                         (global_vars c1)) then
		 error 
		   "Can't introduce at that location: free variable conflict";
	       let a = mk_assumption env sign c1
	       and v = VAR id in
	       let sg = mk_goal info 
			  (add_sign_after whereid (id,a) sign) (sAPP b v) in 
	       [sg]
	   | _ -> error "Introduction needs a product")
	
    | { name = Intro_replacing; newids = []; hypspecs = [id] } ->
	(match strip_outer_cast cl with
           | DOP2(Prod,c1,b) ->
	       if occur_meta c1 then error_use_instantiate();
	       if not (List.for_all 
			 (mem_sign (tl_sign (sign_prefix id sign))) 
			 (global_vars c1))
                 or List.exists (fun t -> occur_var id t.body) 
			 (vals_of_sign sign) 
	       then 
		 error 
		   "Can't introduce at that location: free variable conflict";
	       let a = mk_assumption env sign c1
	       and v = VAR id in
	       let sg = mk_goal info (add_sign_replacing id (id,a) sign) 
			  (sAPP b v) in
	       [sg]
	   | _ -> error "Introduction needs a product")
	
    | { name = Fix; hypspecs = []; terms = []; 
	newids = [f]; params = [Num(_,n)] } ->
     	let rec check_ind k cl = 
          match whd_castapp cl with 
            | DOP2(Prod,c1,DLAM(_,b)) -> 
            	if k = 1 then 
		  (try 
		     find_minductype env c1 
		   with Induc -> 
		     error "cannot do a fixpoint on a non inductive type")
            	else 
		  check_ind (k-1) b
            | _ -> error "not enough products"
	in
     	let _ = check_ind n cl in 
	if mem_sign sign f then error "name already used in the environment";
        let a = mk_assumption env sign cl in
        let sg = mk_goal info (add_sign (f,a) sign) cl in
        [sg]
    
    | { name = Fix; hypspecs = []; terms = lar; newids = lf; params = ln } ->
     	let rec check_ind k cl = 
          match whd_castapp cl with 
            | DOP2(Prod,c1,DLAM(_,b)) -> 
            	if k = 1 then 
		  (try 
		     find_minductype env c1 
		   with Induc -> 
		     error "cannot do a fixpoint on a non inductive type")
            	else 
		  check_ind (k-1) b
            | _ -> error "not enough products"
	in
	let n = (match ln with (Num(_,n))::_ -> n | _ -> assert false) in
	let (sp,_,_) = destMutInd (fst (check_ind n cl)) in
     	let rec mk_sign sign = function 
	  | (ar::lar'),(f::lf'),((Num(_,n))::ln')->
	      let (sp',_,_)  = destMutInd (fst (check_ind n ar)) in 
	      if not (sp=sp') then 
		error ("fixpoints should be on the same " ^ 
		       "mutual inductive declaration");
	      if mem_sign sign f then 
		error "name already used in the environment";
	      let a = mk_assumption env sign ar in
	      mk_sign (add_sign (f,a) sign) (lar',lf',ln')
	  | ([],[],[]) -> 
	      List.map (mk_goal info sign) (cl::lar)
	  | _ -> error "not the right number of arguments"
	in 
	mk_sign sign (cl::lar,lf,ln)

    | { name = Cofix; hypspecs = []; terms = lar; newids = lf; params = [] } ->
     	let rec check_is_coind cl = 
          match (whd_betadeltaiota env (whd_castapp cl)) with 
            | DOP2(Prod,c1,DLAM(_,b)) -> check_is_coind  b
            | b  -> 
		(try 
		   let _ = find_mcoinductype env b in true
                 with Induc -> 
		   error ("All methods must construct elements " ^
			  "in coinductive types"))
	in
     	let _ = List.for_all check_is_coind (cl::lar) in
        let rec mk_sign sign = function 
          | (ar::lar'),(f::lf') ->
	      if mem_sign sign f then 
		error "name already used in the environment";
	      let a = mk_assumption env sign ar in
	      mk_sign (add_sign (f,a) sign) (lar',lf')
	  | ([],[]) -> List.map (mk_goal info sign) (cl::lar)
	  | _ -> error "not the right number of arguments"
     	in 
	mk_sign sign (cl::lar,lf)
	  
    | { name = Refine; terms = [c] } ->
	let c = new_meta_variables c in
	let (sgl,cl') = mk_refgoals env goal [] cl c in
	let sgl = List.rev sgl in
	sgl

    | { name = Convert_concl; terms = [cl'] } ->
    	let cl'ty = type_of env sign cl' in
	if is_conv_leq env cl' cl then
          let sg = mk_goal info sign (DOP2(Cast,cl',cl'ty)) in
          [sg]
	else 
	  error "convert-concl rule passed non-converting term"

    | { name = Convert_hyp; hypspecs = [id]; terms = [ty'] } ->
      (* Faut-il garder la sorte d'origine ou celle du converti ?? *)
    	let tj = execute_type env (sign_before id sign) ty' in
	if is_conv env ty' (snd(lookup_sign id sign)).body then
          [mk_goal info (modify_sign id tj sign) cl]
	else 
	  error "convert-hyp rule passed non-converting term"
	    
    | { name = Thin; hypspecs = ids } ->
     	let rec remove_pair s = function
          | ([],[]) -> 
	      error ((string_of_id s) ^ " is not among the assumptions.")
	  | sign -> 
	      let (s',ty),tlsign = uncons_sign sign in
	      if s = s' then 
		tlsign
              else if occur_var s ty.body then 
		error ((string_of_id s) ^ " is used in the hypothesis " 
		       ^ (string_of_id s'))
              else 
		add_sign (s',ty) (remove_pair s tlsign)
	in
	let clear_aux sign s =
          if occur_var s cl then
            error ((string_of_id s) ^ " is used in the conclusion.");
          remove_pair s sign 
	in
     	let sg = mk_goal info (List.fold_left clear_aux sign ids) cl in
     	[sg]

    | { name = Move withdep; hypspecs = ids } ->
	let (hfrom,hto) =
	  match ids with [h1;h2] ->(h1,h2)| _ -> anomaly "prim_refiner:MOVE" in
  	let hyps = list_of_sign sign in
  	let (left,right,typfrom,toleft) = split_sign hfrom hto hyps in
  	let hyps' = 
	  move_after withdep toleft (left,(hfrom,typfrom),right) hto in
  	[mk_goal info (make_sign hyps') cl]
	
    | _ -> anomaly "prim_refiner: Unrecognized primitive rule"

let abst_value c =
  let env = Global.env () in
  Environ.abst_value (Typing.unsafe_env_of_env env) c
	  
let extract_constr = 
  let rec crec vl = function
    | VAR str ->
        (try 
	   (match lookup_id str vl with
              | GLOBNAME (id,_) -> VAR id
              | RELNAME (n,_) -> Rel n)
         with Not_found -> 
           (try global_reference str
            with Not_found -> error ((string_of_id str)^" not declared")))
	
    | (Rel _) as val_0 -> val_0
	  
    | DOP2(Lambda,c1,DLAM(na,c2)) ->
        let u1 = crec vl c1 in
        DOP2(Lambda,u1,DLAM(na,crec (add_rel (Anonymous,u1) vl) c2))
	  
    | DOPN(Term.Fix (x_0,x_1),cl) ->
        let listar = Array.sub cl 0 ((Array.length cl) -1) 
        and def = array_last cl in 
        let newar = Array.map (crec vl) listar in
        let newenv =
          Array.fold_left
	    (fun env ar -> add_rel (Anonymous,ar) env) vl newar in
        let newdef = under_dlams (crec newenv) def in 
        DOPN(Term.Fix (x_0,x_1),Array.append newar [|newdef|])
	  
    | DOPN(CoFix par,cl) ->
        let listar = Array.sub cl 0 ((Array.length cl) -1) 
        and def = array_last cl in 
        let newar = Array.map (crec vl) listar in
        let newenv =
          Array.fold_left (fun env ar -> add_rel (Anonymous,ar) env) vl newar 
	in
        let newdef = under_dlams (crec newenv) def in 
        DOPN(CoFix par,Array.append newar [|newdef|])
	  
    | DOP2(Prod,c1,DLAM(na,c2)) ->
        let u1 = crec vl c1 in
        DOP2(Prod,u1,DLAM(na,crec (add_rel (Anonymous,u1) vl) c2))
	  
    | DOP2(Cast,c,t) -> DOP2(Cast,crec vl c,crec vl t)
    | DOPN(Abst _,_) as val_0 -> crec vl (abst_value val_0)
    | DOPN(oper,cl) -> DOPN(oper,Array.map (crec vl) cl)
    | DOPL(oper,cl) -> DOPL(oper,List.map (crec vl) cl)
    | DOP0(Meta _) as c -> c
    | DOP0 _ as c -> c
    | _ -> anomaly "extract_constr : term not matched"
  in 
  crec 


let prim_extractor subfun vl pft =
  let cl = pft.goal.goal_ev.evar_concl in
  match pft with
    | { ref = Some (Prim { name = Intro; newids = [id] }, [spf]) } ->
	(match strip_outer_cast cl with
	   | DOP2(Prod,ty,b) ->
	       let cty = extract_constr vl ty in
               let na = Name id in 
	       DOP2(Lambda,cty,DLAM(na,subfun (add_rel (na,cty) vl) spf))
	   | _ -> error "incomplete proof!")
	
    | { ref = Some (Prim { name = Intro_after; newids = [id]}, [spf]) } -> 
	(match strip_outer_cast cl with
	   | DOP2(Prod,ty,b) ->
	       let cty = extract_constr vl ty in
               let na = Name id in 
	       DOP2(Lambda,cty,DLAM(na,subfun (add_rel (na,cty) vl) spf))
	   | _ -> error "incomplete proof!")
	
    | {ref=Some(Prim{name=Intro_replacing;hypspecs=[id]},[spf]) } ->
	(match strip_outer_cast cl with
	   | DOP2(Prod,ty,b) ->
	       let cty = extract_constr vl ty in
               let na = Name id in 
	       DOP2(Lambda,cty,DLAM(na,subfun (add_rel (na,cty) vl) spf))
	   | _ -> error "incomplete proof!")
	
    | {ref=Some(Prim{name=Fix;newids=[f];params=[Num(_,n)]},[spf]) } -> 
	let cty = extract_constr vl cl in 
	let na = Name f in 
	DOPN(Term.Fix([|n-1|],0),
	     [| cty ; DLAMV(na,[|subfun (add_rel (na,cty) vl) spf|])|])
	  
    | {ref=Some(Prim{name=Fix;newids=lf;terms=lar;params=ln},spfl) } ->
	let lcty = List.map (extract_constr vl) (cl::lar) in 
	let vn = 
	  Array.of_list (List.map (function Num(_,n) -> n-1
				     | _ -> anomaly "mutual_fix_refiner")
			   ln) 
	in 
	let lna = List.map (fun f -> Name f) lf in
	let newvl = List.fold_left2 (fun sign na ar -> (add_rel (na,ar) sign)) 
                      vl lna lcty in 
	let lfix =Array.map (subfun newvl) (Array.of_list spfl) in
	DOPN(Term.Fix(vn,0),
	     Array.of_list (lcty@[put_DLAMSV (List.rev lna) lfix]))
	
    | {ref=Some(Prim{name=Cofix;newids=lf;terms=lar},spfl) } ->
	let lcty = List.map (extract_constr vl) (cl::lar) in 
	let lna  = List.map (fun f -> Name f) lf in
	let newvl = 
	  List.fold_left2 (fun sign na ar -> (add_rel (na,ar) sign)) 
            vl lna lcty 
	in 
	let lfix =Array.map (subfun newvl) (Array.of_list spfl) in
	DOPN(CoFix(0),Array.of_list (lcty@[put_DLAMSV (List.rev lna) lfix]))
	  
    | {ref=Some(Prim{name=Refine;terms=[c]},spfl) } ->
	let mvl = collect_meta_variables c in
	let metamap = List.combine mvl (List.map (subfun vl) spfl) in
	let cc = extract_constr vl c in 
	plain_instance metamap cc
	  
    | {ref=Some(Prim{name=Convert_concl;terms=[c]},[pf])} ->
	subfun vl pf
	
    | {ref=Some(Prim{name=Convert_hyp;hypspecs=[id];terms=[c]},[pf])} ->
	subfun vl pf
	
    | {ref=Some(Prim{name=Thin;hypspecs=ids},[pf])} ->
	subfun vl pf
	
    | {ref=Some(Prim{name=Move _;hypspecs=ids},[pf])} ->
	subfun vl pf
	  
    | {ref=Some(Prim _,_)} ->
	error "prim_extractor handed unrecognizable primitive proof"
	  
    | {ref=None} -> error "prim_extractor handed incomplete proof"
	  
    | _ -> anomaly "prim_extractor"
	
(***
let prim_extractor = Profile.profile3 "prim_extractor" prim_extractor
let prim_refiner = Profile.profile3 "prim_refiner" prim_refiner
***)
