
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
open Inductive
open Typing
open Proof_trees
open Proof_type
open Typeops
open Type_errors
open Coqast
open Declare
open Retyping

type refiner_error =
  | BadType of constr * constr * constr
  | OccurMeta of constr
  | CannotApply of constr * constr
  | CannotUnify of constr * constr
  | CannotGeneralize of constr
  | NotWellTyped of constr
  | BadTacticArgs of string * tactic_arg list

exception RefinerError of refiner_error

let catchable_exception = function
  | Util.UserError _ | TypeError _ | RefinerError _
  | Stdpp.Exc_located(_,(Util.UserError _ | TypeError _ | RefinerError _)) -> 
      true
  | _ -> 
      false

let error_cannot_unify k (m,n) =
  raise (RefinerError (CannotUnify (m,n)))

let check = ref true

let without_check tac gl =
  let c = !check in
  check := false;
  let r = tac gl in
  check := c;
  r

let conv_leq_goal env sigma arg ty conclty =
  if not (is_conv_leq env sigma ty conclty) then 
    raise (RefinerError (BadType (arg,ty,conclty)))

let rec mk_refgoals sigma goal goalacc conclty trm =
  let env = goal.evar_env in
  match trm with
    | DOP0(Meta mv) ->
	if occur_meta conclty then
          error "Cannot refine to conclusions with meta-variables";
	let ctxt = out_some goal.evar_info in 
	(mk_goal ctxt env (nf_betaiota env sigma conclty))::goalacc, conclty

    | DOP2(Cast,t,ty) ->
	let _ = type_of env sigma ty in
	conv_leq_goal env sigma trm ty conclty;
	mk_refgoals sigma goal goalacc ty t

    | DOPN(AppL,cl) ->
	let (acc',hdty) = mk_hdgoals sigma goal goalacc (array_hd cl) in
	let (acc'',conclty') = 
	  mk_arggoals sigma goal acc' hdty (array_list_of_tl cl) in
	let _ = conv_leq_goal env sigma trm conclty' conclty in
        (acc'',conclty')

    | DOPN(MutCase _,_) as mc -> 
	let (_,p,c,lf) = destCase mc in
	let (acc',lbrty,conclty') = mk_casegoals sigma goal goalacc p c in
	let acc'' = 
	  array_fold_left2
            (fun lacc ty fi -> fst (mk_refgoals sigma goal lacc ty fi))
            acc' lbrty lf 
	in
	let _ = conv_leq_goal env sigma trm conclty' conclty in 
	(acc'',conclty')

    | t -> 
	if occur_meta t then raise (RefinerError (OccurMeta t));
      	let t'ty = type_of env sigma t in
	conv_leq_goal env sigma t t'ty conclty;
        (goalacc,t'ty)

(* Same as mkREFGOALS but without knowing te type of the term. Therefore,
 * Metas should be casted. *)

and mk_hdgoals sigma goal goalacc trm =
  let env = goal.evar_env in
  match trm with
    | DOP2(Cast,DOP0(Meta mv),ty) ->
	let _ = type_of env sigma ty in
	let ctxt = out_some goal.evar_info in  
	(mk_goal ctxt env (nf_betaiota env sigma ty))::goalacc,ty
	  
    | DOPN(AppL,cl) ->
	let (acc',hdty) = mk_hdgoals sigma goal goalacc (array_hd cl) in
	mk_arggoals sigma goal acc' hdty (array_list_of_tl cl)
	
    | DOPN(MutCase _,_) as mc -> 
	let (_,p,c,lf) = destCase mc in
	let (acc',lbrty,conclty') = mk_casegoals sigma goal goalacc p c in
	let acc'' = 
	  array_fold_left2
            (fun lacc ty fi -> fst (mk_refgoals sigma goal lacc ty fi))
            acc' lbrty lf 
	in
	(acc'',conclty')

    | t -> goalacc, type_of env sigma t

and mk_arggoals sigma goal goalacc funty = function
  | [] -> goalacc,funty
  | harg::tlargs ->
      let env = goal.evar_env in
      (match whd_betadeltaiota env sigma funty with
	 | DOP2(Prod,c1,DLAM(_,b)) ->
	     let (acc',hargty) = mk_refgoals sigma goal goalacc c1 harg in
	     mk_arggoals sigma goal acc' (subst1 harg b) tlargs
	 | t -> raise (RefinerError (CannotApply (t,harg))))

and mk_casegoals sigma goal goalacc p c =
  let env = goal.evar_env in
  let (acc',ct) = mk_hdgoals sigma goal goalacc c in 
  let (acc'',pt) = mk_hdgoals sigma goal acc' p in
  let indspec =
    try find_rectype env sigma ct
    with Induc -> anomaly "mk_casegoals" in
  let (lbrty,conclty) = type_case_branches env sigma indspec pt p c in
  (acc'',lbrty,conclty)


(* Will only be used on terms given to the Refine rule which have meta 
varaibles only in Application and Case *)

let collect_meta_variables c = 
  let rec collrec acc = function
    | DOP0(Meta mv) -> mv::acc
    | DOP2(Cast,c,_) -> collrec acc c
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
    | (hyp,c,typ) as d :: right ->
      	if hyp = hfrom then 
	  (left,right,d,toleft) 
      	else 
	  splitrec (d::left) (toleft or (hyp = hto)) right
  in 
  splitrec [] false l

let occur_decl hyp (_,c,typ) =
  match c with
    | None -> occur_var hyp (body_of_type typ)
    | Some body -> occur_var hyp (body_of_type typ) || occur_var hyp body

let move_after with_dep toleft (left,(idfrom,_,_ as declfrom),right) hto =
  let test_dep (hyp,c,typ as d) (hyp2,c,typ2 as d2) =
    if toleft
    then occur_decl hyp2 d
    else occur_decl hyp d2
  in
  let rec moverec first middle = function
    | [] -> error ("No such hypothesis : " ^ (string_of_id hto))
    | (hyp,_,_) as d :: right ->
	let (first',middle') =
      	  if List.exists (test_dep d) middle then 
	    if with_dep & (hyp <> hto) then 
	      (first, d::middle)
            else 
	      error 
		("Cannot move "^(string_of_id idfrom)^" after "
		 ^(string_of_id hto)
		 ^(if toleft then ": it occurs in " else ": it depends on ")
		 ^(string_of_id hyp))
          else 
	    (d::first, middle)
	in
      	if hyp = hto then 
	  (List.rev first')@(List.rev middle')@right
      	else 
	  moverec first' middle' right
  in
  if toleft then 
    List.rev_append (moverec [] [declfrom] left) right
  else 
    List.rev_append left (moverec [] [declfrom] right)

let apply_to_hyp env id f =
  let found = ref false in
  let env' =
    process_var_context_both_sides
      (fun env (idc,c,ct as d) tail ->
	 if idc = id then (found:=true; f env d tail) else push_var d env)
      env in
  if (not !check) || !found then env'
  else error "No such assumption"

let global_vars_set_of_var = function
  | (_,None,t) -> global_vars_set (body_of_type t)
  | (_,Some c,t) ->
      Idset.union (global_vars_set (body_of_type t)) (global_vars_set c)

let check_backward_dependencies env d =
  if not (Idset.for_all
	    (fun id -> mem_var_context id (var_context env))
	    (global_vars_set_of_var d))
  then
    error "Can't introduce at that location: free variable conflict"

let check_forward_dependencies id tail =
  List.iter
    (function (id',c,t) ->
       let b = match c with
	 | None -> occur_var id (body_of_type t)
	 | Some body -> occur_var id (body_of_type t) || occur_var id body in
       if b then
	 error ((string_of_id id) ^ " is used in the hypothesis " 
		^ (string_of_id id')))
    tail

let convert_hyp env sigma id ty =
  apply_to_hyp env id
    (fun env (idc,c,ct) _ ->
       if !check && not (is_conv env sigma ty (body_of_type ct)) then
	 error "convert-hyp rule passed non-converting term";
       push_var (idc,c,get_assumption_of env sigma ty) env)

let replace_hyp env id d =
  apply_to_hyp env id
    (fun env _ tail ->
       if !check then
	 (check_backward_dependencies env d;
	  check_forward_dependencies id tail);
       push_var d env)

let insert_after_hyp env id d =
  apply_to_hyp env id
    (fun env d' _ ->
       if !check then check_backward_dependencies env d;
       push_var d (push_var d' env))

let remove_hyp env id =
  apply_to_hyp env id
    (fun env _ tail ->
       if !check then check_forward_dependencies id tail;
       env)

(* Primitive tactics are handled here *)

let prim_refiner r sigma goal =
  let env = goal.evar_env in
  let sign = var_context env in
  let cl = goal.evar_concl in
  let info = out_some goal.evar_info in
  match r with
    | { name = Intro; newids = [id] } ->
    	if !check && mem_var_context id sign then
	  error "New variable is already declared";
        (match strip_outer_cast cl with
	   | DOP2(Prod,c1,DLAM(_,b)) ->
	       if occur_meta c1 then error_use_instantiate();
	       let a = get_assumption_of env sigma c1
	       and v = VAR id in
	       let sg = mk_goal info (push_var_decl (id,a) env) (subst1 v b) in
	       [sg]
	   | _ ->
	       if !check then error "Introduction needs a product"
	       else anomaly "Intro: expects a product")
	
    | { name = Intro_after; newids = [id]; hypspecs = [whereid] } ->
    	if !check && mem_var_context id sign then
	  error "New variable is already declared";
        (match strip_outer_cast cl with
	   | DOP2(Prod,c1,DLAM(_,b)) ->
	       if occur_meta c1 then error_use_instantiate();
	       let a = get_assumption_of env sigma c1
	       and v = VAR id in
	       let env' = insert_after_hyp env whereid (id,None,a) in
	       let sg = mk_goal info env' (subst1 v b) in 
	       [sg]
	   | _ ->
	       if !check then error "Introduction needs a product"
	       else anomaly "Intro_after: expects a product")
	
    | { name = Intro_replacing; newids = []; hypspecs = [id] } ->
	(match strip_outer_cast cl with
           | DOP2(Prod,c1,DLAM(_,b)) ->
	       if occur_meta c1 then error_use_instantiate();
	       let a = get_assumption_of env sigma c1
	       and v = VAR id in
	       let env' = replace_hyp env id (id,None,a) in
	       let sg = mk_goal info env' (subst1 v b) in
	       [sg]
	   | _ ->
	       if !check then error "Introduction needs a product"
	       else anomaly "Intro_replacing: expects a product")
	
    | { name = Fix; hypspecs = []; terms = []; 
	newids = [f]; params = [Num(_,n)] } ->
     	let rec check_ind k cl = 
          match whd_castapp cl with 
            | DOP2(Prod,c1,DLAM(_,b)) -> 
            	if k = 1 then 
		  (try 
		     let _ = find_minductype env sigma c1 in ()
		   with Induc -> 
		     error "cannot do a fixpoint on a non inductive type")
            	else 
		  check_ind (k-1) b
            | _ -> error "not enough products"
	in
     	check_ind n cl;
	if !check && mem_var_context f sign then
	  error ("The name "^(string_of_id f)^" is already used");
        let a = get_assumption_of env sigma cl in
        let sg = mk_goal info (push_var_decl (f,a) env) cl in
        [sg]
    
    | { name = Fix; hypspecs = []; terms = lar; newids = lf; params = ln } ->
     	let rec check_ind k cl = 
          match whd_castapp cl with 
            | DOP2(Prod,c1,DLAM(_,b)) -> 
            	if k = 1 then 
		  (try 
		     fst (find_minductype env sigma c1)
		   with Induc -> 
		     error "cannot do a fixpoint on a non inductive type")
            	else 
		  check_ind (k-1) b
            | _ -> error "not enough products"
	in
	let n = (match ln with (Num(_,n))::_ -> n | _ -> assert false) in
	let (sp,_) = check_ind n cl in
     	let rec mk_sign sign = function 
	  | (ar::lar'),(f::lf'),((Num(_,n))::ln')->
	      let (sp',_)  = check_ind n ar in 
	      if not (sp=sp') then 
		error ("fixpoints should be on the same " ^ 
		       "mutual inductive declaration");
	      if mem_var_context f sign then 
		error "name already used in the environment";
	      let a = get_assumption_of env sigma ar in
	      mk_sign (add_var_decl (f,a) sign) (lar',lf',ln')
	  | ([],[],[]) -> 
	      List.map (mk_goal info env) (cl::lar)
	  | _ -> error "not the right number of arguments"
	in 
	mk_sign sign (cl::lar,lf,ln)

    | { name = Cofix; hypspecs = []; terms = lar; newids = lf; params = [] } ->
     	let rec check_is_coind cl = 
          match (whd_betadeltaiota env sigma (whd_castapp cl)) with 
            | DOP2(Prod,c1,DLAM(_,b)) -> check_is_coind  b
            | b  -> 
		(try 
		   let _ = find_mcoinductype env sigma b in ()
                 with Induc -> 
		   error ("All methods must construct elements " ^
			  "in coinductive types"))
	in
     	List.iter check_is_coind (cl::lar);
        let rec mk_env env = function 
          | (ar::lar'),(f::lf') ->
	      (try
                (let _ = lookup_var f env in
                error "name already used in the environment")
              with
              |	Not_found ->
  	        let a = get_assumption_of env sigma ar in
	        mk_env (push_var_decl (f,a) env) (lar',lf'))
	  | ([],[]) -> List.map (mk_goal info env) (cl::lar)
	  | _ -> error "not the right number of arguments"
     	in 
	mk_env env (cl::lar,lf)

(*        let rec mk_sign sign = function 
          | (ar::lar'),(f::lf') ->
	      if (mem_sign sign f) then 
		error "name already used in the environment";
	      let a = get_assumption_of env sigma ar in
	      mk_sign (add_var_decl (f,a) sign) (lar',lf')
	  | ([],[]) -> List.map (mk_goal info env) (cl::lar)
	  | _ -> error "not the right number of arguments"
     	in 
	mk_sign sign (cl::lar,lf)*)
	  
    | { name = Refine; terms = [c] } ->
	let c = new_meta_variables c in
	let (sgl,cl') = mk_refgoals sigma goal [] cl c in
	let sgl = List.rev sgl in
	sgl

    | { name = Convert_concl; terms = [cl'] } ->
    	let cl'ty = type_of env sigma cl' in
	if is_conv_leq env sigma cl' cl then
          let sg = mk_goal info env (DOP2(Cast,cl',cl'ty)) in
          [sg]
	else 
	  error "convert-concl rule passed non-converting term"

    | { name = Convert_hyp; hypspecs = [id]; terms = [ty'] } ->
	[mk_goal info (convert_hyp env sigma id ty') cl]

    | { name = Thin; hypspecs = ids } ->
	let clear_aux env id =
          if !check && occur_var id cl then
            error ((string_of_id id) ^ " is used in the conclusion.");
          remove_hyp env id in
	let env' = List.fold_left clear_aux env ids in
     	let sg = mk_goal info env' cl in
     	[sg]

    | { name = Move withdep; hypspecs = ids } ->
	let (hfrom,hto) =
	  match ids with [h1;h2] ->(h1,h2)| _ -> anomaly "prim_refiner:MOVE" in
  	let (left,right,declfrom,toleft) = split_sign hfrom hto sign in
  	let hyps' = 
	  move_after withdep toleft (left,declfrom,right) hto in
	let env' = change_hyps (fun _ -> hyps') env in
  	[mk_goal info env' cl]
	
    | _ -> anomaly "prim_refiner: Unrecognized primitive rule"

let prim_extractor subfun vl pft =
  let cl = pft.goal.evar_concl in
  match pft with
    | { ref = Some (Prim { name = Intro; newids = [id] }, [spf]) } ->
	(match strip_outer_cast cl with
	   | DOP2(Prod,ty,b) ->
	       let cty = subst_vars vl ty in
	       DOP2(Lambda,cty, DLAM(Name id,subfun (id::vl) spf))
	   | _ -> error "incomplete proof!")
	
    | { ref = Some (Prim { name = Intro_after; newids = [id]}, [spf]) } -> 
	(match strip_outer_cast cl with
	   | DOP2(Prod,ty,b) ->
	       let cty = subst_vars vl ty in
	       DOP2(Lambda,cty, DLAM(Name id,subfun (id::vl) spf))
	   | _ -> error "incomplete proof!")
	
    | {ref=Some(Prim{name=Intro_replacing;hypspecs=[id]},[spf]) } ->
	(match strip_outer_cast cl with
	   | DOP2(Prod,ty,b) ->
	       let cty = subst_vars vl ty in
	       DOP2(Lambda,cty,DLAM(Name id,subfun (id::vl) spf))
	   | _ -> error "incomplete proof!")
	
    | {ref=Some(Prim{name=Fix;newids=[f];params=[Num(_,n)]},[spf]) } -> 
	let cty = subst_vars vl cl in 
	let na = Name f in 
	DOPN(Term.Fix([|n-1|],0),[| cty ; DLAMV(na,[|subfun (f::vl) spf|])|])
    | {ref=Some(Prim{name=Fix;newids=lf;terms=lar;params=ln},spfl) } ->
	let lcty = List.map (subst_vars vl) (cl::lar) in 
	let vn = 
	  Array.of_list (List.map (function Num(_,n) -> n-1
				     | _ -> anomaly "mutual_fix_refiner")
			   ln) 
	in 
	let lna = List.map (fun f -> Name f) lf in
	let newvl = List.fold_left (fun vl id -> (id::vl)) vl lf  in 
	let lfix =Array.map (subfun newvl) (Array.of_list spfl) in
	mkFix ((vn,0),(Array.of_list lcty,lna,lfix))	

    | {ref=Some(Prim{name=Cofix;newids=lf;terms=lar},spfl) } ->
	let lcty = List.map (subst_vars vl) (cl::lar) in 
	let lna  = List.map (fun f -> Name f) lf in
	let newvl = List.fold_left (fun vl id -> (id::vl)) vl lf in 
	let lfix =Array.map (subfun newvl) (Array.of_list spfl) in
	mkCoFix (0,(Array.of_list lcty,lna,lfix))
	  
    | {ref=Some(Prim{name=Refine;terms=[c]},spfl) } ->
	let mvl = collect_meta_variables c in
	let metamap = List.combine mvl (List.map (subfun vl) spfl) in
	let cc = subst_vars vl c in 
	plain_instance metamap cc
	  
    | {ref=Some(Prim{name=Convert_concl;terms=[c]},[pf])} ->
	subfun vl pf
	
    | {ref=Some(Prim{name=Convert_hyp;hypspecs=[id];terms=[c]},[pf])} ->
	subfun vl pf
	
    | {ref=Some(Prim{name=Thin;hypspecs=ids},[pf])} ->
     (* No need to make ids Anonymous in vl: subst_vars take the more recent *)
	subfun vl pf
	
    | {ref=Some(Prim{name=Move _;hypspecs=ids},[pf])} ->
	subfun vl pf
	  
    | {ref=Some(Prim _,_)} ->
	error "prim_extractor handed unrecognizable primitive proof"
	  
    | {ref=None} -> error "prim_extractor handed incomplete proof"
	  
    | _ -> anomaly "prim_extractor"
	
(* Pretty-printer *)

open Printer

let pr_prim_rule = function
  | {name=Intro;newids=[id]} -> 
      [< 'sTR"Intro " ; print_id id >]
	
  | {name=Intro_after;newids=[id]} -> 
      [< 'sTR"intro after " ; print_id id >]
	
  | {name=Intro_replacing;newids=[id]} -> 
      [< 'sTR"intro replacing " ; print_id id >]
	
  | {name=Fix;newids=[f];params=[Num(_,n)]} -> 
      [< 'sTR"Fix "; print_id f; 'sTR"/"; 'iNT n>]
      
  | {name=Fix;newids=(f::lf);params=(Num(_,n))::ln;terms=lar} -> 
      let rec print_mut = 
        function (f::lf),((Num(_,n))::ln),(ar::lar) -> 
          [< print_id f; 'sTR"/"; 'iNT n; 'sTR" : "; prterm ar;
             print_mut (lf,ln,lar)>]
          | _ -> [<>] in
      [< 'sTR"Fix "; print_id f; 'sTR"/"; 'iNT n;
         'sTR" with "; print_mut (lf,ln,lar) >]
      
  | {name=Cofix;newids=[f];terms=[]} -> 
      [< 'sTR"Cofix "; print_id f >]
      
  | {name=Cofix;newids=(f::lf);terms=lar} -> 
      let rec print_mut = 
        function (f::lf),(ar::lar) -> 
	  [< print_id f; 'sTR" : "; prterm ar; print_mut (lf,lar)>]
          | _ -> [<>] 
      in
      [< 'sTR"Cofix "; print_id f;  'sTR" with "; print_mut (lf,lar) >]

  | {name=Refine;terms=[c]} -> 
      [< 'sTR(if occur_meta c then "Refine " else "Exact ") ; prterm c >]
      
  | {name=Convert_concl;terms=[c]} ->
      [< 'sTR"Change " ; prterm c >]
      
  | {name=Convert_hyp;hypspecs=[id];terms=[c]} ->
      [< 'sTR"Change " ; prterm c ; 'sPC ; 'sTR"in " ; print_id id >]
      
  | {name=Thin;hypspecs=ids} ->
      [< 'sTR"Clear " ; prlist_with_sep pr_spc print_id ids >]
      
  | {name=Move withdep;hypspecs=[id1;id2]} ->
      [< 'sTR (if withdep then "Dependent " else "");
	 'sTR"Move " ; print_id id1; 'sTR " after "; print_id id2 >]
      
  | _ -> anomaly "pr_prim_rule: Unrecognized primitive rule"
