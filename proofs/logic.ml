
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
open Typing
open Proof_trees
open Proof_type
open Typeops
open Type_errors
open Coqast
open Declare

type refiner_error =
  | BadType of constr * constr * constr
  | OccurMeta of constr
  | CannotApply of constr * constr
  | CannotUnify of constr * constr
  | CannotGeneralize of typed_type signature * constr
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
	 | DOP2(Prod,c1,b) ->
	     let (acc',hargty) = mk_refgoals sigma goal goalacc c1 harg in
	     mk_arggoals sigma goal acc' (sAPP b harg) tlargs
	 | t -> raise (RefinerError (CannotApply (t,harg))))

and mk_casegoals sigma goal goalacc p c =
  let env = goal.evar_env in
  let (acc',ct) = mk_hdgoals sigma goal goalacc c in 
  let (acc'',pt) = mk_hdgoals sigma goal acc' p in
  let indspec =
    try find_inductive env sigma ct
    with Induc -> anomaly "mk_casegoals" in
  let (lbrty,conclty) = type_case_branches env sigma indspec pt p c in
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

let mk_assumption env sigma c = execute_type env sigma c
				   
let sign_before id = 
  let rec aux sign =
    if isnull_sign sign then error "no such hypothesis";
    if fst (hd_sign sign) = id then tl_sign sign else aux (tl_sign sign)
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
      occur_var hyp2 (body_of_type typ)
    else 
      occur_var hyp (body_of_type typ2)
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

let prim_refiner r sigma goal =
  let env = goal.evar_env in
  let sign = var_context env in
  let cl = goal.evar_concl in
  let info = out_some goal.evar_info in
  match r with
    | { name = Intro; newids = [id] } ->
    	if mem_sign sign id then error "New variable is already declared";
        (match strip_outer_cast cl with
	   | DOP2(Prod,c1,b) ->
	       if occur_meta c1 then error_use_instantiate();
	       let a = mk_assumption env sigma c1
	       and v = VAR id in
	       let sg = mk_goal info (push_var (id,a) env) (sAPP b v) in 
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
	       let a = mk_assumption env sigma c1
	       and v = VAR id in
	       let env' = change_hyps (add_sign_after whereid (id,a)) env in
	       let sg = mk_goal info env' (sAPP b v) in 
	       [sg]
	   | _ -> error "Introduction needs a product")
	
    | { name = Intro_replacing; newids = []; hypspecs = [id] } ->
	(match strip_outer_cast cl with
           | DOP2(Prod,c1,b) ->
	       if occur_meta c1 then error_use_instantiate();
	       if not (List.for_all 
			 (mem_sign (tl_sign (sign_prefix id sign))) 
			 (global_vars c1))
                 or List.exists (fun t -> occur_var id (body_of_type t)) 
			 (vals_of_sign sign) 
	       then 
		 error 
		   "Can't introduce at that location: free variable conflict";
	       let a = mk_assumption env sigma c1
	       and v = VAR id in
	       let env' = change_hyps (add_sign_replacing id (id,a)) env in
	       let sg = mk_goal info env' (sAPP b v) in
	       [sg]
	   | _ -> error "Introduction needs a product")
	
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
	if mem_sign sign f then error "name already used in the environment";
        let a = mk_assumption env sigma cl in
        let sg = mk_goal info (push_var (f,a) env) cl in
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
	      if mem_sign sign f then 
		error "name already used in the environment";
	      let a = mk_assumption env sigma ar in
	      mk_sign (add_sign (f,a) sign) (lar',lf',ln')
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
        let rec mk_sign sign = function 
          | (ar::lar'),(f::lf') ->
	      if mem_sign sign f then 
		error "name already used in the environment";
	      let a = mk_assumption env sigma ar in
	      mk_sign (add_sign (f,a) sign) (lar',lf')
	  | ([],[]) -> List.map (mk_goal info env) (cl::lar)
	  | _ -> error "not the right number of arguments"
     	in 
	mk_sign sign (cl::lar,lf)
	  
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
      (* Faut-il garder la sorte d'origine ou celle du converti ?? *)
	let env' = change_hyps (sign_before id) env in
    	let tj = execute_type env' sigma ty' in
	if is_conv env sigma ty' (body_of_type (snd(lookup_sign id sign))) then
	  let env' = change_hyps (modify_sign id tj) env in
          [mk_goal info env' cl]
	else 
	  error "convert-hyp rule passed non-converting term"
	    
    | { name = Thin; hypspecs = ids } ->
     	let rec remove_pair s sign =
	  if isnull_sign sign then
	    error ((string_of_id s) ^ " is not among the assumptions.");
	  let (s',ty),tlsign = uncons_sign sign in
	  if s = s' then 
	    tlsign
          else if occur_var s (body_of_type ty) then 
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
	let env' = 
	  change_hyps (fun sign -> List.fold_left clear_aux sign ids) env in
     	let sg = mk_goal info env' cl in
     	[sg]

    | { name = Move withdep; hypspecs = ids } ->
	let (hfrom,hto) =
	  match ids with [h1;h2] ->(h1,h2)| _ -> anomaly "prim_refiner:MOVE" in
  	let hyps = list_of_sign sign in
  	let (left,right,typfrom,toleft) = split_sign hfrom hto hyps in
  	let hyps' = 
	  move_after withdep toleft (left,(hfrom,typfrom),right) hto in
	let env' = change_hyps (fun _ -> make_sign hyps') env in
  	[mk_goal info env' cl]
	
    | _ -> anomaly "prim_refiner: Unrecognized primitive rule"

let abst_value c =
  let env = Global.env () in
  Environ.abst_value env c
	  
let extract_constr = 
  let rec crec vl = function
    | VAR str ->
        (try 
	   (match lookup_id str vl with
              | GLOBNAME (id,_) -> VAR id
              | RELNAME (n,_) -> Rel n)
         with Not_found -> 
           (try global_reference CCI str
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
    | DOP0 _ as c -> c
    | _ -> anomaly "extract_constr : term not matched"
  in 
  crec 


let prim_extractor subfun vl pft =
  let cl = pft.goal.evar_concl in
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
