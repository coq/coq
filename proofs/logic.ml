(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Pp
open Util
open Names
open Nameops
open Evd
open Term
open Termops
open Sign
open Environ
open Reductionops
open Inductive
open Inductiveops
open Typing
open Proof_trees
open Proof_type
open Typeops
open Type_errors
open Coqast
open Declare
open Retyping
open Evarutil

(* Will only be used on terms given to the Refine rule which have meta 
variables only in Application and Case *)

let collect_meta_variables c = 
  let rec collrec acc c = match kind_of_term c with
    | Meta mv -> mv::acc
    | Cast(c,_) -> collrec acc c
    | (App _| Case _) -> fold_constr collrec acc c
    | _ -> acc
  in 
  List.rev(collrec [] c)

type refiner_error =

  (* Errors raised by the refiner *)
  | BadType of constr * constr * constr
  | OccurMeta of constr
  | OccurMetaGoal of constr
  | CannotApply of constr * constr
  | NotWellTyped of constr
  | NonLinearProof of constr

  (* Errors raised by the tactics *)
  | CannotUnify of constr * constr
  | CannotGeneralize of constr
  | BadTacticArgs of string * tactic_arg list
  | IntroNeedsProduct
  | DoesNotOccurIn of constr * identifier

exception RefinerError of refiner_error

let catchable_exception = function
  | Util.UserError _ | TypeError _ | RefinerError _
  | Stdpp.Exc_located(_,(Util.UserError _ | TypeError _ | RefinerError _ |
    Nametab.GlobalizationError _)) -> true
  | _ -> false

let error_cannot_unify (m,n) =
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
  let env = evar_env goal in
  let hyps = goal.evar_hyps in
(*
   if  not (occur_meta trm) then
    let t'ty = (unsafe_machine env sigma trm).uj_type in 	
    let _ = conv_leq_goal env sigma trm t'ty conclty in
      (goalacc,t'ty)
  else
*)
  match kind_of_term trm with
    | Meta _ ->
	if occur_meta conclty then
          raise (RefinerError (OccurMetaGoal conclty));
	(mk_goal hyps (nf_betaiota conclty))::goalacc, conclty

    | Cast (t,ty) ->
	let _ = type_of env sigma ty in
	conv_leq_goal env sigma trm ty conclty;
	mk_refgoals sigma goal goalacc ty t

    | App (f,l) ->
	let (acc',hdty) = mk_hdgoals sigma goal goalacc f in
	let (acc'',conclty') =
	  mk_arggoals sigma goal acc' hdty (Array.to_list l) in
	let _ = conv_leq_goal env sigma trm conclty' conclty in
        (acc'',conclty')

    | Case (_,p,c,lf) ->
	let (acc',lbrty,conclty') = mk_casegoals sigma goal goalacc p c in
	let acc'' = 
	  array_fold_left2
            (fun lacc ty fi -> fst (mk_refgoals sigma goal lacc ty fi))
            acc' lbrty lf 
	in
	let _ = conv_leq_goal env sigma trm conclty' conclty in 
	(acc'',conclty')

    | _ -> 
	if occur_meta trm then raise (RefinerError (OccurMeta trm));
      	let t'ty = type_of env sigma trm in
	conv_leq_goal env sigma trm t'ty conclty;
        (goalacc,t'ty)

(* Same as mkREFGOALS but without knowing te type of the term. Therefore,
 * Metas should be casted. *)

and mk_hdgoals sigma goal goalacc trm =
  let env = evar_env goal in
  let hyps = goal.evar_hyps in
  match kind_of_term trm with
    | Cast (c,ty) when isMeta c ->
	let _ = type_of env sigma ty in
	(mk_goal hyps (nf_betaiota ty))::goalacc,ty

    | App (f,l) ->
	let (acc',hdty) = mk_hdgoals sigma goal goalacc f in
	mk_arggoals sigma goal acc' hdty (Array.to_list l)

    | Case (_,p,c,lf) ->
	let (acc',lbrty,conclty') = mk_casegoals sigma goal goalacc p c in
	let acc'' = 
	  array_fold_left2
            (fun lacc ty fi -> fst (mk_refgoals sigma goal lacc ty fi))
            acc' lbrty lf 
	in
	(acc'',conclty')

    | _ -> goalacc, type_of env sigma trm

and mk_arggoals sigma goal goalacc funty = function
  | [] -> goalacc,funty
  | harg::tlargs as allargs ->
      let t = whd_betadeltaiota (evar_env goal) sigma funty in
      match kind_of_term t with
	| Prod (_,c1,b) ->
	    let (acc',hargty) = mk_refgoals sigma goal goalacc c1 harg in
	    mk_arggoals sigma goal acc' (subst1 harg b) tlargs
	| LetIn (_,c1,_,b) ->
	    mk_arggoals sigma goal goalacc (subst1 c1 b) allargs
	| _ -> raise (RefinerError (CannotApply (t,harg)))

and mk_casegoals sigma goal goalacc p c =
  let env = evar_env goal in
  let (acc',ct) = mk_hdgoals sigma goal goalacc c in 
  let (acc'',pt) = mk_hdgoals sigma goal acc' p in
  let pj = {uj_val=p; uj_type=pt} in 
  let indspec =
    try find_mrectype env sigma ct
    with Induc -> anomaly "mk_casegoals" in
  let (lbrty,conclty) =
    type_case_branches_with_names env indspec pj c in
  (acc'',lbrty,conclty)


let error_use_instantiate () =
  errorlabstrm "Logic.prim_refiner"
    (str"cannot intro when there are open metavars in the domain type" ++
       spc () ++ str"- use Instantiate")
    
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

let move_after with_dep toleft (left,(idfrom,_,_ as declfrom),right) hto =
  let env = Global.env() in
  let test_dep (hyp,c,typ as d) (hyp2,c,typ2 as d2) =
    if toleft
    then occur_var_in_decl env hyp2 d
    else occur_var_in_decl env hyp d2
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

let apply_to_hyp sign id f =
  let found = ref false in
  let sign' =
    fold_named_context_both_sides
      (fun sign (idc,c,ct as d) tail ->
	 if idc = id then begin
	   found := true; f sign d tail
	 end else 
	   add_named_decl d sign)
      sign ~init:empty_named_context
  in
  if (not !check) || !found then sign' else error "No such assumption"

let apply_to_hyp2 env id f =
  let found = ref false in
  let env' =
    fold_named_context_both_sides
      (fun env (idc,c,ct as d) tail ->
	 if idc = id then begin
	   found := true; f env d tail
	 end else 
	   push_named_decl d env)
      (named_context env) ~init:(reset_context env)
  in
  if (not !check) || !found then env' else error "No such assumption"

let global_vars_set_of_var = function
  | (_,None,t) -> global_vars_set (Global.env()) (body_of_type t)
  | (_,Some c,t) ->
      let env =Global.env() in
      Idset.union (global_vars_set env (body_of_type t))
        (global_vars_set env c)

let check_backward_dependencies sign d =
  if not (Idset.for_all
	    (fun id -> mem_named_context id sign)
	    (global_vars_set_of_var d))
  then
    error "Can't introduce at that location: free variable conflict"

let check_forward_dependencies id tail =
  let env = Global.env() in
  List.iter
    (function (id',_,_ as decl) ->
       if occur_var_in_decl env id decl then
	 error ((string_of_id id) ^ " is used in the hypothesis " 
		^ (string_of_id id')))
    tail

let convert_hyp sign sigma id b =
  apply_to_hyp sign id
    (fun sign (idc,c,ct) _ ->
       let env = Global.env_of_context sign in
       match c with
	 | None -> (* Change the type *)
	     if !check && not (is_conv env sigma b ct) then
	       error "convert-hyp rule passed non-converting term";
	     add_named_decl (idc,c,b) sign
	 | Some c -> (* Change the body *)
	     if !check && not (is_conv env sigma b c) then
	       error "convert-hyp rule passed non-converting term";
	     add_named_decl (idc,Some b,ct) sign)

let convert_def inbody sign sigma id c =
  apply_to_hyp sign id
    (fun sign (idc,b,t) _ ->
       let env = Global.env_of_context sign in
       match b with
	 | None -> error "convert-deftype rule passed to an hyp without body" 
	 | Some b ->
	     let b,t = 
	       if inbody then
		 (if !check && not (is_conv env sigma c b) then 
		    error "convert-deftype rule passed non-converting type";
		  (c,t))
	       else
		 (if !check && not (is_conv env sigma c t) then
		    error "convert-deftype rule passed non-converting type";
		  (b,c)) in
	     add_named_decl (idc,Some b,t) sign)

let replace_hyp sign id d =
  apply_to_hyp sign id
    (fun sign _ tail ->
       if !check then
	 (check_backward_dependencies sign d;
	  check_forward_dependencies id tail);
       add_named_decl d sign)

let insert_after_hyp sign id d =
  apply_to_hyp sign id
    (fun sign d' _ ->
       if !check then check_backward_dependencies sign d;
       add_named_decl d (add_named_decl d' sign))

let remove_hyp env id =
  apply_to_hyp env id
    (fun env _ tail ->
       if !check then check_forward_dependencies id tail;
       env)

let recheck_typability (what,id) env sigma t =
  try let _ = type_of env sigma t in ()
  with _ ->
    let s = match what with
      | None -> "the conclusion"
      | Some id -> "hypothesis "^(string_of_id id) in
    error
      ("The correctness of "^s^" relies on the body of "^(string_of_id id))
  
let remove_hyp_body env sigma id =
  apply_to_hyp2 env id
    (fun env (_,c,t) tail ->
       match c with
         | None -> error ((string_of_id id)^" is not a local definition")
         | Some c ->
             let env' = push_named_decl (id,None,t) env in
             if !check then 
               ignore
                 (Sign.fold_named_context 
                    (fun (id',c,t as d) env'' ->
                       (match c with
                          | None -> 
                              recheck_typability (Some id',id) env'' sigma t
                          | Some b ->
                              let b' = mkCast (b,t) in
                              recheck_typability (Some id',id) env'' sigma b');
                       push_named_decl d env'')
                    tail ~init:env');
             env')

(* Primitive tactics are handled here *)

let prim_refiner r sigma goal =
  let env = evar_env goal in
  let sign = goal.evar_hyps in
  let cl = goal.evar_concl in
  match r with
    | { name = Intro; newids = [id] } ->
    	if !check && mem_named_context id sign then
	  error "New variable is already declared";
        (match kind_of_term (strip_outer_cast cl) with
	   | Prod (_,c1,b) ->
	       if occur_meta c1 then error_use_instantiate();
	       let sg = mk_goal (add_named_decl (id,None,c1) sign)
			  (subst1 (mkVar id) b) in
	       [sg]
	   | LetIn (_,c1,t1,b) ->
	       if occur_meta c1 or occur_meta t1 then error_use_instantiate();
	       let sg =
		 mk_goal (add_named_decl (id,Some c1,t1) sign)
		   (subst1 (mkVar id) b) in
	       [sg]
	   | _ ->
	       if !check then raise (RefinerError IntroNeedsProduct)
	       else anomaly "Intro: expects a product")
	
    | { name = Intro_after; newids = [id]; hypspecs = [whereid] } ->
    	if !check && mem_named_context id sign then
	  error "New variable is already declared";
        (match kind_of_term (strip_outer_cast cl) with
	   | Prod (_,c1,b) ->
	       if occur_meta c1 then error_use_instantiate();
	       let sign' = insert_after_hyp sign whereid (id,None,c1) in
	       let sg = mk_goal sign' (subst1 (mkVar id) b) in 
	       [sg]
	   | LetIn (_,c1,t1,b) ->
	       if occur_meta c1 or occur_meta t1 then error_use_instantiate();
	       let sign' = insert_after_hyp sign whereid (id,Some c1,t1) in
	       let sg = mk_goal sign' (subst1 (mkVar id) b) in 
	       [sg]
	   | _ ->
	       if !check then error "Introduction needs a product"
	       else anomaly "Intro_after: expects a product")
	
    | { name = Intro_replacing; newids = []; hypspecs = [id] } ->
	(match kind_of_term (strip_outer_cast cl) with
           | Prod (_,c1,b) ->
	       if occur_meta c1 then error_use_instantiate();
	       let sign' = replace_hyp sign id (id,None,c1) in
	       let sg = mk_goal sign' (subst1 (mkVar id) b) in
	       [sg]
           | LetIn (_,c1,t1,b) ->
	       if occur_meta c1 then error_use_instantiate();
	       let sign' = replace_hyp sign id (id,Some c1,t1) in
	       let sg = mk_goal sign' (subst1 (mkVar id) b) in
	       [sg]
	   | _ ->
	       if !check then error "Introduction needs a product"
	       else anomaly "Intro_replacing: expects a product")
	
    | { name = Cut b; terms = [t]; newids = [id] } ->
        if occur_meta t then error_use_instantiate();
        let sg1 = mk_goal sign (nf_betaiota t) in
        let sg2 = mk_goal (add_named_decl (id,None,t) sign) cl in
        if b then [sg1;sg2] else [sg2;sg1]  

    | { name = FixRule; hypspecs = []; terms = []; 
	newids = [f]; params = [Num(_,n)] } ->
     	let rec check_ind k cl = 
          match kind_of_term (strip_outer_cast cl) with 
            | Prod (_,c1,b) -> 
            	if k = 1 then 
		  try 
		    let _ = find_inductive env sigma c1 in ()
		  with Induc -> 
		    error "cannot do a fixpoint on a non inductive type"
            	else 
		  check_ind (k-1) b
            | _ -> error "not enough products"
	in
     	check_ind n cl;
	if !check && mem_named_context f sign then
	  error ("The name "^(string_of_id f)^" is already used");
        let sg = mk_goal (add_named_decl (f,None,cl) sign) cl in
        [sg]
    
    | { name = FixRule; hypspecs = []; terms = lar; newids = lf; params = ln } ->
     	let rec check_ind k cl = 
          match kind_of_term (strip_outer_cast cl) with 
            | Prod (_,c1,b) -> 
            	if k = 1 then 
		  try 
		    fst (find_inductive env sigma c1)
		  with Induc -> 
		    error "cannot do a fixpoint on a non inductive type"
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
	      if mem_named_context f sign then 
		error "name already used in the environment";
	      mk_sign (add_named_decl (f,None,ar) sign) (lar',lf',ln')
	  | ([],[],[]) -> 
	      List.map (mk_goal sign) (cl::lar)
	  | _ -> error "not the right number of arguments"
	in 
	mk_sign sign (cl::lar,lf,ln)

    | { name = Cofix; hypspecs = []; terms = lar; newids = lf; params = [] } ->
     	let rec check_is_coind cl = 
	  let b = whd_betadeltaiota env sigma cl in
          match kind_of_term b with
            | Prod (_,c1,b) -> check_is_coind  b
            | _ -> 
		try 
		  let _ = find_coinductive env sigma b in ()
                with Induc -> 
		  error ("All methods must construct elements " ^
			  "in coinductive types")
	in
     	List.iter check_is_coind (cl::lar);
        let rec mk_sign sign = function 
          | (ar::lar'),(f::lf') ->
	      (try
                (let _ = Sign.lookup_named f sign in
                error "name already used in the environment")
              with
              |	Not_found ->
                  mk_sign (add_named_decl (f,None,ar) sign) (lar',lf'))
	  | ([],[]) -> List.map (mk_goal sign) (cl::lar)
	  | _ -> error "not the right number of arguments"
     	in 
	mk_sign sign (cl::lar,lf)

    | { name = Refine; terms = [c] } ->
        if not (list_distinct (collect_meta_variables c)) then
          raise (RefinerError (NonLinearProof c));
	let (sgl,cl') = mk_refgoals sigma goal [] cl c in
	let sgl = List.rev sgl in
	sgl

    | { name = Convert_concl; terms = [cl'] } ->
    	let cl'ty = type_of env sigma cl' in
	if is_conv_leq env sigma cl' cl then
          let sg = mk_goal sign cl' in
          [sg]
	else 
	  error "convert-concl rule passed non-converting term"

    | { name = Convert_hyp; hypspecs = [id]; terms = [ty] } ->
	[mk_goal (convert_hyp sign sigma id ty) cl]

    | { name = Convert_defbody; hypspecs = [id]; terms = [c] } ->
	[mk_goal (convert_def true sign sigma id c) cl]

    | { name = Convert_deftype; hypspecs = [id]; terms = [ty] } ->
	[mk_goal (convert_def false sign sigma id ty) cl]

    | { name = Thin; hypspecs = ids } ->
	let clear_aux sign id =
          if !check && occur_var env id cl then
            error ((string_of_id id) ^ " is used in the conclusion.");
          remove_hyp sign id 
	in
	let sign' = List.fold_left clear_aux sign ids in
     	let sg = mk_goal sign' cl in
     	[sg]

    | { name = ThinBody; hypspecs = ids } ->
	let clear_aux env id =
          let env' = remove_hyp_body env sigma id in
          if !check then recheck_typability (None,id) env' sigma cl;
          env'
	in
	let sign' = named_context (List.fold_left clear_aux env ids) in
     	let sg = mk_goal sign' cl in
     	[sg]

    | { name = Move withdep; hypspecs = ids } ->
	let (hfrom,hto) =
	  match ids with [h1;h2] ->(h1,h2)| _ -> anomaly "prim_refiner:MOVE" in
  	let (left,right,declfrom,toleft) = split_sign hfrom hto sign in
  	let hyps' = 
	  move_after withdep toleft (left,declfrom,right) hto in
  	[mk_goal hyps' cl]
	
    | _ -> anomaly "prim_refiner: Unrecognized primitive rule"

let prim_extractor subfun vl pft =
  let cl = pft.goal.evar_concl in
  match pft with
    | { ref = Some (Prim { name = Intro; newids = [id] }, [spf]) } ->
	(match kind_of_term (strip_outer_cast cl) with
	   | Prod (_,ty,_) ->
	       let cty = subst_vars vl ty in
	       mkLambda (Name id, cty, subfun (id::vl) spf)
	   | LetIn (_,b,ty,_) ->
	       let cb = subst_vars vl b in
	       let cty = subst_vars vl ty in
	       mkLetIn (Name id, cb, cty, subfun (id::vl) spf)
	   | _ -> error "incomplete proof!")
	
    | { ref = Some (Prim { name = Intro_after; newids = [id]}, [spf]) } -> 
	(match kind_of_term (strip_outer_cast cl) with
	   | Prod (_,ty,_) ->
	       let cty = subst_vars vl ty in
	       mkLambda (Name id, cty, subfun (id::vl) spf)
	   | LetIn (_,b,ty,_) ->
	       let cb = subst_vars vl b in
	       let cty = subst_vars vl ty in
	       mkLetIn (Name id, cb, cty, subfun (id::vl) spf)
	   | _ -> error "incomplete proof!")
	
    | {ref=Some(Prim{name=Intro_replacing;hypspecs=[id]},[spf]) } ->
	(match kind_of_term (strip_outer_cast cl) with
	   | Prod (_,ty,_) ->
	       let cty = subst_vars vl ty in
	       mkLambda (Name id, cty, subfun (id::vl) spf)
	   | LetIn (_,b,ty,_) ->
	       let cb = subst_vars vl b in
	       let cty = subst_vars vl ty in
	       mkLetIn (Name id, cb, cty, subfun (id::vl) spf)
	   | _ -> error "incomplete proof!")

    | {ref=Some(Prim{name=Cut b;terms=[t];newids=[id]},[spf1;spf2]) } ->
        let spf1, spf2 = if b then spf1, spf2 else spf2, spf1 in
	mkLetIn (Name id,subfun vl spf1,subst_vars vl t,subfun (id::vl) spf2)

    | {ref=Some(Prim{name=FixRule;newids=[f];params=[Num(_,n)]},[spf]) } -> 
	let cty = subst_vars vl cl in 
	let na = Name f in 
	mkFix (([|n-1|],0),([|na|], [|cty|], [|subfun (f::vl) spf|]))

    | {ref=Some(Prim{name=FixRule;newids=lf;terms=lar;params=ln},spfl) } ->
	let lcty = List.map (subst_vars vl) (cl::lar) in 
	let vn = 
	  Array.of_list (List.map (function Num(_,n) -> n-1
				     | _ -> anomaly "mutual_fix_refiner")
			   ln) 
	in 
	let names = Array.map (fun f -> Name f) (Array.of_list lf) in
	let newvl = List.fold_left (fun vl id -> (id::vl)) vl lf  in 
	let lfix =Array.map (subfun newvl) (Array.of_list spfl) in
	mkFix ((vn,0),(names,Array.of_list lcty,lfix))	

    | {ref=Some(Prim{name=Cofix;newids=lf;terms=lar},spfl) } ->
	let lcty = List.map (subst_vars vl) (cl::lar) in 
	let names  = Array.map (fun f -> Name f) (Array.of_list lf) in
	let newvl = List.fold_left (fun vl id -> (id::vl)) vl lf in 
	let lfix =Array.map (subfun newvl) (Array.of_list spfl) in
	mkCoFix (0,(names,Array.of_list lcty,lfix))
	  
    | {ref=Some(Prim{name=Refine;terms=[c]},spfl) } ->
	let mvl = collect_meta_variables c in
	let metamap = List.combine mvl (List.map (subfun vl) spfl) in
	let cc = subst_vars vl c in 
	plain_instance metamap cc
	  
    | {ref=Some(Prim{name=Convert_concl;terms=[c]},[pf])} ->
	subfun vl pf
	
    | {ref=Some(Prim{name=Convert_hyp;hypspecs=[id];terms=[_]},[pf])} ->
	subfun vl pf

    | {ref=Some(Prim{name=Convert_defbody;hypspecs=[id];terms=[_]},[pf])} ->
	subfun vl pf

    | {ref=Some(Prim{name=Convert_deftype;hypspecs=[id];terms=[_]},[pf])} ->
	subfun vl pf
	
    | {ref=Some(Prim{name=Thin;hypspecs=ids},[pf])} ->
     (* No need to make ids Anonymous in vl: subst_vars take the more recent *)
	subfun vl pf
	
    | {ref=Some(Prim{name=ThinBody;hypspecs=ids},[pf])} ->
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
      str"Intro " ++ pr_id id
	
  | {name=Intro_after;newids=[id]} -> 
      str"intro after "  ++ pr_id id
	
  | {name=Intro_replacing;newids=[id]} -> 
      (str"intro replacing "  ++ pr_id id)
	
  | {name=Cut b;terms=[t];newids=[id]} ->
      if b then
        (str"TrueCut " ++ prterm t)
      else
        (str"Cut " ++ prterm t ++ str ";[Intro " ++ pr_id id ++ str "|Idtac]")
	
  | {name=FixRule;newids=[f];params=[Num(_,n)]} -> 
      (str"Fix " ++ pr_id f ++ str"/" ++ int n)
      
  | {name=FixRule;newids=(f::lf);params=(Num(_,n))::ln;terms=lar} -> 
      let rec print_mut = 
        function (f::lf),((Num(_,n))::ln),(ar::lar) -> 
          pr_id f ++ str"/" ++ int n ++ str" : " ++ prterm ar ++
          print_mut (lf,ln,lar)
          | _ -> (mt ()) in
      (str"Fix " ++ pr_id f ++ str"/" ++ int n ++
         str" with " ++ print_mut (lf,ln,lar))
      
  | {name=Cofix;newids=[f];terms=[]} -> 
      (str"Cofix " ++ pr_id f)
      
  | {name=Cofix;newids=(f::lf);terms=lar} -> 
      let rec print_mut = 
        function (f::lf),(ar::lar) -> 
	  (pr_id f ++ str" : " ++ prterm ar ++ print_mut (lf,lar))
          | _ -> (mt ()) 
      in
      (str"Cofix " ++ pr_id f ++  str" with " ++ print_mut (lf,lar))

  | {name=Refine;terms=[c]} -> 
      (str(if occur_meta c then "Refine " else "Exact ")  ++ prterm c)
      
  | {name=Convert_concl;terms=[c]} ->
      (str"Change "  ++ prterm c)
      
  | {name=Convert_hyp;hypspecs=[id];terms=[c]} ->
      (str"Change "  ++ prterm c  ++ spc ()  ++ str"in "  ++ pr_id id)
      
  | {name=Convert_defbody;hypspecs=[id];terms=[c]} ->
      (str"Change "  ++ prterm c  ++ spc ()  ++ str"in "  ++ pr_id id)

  | {name=Convert_deftype;hypspecs=[id];terms=[c]} ->
      (str"Change "  ++ prterm c  ++ spc ()  ++
	 str"in (Type of "  ++ pr_id id ++ str ")")
      
  | {name=Thin;hypspecs=ids} ->
      (str"Clear "  ++ prlist_with_sep pr_spc pr_id ids)
      
  | {name=ThinBody;hypspecs=ids} ->
      (str"ClearBody "  ++ prlist_with_sep pr_spc pr_id ids)
      
  | {name=Move withdep;hypspecs=[id1;id2]} ->
      (str (if withdep then "Dependent " else "") ++
	 str"Move "  ++ pr_id id1 ++ str " after " ++ pr_id id2)
      
  | _ -> anomaly "pr_prim_rule: Unrecognized primitive rule"
