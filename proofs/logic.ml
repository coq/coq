(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

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
open Retyping
open Evarutil
open Tacexpr
 
type refiner_error =

  (* Errors raised by the refiner *)
  | BadType of constr * constr * constr
  | UnresolvedBindings of name list
  | CannotApply of constr * constr
  | NotWellTyped of constr
  | NonLinearProof of constr

  (* Errors raised by the tactics *)
  | IntroNeedsProduct
  | DoesNotOccurIn of constr * identifier

exception RefinerError of refiner_error

open Pretype_errors

let rec catchable_exception = function
  | Stdpp.Exc_located(_,e) -> catchable_exception e
  | LtacLocated(_,e) -> catchable_exception e
  | Util.UserError _ | TypeError _ 
  | RefinerError _ | Indrec.RecursionSchemeError _
  | Nametab.GlobalizationError _ | PretypeError (_,VarNotFound _)
  (* unification errors *)
  | PretypeError(_,(CannotUnify _|CannotUnifyLocal _|CannotGeneralize _
		   |NoOccurrenceFound _|CannotUnifyBindingType _|NotClean _
		   |CannotFindWellTypedAbstraction _
		   |UnsolvableImplicit _)) -> true
  | Typeclasses_errors.TypeClassError 
      (_, Typeclasses_errors.UnsatisfiableConstraints _) -> true
  | _ -> false

(* Tells if the refiner should check that the submitted rules do not
   produce invalid subgoals *)
let check = ref false
let with_check = Flags.with_option check

(************************************************************************)
(************************************************************************)
(* Implementation of the structural rules (moving and deleting
   hypotheses around) *)

(* The Clear tactic: it scans the context for hypotheses to be removed
   (instead of iterating on the list of identifier to be removed, which
   forces the user to give them in order). *)

let clear_hyps sigma ids sign cl =
  let evdref = ref (Evd.create_goal_evar_defs sigma) in
  let (hyps,concl) = Evarutil.clear_hyps_in_evi evdref sign cl ids in
  (hyps,concl,evars_of !evdref)

(* The ClearBody tactic *)

(* [apply_to_hyp sign id f] splits [sign] into [tail::[id,_,_]::head] and
   returns [tail::(f head (id,_,_) (rev tail))] *)
let apply_to_hyp sign id f =
  try apply_to_hyp sign id f 
  with Hyp_not_found -> 
    if !check then error "No such assumption."
    else sign

let apply_to_hyp_and_dependent_on sign id f g =
  try apply_to_hyp_and_dependent_on sign id f g 
  with Hyp_not_found -> 
    if !check then error "No such assumption."
    else sign

let check_typability env sigma c =
  if !check then let _ = type_of env sigma c in () 

let recheck_typability (what,id) env sigma t =
  try check_typability env sigma t
  with _ ->
    let s = match what with
      | None -> "the conclusion"
      | Some id -> "hypothesis "^(string_of_id id) in
    error
      ("The correctness of "^s^" relies on the body of "^(string_of_id id))
  
let remove_hyp_body env sigma id =
  let sign =
    apply_to_hyp_and_dependent_on (named_context_val env) id
      (fun (_,c,t) _ ->
	match c with
	| None -> error ((string_of_id id)^" is not a local definition.")
	| Some c ->(id,None,t))
      (fun (id',c,t as d) sign ->
	(if !check then
	  begin 
	    let env = reset_with_named_context sign env in
	    match c with
	    | None ->  recheck_typability (Some id',id) env sigma t
	    | Some b ->
		let b' = mkCast (b,DEFAULTcast, t) in
		recheck_typability (Some id',id) env sigma b'
	  end;d))
  in
  reset_with_named_context sign env 

(* Auxiliary functions for primitive MOVE tactic
 *
 * [move_hyp with_dep toleft (left,(hfrom,typfrom),right) hto] moves
 * hyp [hfrom] at location [hto] which belongs to the hyps on the 
 * left side [left] of the full signature if [toleft=true] or to the hyps 
 * on the right side [right] if [toleft=false].
 * If [with_dep] then dependent hypotheses are moved accordingly. *)

let error_no_such_hypothesis id =
  error ("No such hypothesis: " ^ string_of_id id ^ ".")

let rec get_hyp_after h = function
  | [] -> error_no_such_hypothesis h
  | (hyp,_,_) :: right ->
      if hyp = h then
	match right with (id,_,_)::_ -> MoveBefore id | [] -> MoveToEnd false
      else
       get_hyp_after h right

let split_sign hfrom hto l =
  let rec splitrec left toleft = function
    | [] -> error_no_such_hypothesis hfrom
    | (hyp,c,typ) as d :: right ->
      	if hyp = hfrom then 
	  (left,right,d, toleft or hto = MoveToEnd true)
      	else
	  splitrec (d::left) 
	    (toleft or hto = MoveAfter hyp or hto = MoveBefore hyp)
	    right
  in 
    splitrec [] false l

let hyp_of_move_location = function
  | MoveAfter id -> id 
  | MoveBefore id -> id
  | _ -> assert false

let move_hyp with_dep toleft (left,(idfrom,_,_ as declfrom),right) hto =
  let env = Global.env() in
  let test_dep (hyp,c,typ as d) (hyp2,c,typ2 as d2) =
    if toleft
    then occur_var_in_decl env hyp2 d
    else occur_var_in_decl env hyp d2
  in
  let rec moverec first middle = function
    | [] ->
	if match hto with MoveToEnd _ -> false | _ -> true then
	  error_no_such_hypothesis (hyp_of_move_location hto);
	List.rev first @ List.rev middle
    | (hyp,_,_) :: _ as right when hto = MoveBefore hyp ->
	List.rev first @ List.rev middle @ right
    | (hyp,_,_) as d :: right ->
	let (first',middle') =
      	  if List.exists (test_dep d) middle then 
	    if with_dep & hto <> MoveAfter hyp then 
	      (first, d::middle)
            else 
	      errorlabstrm "" (str "Cannot move " ++ pr_id idfrom ++
	        pr_move_location pr_id hto ++ 
	        str (if toleft then ": it occurs in " else ": it depends on ")
	        ++ pr_id hyp ++ str ".")
          else
	    (d::first, middle)
	in
      	if hto = MoveAfter hyp then
	  List.rev first' @ List.rev middle' @ right
      	else 
	  moverec first' middle' right
  in
  if toleft then 
    let right = 
      List.fold_right push_named_context_val right empty_named_context_val in
    List.fold_left (fun sign d -> push_named_context_val d sign)
      right (moverec [] [declfrom] left) 
  else 
    let right = 
      List.fold_right push_named_context_val
	(moverec [] [declfrom] right) empty_named_context_val in
    List.fold_left (fun sign d -> push_named_context_val d sign)
      right left

let rename_hyp id1 id2 sign =
  apply_to_hyp_and_dependent_on sign id1
    (fun (_,b,t) _ -> (id2,b,t))
    (fun d _ -> map_named_declaration (replace_vars [id1,mkVar id2]) d)

(************************************************************************)
(************************************************************************)
(* Implementation of the logical rules *)

(* Will only be used on terms given to the Refine rule which have meta 
variables only in Application and Case *)

let collect_meta_variables c = 
  let rec collrec acc c = match kind_of_term c with
    | Meta mv -> mv::acc
    | Cast(c,_,_) -> collrec acc c
    | (App _| Case _) -> fold_constr collrec acc c
    | _ -> acc
  in 
  List.rev(collrec [] c)

let check_conv_leq_goal env sigma arg ty conclty =
  if !check & not (is_conv_leq env sigma ty conclty) then 
    raise (RefinerError (BadType (arg,ty,conclty)))

let goal_type_of env sigma c =
  (if !check then type_of else Retyping.get_type_of) env sigma c

let rec mk_refgoals sigma goal goalacc conclty trm =
  let env = evar_env goal in
  let hyps = goal.evar_hyps in
  let mk_goal hyps concl = mk_goal hyps concl goal.evar_extra in
(*
   if  not (occur_meta trm) then
    let t'ty = (unsafe_machine env sigma trm).uj_type in 	
    let _ = conv_leq_goal env sigma trm t'ty conclty in
      (goalacc,t'ty)
  else
*)
  match kind_of_term trm with
    | Meta _ ->
	if !check && occur_meta conclty then
	  anomaly "refined called with a dependent meta";
	(mk_goal hyps (nf_betaiota conclty))::goalacc, conclty

    | Cast (t,_, ty) ->
	check_typability env sigma ty;
	check_conv_leq_goal env sigma trm ty conclty;
	mk_refgoals sigma goal goalacc ty t

    | App (f,l) ->
	let (acc',hdty) =
	  match kind_of_term f with
	    | Ind _ | Const _
		when not (array_exists occur_meta l) (* we could be finer *)
		  & (isInd f or has_polymorphic_type (destConst f))
		  ->
		(* Sort-polymorphism of definition and inductive types *)
		goalacc, 
		type_of_global_reference_knowing_parameters env sigma f l
	    | _ -> 
		mk_hdgoals sigma goal goalacc f
	in
	let (acc'',conclty') =
	  mk_arggoals sigma goal acc' hdty (Array.to_list l) in
	check_conv_leq_goal env sigma trm conclty' conclty;
        (acc'',conclty')

    | Case (_,p,c,lf) ->
	let (acc',lbrty,conclty') = mk_casegoals sigma goal goalacc p c in
	check_conv_leq_goal env sigma trm conclty' conclty;
	let acc'' = 
	  array_fold_left2
            (fun lacc ty fi -> fst (mk_refgoals sigma goal lacc ty fi))
            acc' lbrty lf 
	in
	(acc'',conclty')

    | _ -> 
	if occur_meta trm then
	  anomaly "refiner called with a meta in non app/case subterm";
      	let t'ty = goal_type_of env sigma trm in
	check_conv_leq_goal env sigma trm t'ty conclty;
        (goalacc,t'ty)

(* Same as mkREFGOALS but without knowing te type of the term. Therefore,
 * Metas should be casted. *)

and mk_hdgoals sigma goal goalacc trm =
  let env = evar_env goal in
  let hyps = goal.evar_hyps in
  let mk_goal hyps concl = mk_goal hyps concl goal.evar_extra in
  match kind_of_term trm with
    | Cast (c,_, ty) when isMeta c ->
	check_typability env sigma ty;
	(mk_goal hyps (nf_betaiota ty))::goalacc,ty

    | Cast (t,_, ty) ->
	check_typability env sigma ty;
	mk_refgoals sigma goal goalacc ty t

    | App (f,l) ->
	let (acc',hdty) = 
	  if isInd f or isConst f 
	     & not (array_exists occur_meta l) (* we could be finer *)
	  then
	    (goalacc,type_of_global_reference_knowing_parameters env sigma f l)
	  else mk_hdgoals sigma goal goalacc f
	in
	mk_arggoals sigma goal acc' hdty (Array.to_list l)

    | Case (_,p,c,lf) ->
	let (acc',lbrty,conclty') = mk_casegoals sigma goal goalacc p c in
	let acc'' = 
	  array_fold_left2
            (fun lacc ty fi -> fst (mk_refgoals sigma goal lacc ty fi))
            acc' lbrty lf 
	in
	(acc'',conclty')

    | _ ->
	if !check && occur_meta trm then
	  anomaly "refined called with a dependent meta";
	goalacc, goal_type_of env sigma trm

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
    with Not_found -> anomaly "mk_casegoals" in
  let (lbrty,conclty) =
    type_case_branches_with_names env indspec pj c in
  (acc'',lbrty,conclty)


let convert_hyp sign sigma (id,b,bt as d) =
  apply_to_hyp sign id
    (fun _ (_,c,ct) _ ->
       let env = Global.env_of_context sign in
       if !check && not (is_conv env sigma bt ct) then
	 error ("Incorrect change of the type of "^(string_of_id id)^".");
       if !check && not (Option.Misc.compare (is_conv env sigma) b c) then
	 error ("Incorrect change of the body of "^(string_of_id id)^".");
       d)

(* Normalizing evars in a goal. Called by tactic Local_constraints
   (i.e. when the sigma of the proof tree changes). Detect if the
   goal is unchanged *)
let norm_goal sigma gl =
  let red_fun = Evarutil.nf_evar sigma in
  let ncl = red_fun gl.evar_concl in
  let ngl =
    { gl with 
	evar_concl = ncl;
	evar_hyps = map_named_val red_fun gl.evar_hyps } in
    if Evd.eq_evar_info ngl gl then None else Some ngl



(************************************************************************)
(************************************************************************)
(* Primitive tactics are handled here *)

let prim_refiner r sigma goal =
  let env = evar_env goal in
  let sign = goal.evar_hyps in
  let cl = goal.evar_concl in
  let mk_goal hyps concl = mk_goal hyps concl goal.evar_extra in
  match r with
    (* Logical rules *)
    | Intro id ->
    	if !check && mem_named_context id (named_context_of_val sign) then
	  error "New variable is already declared";
        (match kind_of_term (strip_outer_cast cl) with
	   | Prod (_,c1,b) ->
	       let sg = mk_goal (push_named_context_val (id,None,c1) sign)
			  (subst1 (mkVar id) b) in
	       ([sg], sigma)
	   | LetIn (_,c1,t1,b) ->
	       let sg =
		 mk_goal (push_named_context_val (id,Some c1,t1) sign)
		   (subst1 (mkVar id) b) in
	       ([sg], sigma)
	   | _ ->
	       raise (RefinerError IntroNeedsProduct))
	
    | Cut (b,replace,id,t) ->
        let sg1 = mk_goal sign (nf_betaiota t) in
	let sign,cl,sigma =
	  if replace then
	    let nexthyp = get_hyp_after id (named_context_of_val sign) in
	    let sign,cl,sigma = clear_hyps sigma [id] sign cl in
	    move_hyp true false ([],(id,None,t),named_context_of_val sign)
	      nexthyp,
	      cl,sigma
	  else
	    (push_named_context_val (id,None,t) sign),cl,sigma in
        let sg2 = mk_goal sign cl in
        if b then ([sg1;sg2],sigma) else ([sg2;sg1],sigma)

    | FixRule (f,n,rest) ->
     	let rec check_ind env k cl = 
          match kind_of_term (strip_outer_cast cl) with 
            | Prod (na,c1,b) -> 
            	if k = 1 then 
		  try 
		    fst (find_inductive env sigma c1)
		  with Not_found -> 
		    error "Cannot do a fixpoint on a non inductive type."
            	else 
		  check_ind (push_rel (na,None,c1) env) (k-1) b
            | _ -> error "Not enough products."
	in
	let (sp,_) = check_ind env n cl in
	let all = (f,n,cl)::rest in
     	let rec mk_sign sign = function 
	  | (f,n,ar)::oth ->
	      let (sp',_)  = check_ind env n ar in 
	      if not (sp=sp') then 
		error ("Fixpoints should be on the same " ^ 
		       "mutual inductive declaration.");
	      if !check && mem_named_context f (named_context_of_val sign) then
		error "Name already used in the environment";
	      mk_sign (push_named_context_val (f,None,ar) sign) oth
	  | [] -> 
	      List.map (fun (_,_,c) -> mk_goal sign c) all
	in 
	  (mk_sign sign all, sigma)
	
    | Cofix (f,others) ->
     	let rec check_is_coind env cl = 
	  let b = whd_betadeltaiota env sigma cl in
          match kind_of_term b with
            | Prod (na,c1,b) -> check_is_coind (push_rel (na,None,c1) env) b
            | _ -> 
		try 
		  let _ = find_coinductive env sigma b in ()
                with Not_found -> 
		  error ("All methods must construct elements " ^
			  "in coinductive types.")
	in
	let all = (f,cl)::others in
     	List.iter (fun (_,c) -> check_is_coind env c) all;
        let rec mk_sign sign = function 
          | (f,ar)::oth ->
	      (try
                (let _ = lookup_named_val f sign in
                error "Name already used in the environment.")
              with
              |	Not_found ->
                  mk_sign (push_named_context_val (f,None,ar) sign) oth)
	  | [] -> List.map (fun (_,c) -> mk_goal sign c) all
     	in 
	  (mk_sign sign all, sigma)

    | Refine c ->
        if not (list_distinct (collect_meta_variables c)) then
          raise (RefinerError (NonLinearProof c));
	let (sgl,cl') = mk_refgoals sigma goal [] cl c in
	let sgl = List.rev sgl in
	  (sgl, sigma)

    (* Conversion rules *)
    | Convert_concl (cl',_) ->
	check_typability env sigma cl';
	if (not !check) || is_conv_leq env sigma cl' cl then
          let sg = mk_goal sign cl' in
          ([sg], sigma)
	else 
	  error "convert-concl rule passed non-converting term"

    | Convert_hyp (id,copt,ty) ->
	([mk_goal (convert_hyp sign sigma (id,copt,ty)) cl], sigma)

    (* And now the structural rules *)
    | Thin ids -> 
	let (hyps,concl,nsigma) = clear_hyps sigma ids sign cl in
	  ([mk_goal hyps concl], nsigma)
	
    | ThinBody ids ->
	let clear_aux env id =
          let env' = remove_hyp_body env sigma id in
            if !check then recheck_typability (None,id) env' sigma cl;
            env'
	in
	let sign' = named_context_val (List.fold_left clear_aux env ids) in
     	let sg = mk_goal sign' cl in
     	  ([sg], sigma)

    | Move (withdep, hfrom, hto) ->
  	let (left,right,declfrom,toleft) = 
	  split_sign hfrom hto (named_context_of_val sign) in
  	let hyps' = 
	  move_hyp withdep toleft (left,declfrom,right) hto in
  	  ([mk_goal hyps' cl], sigma)

    | Rename (id1,id2) ->
        if !check & id1 <> id2 &&
	  List.mem id2 (ids_of_named_context (named_context_of_val sign)) then
          error ((string_of_id id2)^" is already used.");
        let sign' = rename_hyp id1 id2 sign in
        let cl' = replace_vars [id1,mkVar id2] cl in
          ([mk_goal sign' cl'], sigma)

    | Change_evars ->
        match norm_goal sigma goal with
	    Some ngl -> ([ngl],sigma)
          | None -> ([goal], sigma)

(************************************************************************)
(************************************************************************)
(* Extracting a proof term from the proof tree *)

(* Util *)

type variable_proof_status = ProofVar | SectionVar of identifier

type proof_variable = name * variable_proof_status

let subst_proof_vars = 
  let rec aux p vars =
    let _,subst =
      List.fold_left (fun (n,l) var ->
        let t = match var with
          | Anonymous,_ -> l
          | Name id, ProofVar -> (id,mkRel n)::l
          | Name id, SectionVar id' -> (id,mkVar id')::l in
        (n+1,t)) (p,[]) vars
    in replace_vars (List.rev subst)
  in aux 1
         
let rec rebind id1 id2 = function
  | [] -> [Name id2,SectionVar id1]
  | (na,k as x)::l -> 
      if na = Name id1 then (Name id2,k)::l else
        let l' = rebind id1 id2 l in
        if na = Name id2 then (Anonymous,k)::l' else x::l'

let add_proof_var id vl = (Name id,ProofVar)::vl

let proof_variable_index x = 
  let rec aux n = function
    | (Name id,ProofVar)::l when x = id -> n
    | _::l ->  aux (n+1) l
    | [] -> raise Not_found
  in 
  aux 1

let prim_extractor subfun vl pft =
  let cl = pft.goal.evar_concl in
    match pft.ref with
      | Some (Prim (Intro id), [spf]) ->
	  (match kind_of_term (strip_outer_cast cl) with
	    | Prod (_,ty,_) ->
		let cty = subst_proof_vars vl ty in
		  mkLambda (Name id, cty, subfun (add_proof_var id vl) spf)
	    | LetIn (_,b,ty,_) ->
		let cb = subst_proof_vars vl b in
		let cty = subst_proof_vars vl ty in
		  mkLetIn (Name id, cb, cty, subfun (add_proof_var id vl) spf)
	    | _ -> error "Incomplete proof!")
	    
      | Some (Prim (Cut (b,_,id,t)),[spf1;spf2]) ->
          let spf1, spf2 = if b then spf1, spf2 else spf2, spf1 in
	    mkLetIn (Name id,subfun vl spf1,subst_proof_vars vl t,
                    subfun (add_proof_var id vl) spf2)

      | Some (Prim (FixRule (f,n,others)),spfl) ->
	  let all = Array.of_list ((f,n,cl)::others) in
	  let lcty = Array.map (fun (_,_,ar) -> subst_proof_vars vl ar) all in
	  let names = Array.map (fun (f,_,_) -> Name f) all in
	  let vn = Array.map (fun (_,n,_) -> n-1) all in
	  let newvl = List.fold_left (fun vl (id,_,_) -> add_proof_var id vl)
            (add_proof_var f vl) others in
	  let lfix = Array.map (subfun newvl) (Array.of_list spfl) in
	    mkFix ((vn,0),(names,lcty,lfix))	

      | Some (Prim (Cofix (f,others)),spfl) ->
	  let all = Array.of_list ((f,cl)::others) in
	  let lcty = Array.map (fun (_,ar) -> subst_proof_vars vl ar) all in
	  let names  = Array.map (fun (f,_) -> Name f) all in
	  let newvl = List.fold_left (fun vl (id,_)-> add_proof_var id vl)
            (add_proof_var f vl) others in 
	  let lfix = Array.map (subfun newvl) (Array.of_list spfl) in
	    mkCoFix (0,(names,lcty,lfix))
	      
      | Some (Prim (Refine c),spfl) ->
	  let mvl = collect_meta_variables c in
	  let metamap = List.combine mvl (List.map (subfun vl) spfl) in
	  let cc = subst_proof_vars vl c in 
	    plain_instance metamap cc

      (* Structural and conversion rules do not produce any proof *)
      | Some (Prim (Convert_concl (t,k)),[pf]) ->
	  if k = DEFAULTcast then subfun vl pf
	  else mkCast (subfun vl pf,k,subst_proof_vars vl cl)
      | Some (Prim (Convert_hyp _),[pf]) ->
	  subfun vl pf

      | Some (Prim (Thin _),[pf]) ->
	  (* No need to make ids Anon in vl: subst_proof_vars take the most recent*)
	  subfun vl pf
	    
      | Some (Prim (ThinBody _),[pf]) ->
	  subfun vl pf
	    
      | Some (Prim (Move _),[pf]) ->
	  subfun vl pf

      | Some (Prim (Rename (id1,id2)),[pf]) ->
	  subfun (rebind id1 id2 vl) pf

      | Some (Prim Change_evars, [pf]) ->
	  subfun vl pf

      | Some _ -> anomaly "prim_extractor"

      | None-> error "prim_extractor handed incomplete proof"
	  
