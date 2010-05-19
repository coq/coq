(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Compat
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
  | MetaInType of constr

  (* Errors raised by the tactics *)
  | IntroNeedsProduct
  | DoesNotOccurIn of constr * identifier

exception RefinerError of refiner_error

open Pretype_errors

let rec catchable_exception = function
  | Loc.Exc_located(_,e) -> catchable_exception e
  | LtacLocated(_,e) -> catchable_exception e
  | Util.UserError _ | TypeError _
  | RefinerError _ | Indrec.RecursionSchemeError _
  | Nametab.GlobalizationError _ | PretypeError (_,VarNotFound _)
  (* reduction errors *)
  | Tacred.ReductionTacticError _ 
  (* unification errors *)
  | PretypeError(_,(CannotUnify _|CannotUnifyLocal _|CannotGeneralize _
		   |NoOccurrenceFound _|CannotUnifyBindingType _|NotClean _
		   |CannotFindWellTypedAbstraction _|OccurCheck _
		   |UnsolvableImplicit _)) -> true
  | Typeclasses_errors.TypeClassError
      (_, Typeclasses_errors.UnsatisfiableConstraints _) -> true
  | _ -> false

let error_no_such_hypothesis id =
  error ("No such hypothesis: " ^ string_of_id id ^ ".")

(* Tells if the refiner should check that the submitted rules do not
   produce invalid subgoals *)
let check = ref false
let with_check = Flags.with_option check

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
  (hyps,concl, !evdref)

(* The ClearBody tactic *)

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

(* Reordering of the context *)

(* faire le minimum d'echanges pour que l'ordre donne soit un *)
(* sous-ordre du resultat. Par exemple, 2 hyps non mentionnee ne sont *)
(* pas echangees. Choix: les hyps mentionnees ne peuvent qu'etre *)
(* reculees par rapport aux autres (faire le contraire!) *)

let mt_q = (Idmap.empty,[])
let push_val y = function
    (_,[] as q) -> q
  | (m, (x,l)::q) -> (m, (x,Idset.add y l)::q)
let push_item x v (m,l) =
  (Idmap.add x v m, (x,Idset.empty)::l)
let mem_q x (m,_) = Idmap.mem x m
let rec find_q x (m,q) =
  let v = Idmap.find x m in
  let m' = Idmap.remove x m in
  let rec find accs acc = function
      [] -> raise Not_found
    | [(x',l)] ->
        if x=x' then ((v,Idset.union accs l),(m',List.rev acc))
        else raise Not_found
    | (x',l as i)::((x'',l'')::q as itl) ->
        if x=x' then
          ((v,Idset.union accs l),
           (m',List.rev acc@(x'',Idset.add x (Idset.union l l''))::q))
        else find (Idset.union l accs) (i::acc) itl in
  find Idset.empty [] q

let occur_vars_in_decl env hyps d =
  if Idset.is_empty hyps then false else
    let ohyps = global_vars_set_of_decl env d in
    Idset.exists (fun h -> Idset.mem h ohyps) hyps

let reorder_context env sign ord =
  let ords = List.fold_right Idset.add ord Idset.empty in
  if List.length ord <> Idset.cardinal ords then
    error "Order list has duplicates";
  let rec step ord expected ctxt_head moved_hyps ctxt_tail =
    match ord with
      | [] -> List.rev ctxt_tail @ ctxt_head
      | top::ord' when mem_q top moved_hyps ->
          let ((d,h),mh) = find_q top moved_hyps in
          if occur_vars_in_decl env h d then
            errorlabstrm "reorder_context"
              (str "Cannot move declaration " ++ pr_id top ++ spc() ++
              str "before " ++
              prlist_with_sep pr_spc pr_id
                (Idset.elements (Idset.inter h
                  (global_vars_set_of_decl env d))));
          step ord' expected ctxt_head mh (d::ctxt_tail)
      | _ ->
          (match ctxt_head with
            | [] -> error_no_such_hypothesis (List.hd ord)
            | (x,_,_ as d) :: ctxt ->
                if Idset.mem x expected then
                  step ord (Idset.remove x expected)
                    ctxt (push_item x d moved_hyps) ctxt_tail
                else
                  step ord expected
                    ctxt (push_val x moved_hyps) (d::ctxt_tail)) in
  step ord ords sign mt_q []

let reorder_val_context env sign ord =
  val_of_named_context (reorder_context env (named_context_of_val sign) ord)




let check_decl_position env sign (x,_,_ as d) =
  let needed = global_vars_set_of_decl env d in
  let deps = dependency_closure env (named_context_of_val sign) needed in
  if List.mem x deps then
    error ("Cannot create self-referring hypothesis "^string_of_id x);
  x::deps

(* Auxiliary functions for primitive MOVE tactic
 *
 * [move_hyp with_dep toleft (left,(hfrom,typfrom),right) hto] moves
 * hyp [hfrom] at location [hto] which belongs to the hyps on the
 * left side [left] of the full signature if [toleft=true] or to the hyps
 * on the right side [right] if [toleft=false].
 * If [with_dep] then dependent hypotheses are moved accordingly. *)

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
	      errorlabstrm "move_hyp" (str "Cannot move " ++ pr_id idfrom ++
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

let error_unsupported_deep_meta c =
  errorlabstrm "" (strbrk "Application of lemmas whose beta-iota normal " ++
    strbrk "form contains metavariables deep inside the term is not " ++
    strbrk "supported; try \"refine\" instead.")

let collect_meta_variables c =
  let rec collrec deep acc c = match kind_of_term c with
    | Meta mv -> if deep then error_unsupported_deep_meta () else mv::acc
    | Cast(c,_,_) -> collrec deep acc c
    | (App _| Case _) -> fold_constr (collrec deep) acc c
    | _ -> fold_constr (collrec true) acc c
  in
  List.rev (collrec false [] c)

let check_meta_variables c =
  if not (list_distinct (collect_meta_variables c)) then
    raise (RefinerError (NonLinearProof c))

let check_conv_leq_goal env sigma arg ty conclty =
  if !check & not (is_conv_leq env sigma ty conclty) then
    raise (RefinerError (BadType (arg,ty,conclty)))

let goal_type_of env sigma c =
  (if !check then type_of else Retyping.get_type_of ~refresh:true) env sigma c

let rec mk_refgoals sigma goal goalacc conclty trm =
  let env = Goal.V82.env sigma goal in
  let hyps = Goal.V82.hyps sigma goal in
  let mk_goal hyps concl =
    Goal.V82.mk_goal sigma hyps concl (Goal.V82.extra sigma goal)
  in
  match kind_of_term trm with
    | Meta _ ->
	let conclty = nf_betaiota sigma conclty in
	  if !check && occur_meta conclty then
	    raise (RefinerError (MetaInType conclty));
	  let (gl,ev,sigma) = mk_goal hyps conclty in
	  gl::goalacc, conclty, sigma, ev

    | Cast (t,_, ty) ->
	check_typability env sigma ty;
	check_conv_leq_goal env sigma trm ty conclty;
	mk_refgoals sigma goal goalacc ty t

    | App (f,l) ->
	let (acc',hdty,sigma,applicand) =
	  match kind_of_term f with
	    | Ind _ | Const _
		when (isInd f or has_polymorphic_type (destConst f)) ->
		(* Sort-polymorphism of definition and inductive types *)
		goalacc,
                type_of_global_reference_knowing_conclusion env sigma f conclty,
		sigma, f
	    | _ ->
		mk_hdgoals sigma goal goalacc f
	in
	let (acc'',conclty',sigma, args) =
	  mk_arggoals sigma goal acc' hdty (Array.to_list l) in
	check_conv_leq_goal env sigma trm conclty' conclty;
        (acc'',conclty',sigma, Term.mkApp (applicand, Array.of_list args))

    | Case (ci,p,c,lf) ->
	let (acc',lbrty,conclty',sigma,p',c') = mk_casegoals sigma goal goalacc p c in
	check_conv_leq_goal env sigma trm conclty' conclty;
	let (acc'',sigma, rbranches) =
	  array_fold_left2
            (fun (lacc,sigma,bacc) ty fi ->
	       let (r,_,s,b') = mk_refgoals sigma goal lacc ty fi in r,s,(b'::bacc))
            (acc',sigma,[]) lbrty lf
	in
	(acc'',conclty',sigma, Term.mkCase (ci,p',c',Array.of_list (List.rev rbranches)))

    | _ ->
	if occur_meta trm then
	  anomaly "refiner called with a meta in non app/case subterm";

      	let t'ty = goal_type_of env sigma trm in
	check_conv_leq_goal env sigma trm t'ty conclty;
        (goalacc,t'ty,sigma, trm)

(* Same as mkREFGOALS but without knowing the type of the term. Therefore,
 * Metas should be casted. *)

and mk_hdgoals sigma goal goalacc trm =
  let env = Goal.V82.env sigma goal in
  let hyps = Goal.V82.hyps sigma goal in
  let mk_goal hyps concl = 
    Goal.V82.mk_goal sigma hyps concl (Goal.V82.extra sigma goal) in
  match kind_of_term trm with
    | Cast (c,_, ty) when isMeta c ->
	check_typability env sigma ty;
	let (gl,ev,sigma) = mk_goal hyps (nf_betaiota sigma ty) in
	gl::goalacc,ty,sigma,ev

    | Cast (t,_, ty) ->
	check_typability env sigma ty;
	mk_refgoals sigma goal goalacc ty t

    | App (f,l) ->
	let (acc',hdty,sigma,applicand) =
	  if isInd f or isConst f
	     & not (array_exists occur_meta l) (* we could be finer *)
	  then
	   (goalacc,type_of_global_reference_knowing_parameters env sigma f l,sigma,f)
	  else mk_hdgoals sigma goal goalacc f
	in
	let (acc'',conclty',sigma, args) =
	  mk_arggoals sigma goal acc' hdty (Array.to_list l) in
	(acc'',conclty',sigma, Term.mkApp (applicand, Array.of_list args))

    | Case (ci,p,c,lf) ->
	let (acc',lbrty,conclty',sigma,p',c') = mk_casegoals sigma goal goalacc p c in
	let (acc'',sigma,rbranches) =
	  array_fold_left2
            (fun (lacc,sigma,bacc) ty fi ->
	       let (r,_,s,b') = mk_refgoals sigma goal lacc ty fi in r,s,(b'::bacc))
            (acc',sigma,[]) lbrty lf
	in
	(acc'',conclty',sigma, Term.mkCase (ci,p',c',Array.of_list (List.rev rbranches)))

    | _ ->
	if !check && occur_meta trm then
	  anomaly "refine called with a dependent meta";
	goalacc, goal_type_of env sigma trm, sigma, trm

and mk_arggoals sigma goal goalacc funty = function
  | [] -> goalacc,funty,sigma, []
  | harg::tlargs as allargs ->
      let t = whd_betadeltaiota (Goal.V82.env sigma goal) sigma funty in
      match kind_of_term t with
	| Prod (_,c1,b) ->
	    let (acc',hargty,sigma,arg') = mk_refgoals sigma goal goalacc c1 harg in
	    let (acc'',fty, sigma', args) =
	      mk_arggoals sigma goal acc' (subst1 harg b) tlargs in
	    (acc'',fty,sigma',arg'::args)
	| LetIn (_,c1,_,b) ->
	    mk_arggoals sigma goal goalacc (subst1 c1 b) allargs
	| _ -> raise (RefinerError (CannotApply (t,harg)))

and mk_casegoals sigma goal goalacc p c =
  let env = Goal.V82.env sigma goal in
  let (acc',ct,sigma,c') = mk_hdgoals sigma goal goalacc c in
  let (acc'',pt,sigma,p') = mk_hdgoals sigma goal acc' p in
  let indspec =
    try find_mrectype env sigma ct
    with Not_found -> anomaly "mk_casegoals" in
  let (lbrty,conclty) =
    type_case_branches_with_names env indspec p c in
  (acc'',lbrty,conclty,sigma,p',c')


let convert_hyp sign sigma (id,b,bt as d) =
  let env = Global.env() in
  let reorder = ref [] in
  let sign' =
    apply_to_hyp sign id
      (fun _ (_,c,ct) _ ->
        let env = Global.env_of_context sign in
        if !check && not (is_conv env sigma bt ct) then
	  error ("Incorrect change of the type of "^(string_of_id id)^".");
        if !check && not (Option.Misc.compare (is_conv env sigma) b c) then
	  error ("Incorrect change of the body of "^(string_of_id id)^".");
       if !check then reorder := check_decl_position env sign d;
       d) in
  reorder_val_context env sign' !reorder



(************************************************************************)
(************************************************************************)
(* Primitive tactics are handled here *)

let prim_refiner r sigma goal =
  let env = Goal.V82.env sigma goal in
  let sign = Goal.V82.hyps sigma goal in
  let cl = Goal.V82.concl sigma goal in
  let mk_goal hyps concl = 
    Goal.V82.mk_goal sigma hyps concl (Goal.V82.extra sigma goal) 
  in
  match r with
    (* Logical rules *)
    | Intro id ->
    	if !check && mem_named_context id (named_context_of_val sign) then
	  error "New variable is already declared";
        (match kind_of_term (strip_outer_cast cl) with
	   | Prod (_,c1,b) ->
	       let (sg,ev,sigma) = mk_goal (push_named_context_val (id,None,c1) sign)
			  (subst1 (mkVar id) b) in
               let sigma = 
		 Goal.V82.partial_solution sigma goal (mkNamedLambda id c1 ev) in
	       ([sg], sigma)
	   | LetIn (_,c1,t1,b) ->
	       let (sg,ev,sigma) =
		 mk_goal (push_named_context_val (id,Some c1,t1) sign)
		   (subst1 (mkVar id) b) in
	       let sigma = 
		 Goal.V82.partial_solution sigma goal (mkNamedLetIn id c1 t1 ev) in
	       ([sg], sigma)
	   | _ ->
	       raise (RefinerError IntroNeedsProduct))

    | Cut (b,replace,id,t) ->
        let (sg1,ev1,sigma) = mk_goal sign (nf_betaiota sigma t) in
	let sign,cl,sigma =
	  if replace then
	    let nexthyp = get_hyp_after id (named_context_of_val sign) in
	    let sign,cl,sigma = clear_hyps sigma [id] sign cl in
	    move_hyp true false ([],(id,None,t),named_context_of_val sign)
	      nexthyp,
	      cl,sigma
	  else
            (if !check && mem_named_context id (named_context_of_val sign) then
                error "New variable is already declared";
	     push_named_context_val (id,None,t) sign,cl,sigma) in
        let (sg2,ev2,sigma) = 
	  Goal.V82.mk_goal sigma sign cl (Goal.V82.extra sigma goal) in
	let oterm = Term.mkApp (Term.mkNamedLambda id t ev2 , [| ev1 |]) in
	let sigma = Goal.V82.partial_solution sigma goal oterm in
        if b then ([sg1;sg2],sigma) else ([sg2;sg1],sigma)

    | FixRule (f,n,rest,j) ->
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
	let firsts,lasts = list_chop j rest in
	let all = firsts@(f,n,cl)::lasts in
     	let rec mk_sign sign = function
	  | (f,n,ar)::oth ->
	      let (sp',_)  = check_ind env n ar in
	      if not (sp=sp') then
		error ("Fixpoints should be on the same " ^
		       "mutual inductive declaration.");
	      if !check && mem_named_context f (named_context_of_val sign) then
		error
		  ("Name "^string_of_id f^" already used in the environment");
	      mk_sign (push_named_context_val (f,None,ar) sign) oth
	  | [] ->
	      Goal.list_map (fun sigma (_,_,c) ->
				                   let (gl,ev,sig')=
				                     Goal.V82.mk_goal sigma sign c
						             (Goal.V82.extra sigma goal)
						   in ((gl,ev),sig'))
		                              all sigma
	in
	let (gls_evs,sigma) =  mk_sign sign all in
	let (gls,evs) = List.split gls_evs in
	let ids = List.map pi1 all in
	let evs = List.map (Term.subst_vars (List.rev ids)) evs in
	let indxs = Array.of_list (List.map (fun n -> n-1) (List.map pi2 all)) in
	let funnames = Array.of_list (List.map (fun i -> Name i) ids) in
	let typarray = Array.of_list (List.map pi3 all) in
	let bodies = Array.of_list evs in
	let oterm = Term.mkFix ((indxs,0),(funnames,typarray,bodies)) in
	let sigma = Goal.V82.partial_solution sigma goal oterm in
	(gls,sigma)

    | Cofix (f,others,j) ->
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
	let firsts,lasts = list_chop j others in
	let all = firsts@(f,cl)::lasts in
     	List.iter (fun (_,c) -> check_is_coind env c) all;
        let rec mk_sign sign = function
          | (f,ar)::oth ->
	      (try
                (let _ = lookup_named_val f sign in
                error "Name already used in the environment.")
              with
              |	Not_found ->
                  mk_sign (push_named_context_val (f,None,ar) sign) oth)
	  | [] -> Goal.list_map (fun sigma(_,c) ->
				                       let (gl,ev,sigma) =
				                         Goal.V82.mk_goal sigma sign c
							   (Goal.V82.extra sigma goal)
						       in
				                       ((gl,ev),sigma))
	                                             all sigma                                      
     	in
	let (gls_evs,sigma) =  mk_sign sign all in
	let (gls,evs) = List.split gls_evs in
	let (ids,types) = List.split all in
	let evs = List.map (Term.subst_vars (List.rev ids)) evs in
	let funnames = Array.of_list (List.map (fun i -> Name i) ids) in
	let typarray = Array.of_list types in
	let bodies = Array.of_list evs in
	let oterm = Term.mkCoFix (0,(funnames,typarray,bodies)) in
	let sigma = Goal.V82.partial_solution sigma goal oterm in
        (gls,sigma)

    | Refine c ->
	check_meta_variables c;
	let (sgl,cl',sigma,oterm) = mk_refgoals sigma goal [] cl c in
	let sgl = List.rev sgl in
	let sigma = Goal.V82.partial_solution sigma goal oterm in
	  (sgl, sigma)

    (* Conversion rules *)
    | Convert_concl (cl',_) ->
	check_typability env sigma cl';
	if (not !check) || is_conv_leq env sigma cl' cl then
          let (sg,ev,sigma) = mk_goal sign cl' in
	  let sigma = Goal.V82.partial_solution sigma goal ev in
          ([sg], sigma)
	else
	  error "convert-concl rule passed non-converting term"

    | Convert_hyp (id,copt,ty) ->
	let (gl,ev,sigma) = mk_goal (convert_hyp sign sigma (id,copt,ty)) cl in
	let sigma = Goal.V82.partial_solution sigma goal ev in
	([gl], sigma)

    (* And now the structural rules *)
    | Thin ids ->
	let (hyps,concl,nsigma) = clear_hyps sigma ids sign cl in
	let (gl,ev,sigma) =
	  Goal.V82.mk_goal nsigma hyps concl (Goal.V82.extra nsigma goal)
	in
	let sigma = Goal.V82.partial_solution sigma goal ev in
	  ([gl], sigma)

    | ThinBody ids ->
	let clear_aux env id =
          let env' = remove_hyp_body env sigma id in
            if !check then recheck_typability (None,id) env' sigma cl;
            env'
	in
	let sign' = named_context_val (List.fold_left clear_aux env ids) in
     	let (sg,ev,sigma) = mk_goal sign' cl in
	let sigma = Goal.V82.partial_solution sigma goal ev in
     	  ([sg], sigma)

    | Move (withdep, hfrom, hto) ->
  	let (left,right,declfrom,toleft) =
	  split_sign hfrom hto (named_context_of_val sign) in
  	let hyps' =
	  move_hyp withdep toleft (left,declfrom,right) hto in
	let (gl,ev,sigma) = mk_goal hyps' cl in
	let sigma = Goal.V82.partial_solution sigma goal ev in
  	  ([gl], sigma)

    | Order ord ->
        let hyps' = reorder_val_context env sign ord in
	let (gl,ev,sigma) = mk_goal hyps' cl in
	let sigma = Goal.V82.partial_solution sigma goal ev in
        ([gl], sigma)

    | Rename (id1,id2) ->
        if !check & id1 <> id2 &&
	  List.mem id2 (ids_of_named_context (named_context_of_val sign)) then
          error ((string_of_id id2)^" is already used.");
        let sign' = rename_hyp id1 id2 sign in
        let cl' = replace_vars [id1,mkVar id2] cl in
	let (gl,ev,sigma) = mk_goal sign' cl' in
	let ev = Term.replace_vars [(id2,mkVar id1)] ev in
	let sigma = Goal.V82.partial_solution sigma goal ev in
          ([gl], sigma)

    | Change_evars ->
	(* spiwack: a priori [Change_evars] is now devoid of operational content.
	    The new proof engine keeping the evar_map up to date at all time.
	    As a compatibility mesure I leave the rule. 
	    It is possible that my assumption is wrong and some uses of 
	    [Change_evars] are not subsumed by the new engine. In which
	    case something has to be done here. (Feb. 2010) *)
	([goal],sigma)

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
