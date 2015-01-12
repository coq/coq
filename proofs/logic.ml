(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Errors
open Util
open Names
open Nameops
open Term
open Vars
open Context
open Termops
open Environ
open Reductionops
open Inductiveops
open Typing
open Proof_type
open Type_errors
open Retyping
open Misctypes

type refiner_error =

  (* Errors raised by the refiner *)
  | BadType of constr * constr * constr
  | UnresolvedBindings of Name.t list
  | CannotApply of constr * constr
  | NotWellTyped of constr
  | NonLinearProof of constr
  | MetaInType of constr

  (* Errors raised by the tactics *)
  | IntroNeedsProduct
  | DoesNotOccurIn of constr * Id.t
  | NoSuchHyp of Id.t

exception RefinerError of refiner_error

open Pretype_errors

(** FIXME: this is quite brittle. Why not accept any PretypeError? *)
let is_typing_error = function
| UnexpectedType (_, _) | NotProduct _
| VarNotFound _ | TypingError _ -> true
| _ -> false

let is_unification_error = function
| CannotUnify _ | CannotUnifyLocal _| CannotGeneralize _
| NoOccurrenceFound _ | CannotUnifyBindingType _
| ActualTypeNotCoercible _ | UnifOccurCheck _
| CannotFindWellTypedAbstraction _ | WrongAbstractionType _
| UnsolvableImplicit _| AbstractionOverMeta _
| UnsatisfiableConstraints _ -> true
| _ -> false

let catchable_exception = function
  | Errors.UserError _ | TypeError _
  | RefinerError _ | Indrec.RecursionSchemeError _
  | Nametab.GlobalizationError _
  (* reduction errors *)
  | Tacred.ReductionTacticError _ -> true
  (* unification and typing errors *)
  | PretypeError(_,_, e) -> is_unification_error e || is_typing_error e 
  | _ -> false

let error_no_such_hypothesis id = raise (RefinerError (NoSuchHyp id))

(* Tells if the refiner should check that the submitted rules do not
   produce invalid subgoals *)
let check = ref false
let with_check = Flags.with_option check

(* [apply_to_hyp sign id f] splits [sign] into [tail::[id,_,_]::head] and
   returns [tail::(f head (id,_,_) (rev tail))] *)
let apply_to_hyp sign id f =
  try apply_to_hyp sign id f
  with Hyp_not_found ->
    if !check then error_no_such_hypothesis id
    else sign

let apply_to_hyp_and_dependent_on sign id f g =
  try apply_to_hyp_and_dependent_on sign id f g
  with Hyp_not_found ->
    if !check then error_no_such_hypothesis id
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

let clear_hyps env sigma ids sign cl =
  let evdref = ref (Evd.create_goal_evar_defs sigma) in
  let (hyps,cl) = Evarutil.clear_hyps_in_evi env evdref sign cl ids in
  (hyps, cl, !evdref)

let clear_hyps2 env sigma ids sign t cl =
  let evdref = ref (Evd.create_goal_evar_defs sigma) in
  let (hyps,t,cl) = Evarutil.clear_hyps2_in_evi env evdref sign t cl ids in
  (hyps, t, cl, !evdref)

(* The ClearBody tactic *)

(* Reordering of the context *)

(* faire le minimum d'echanges pour que l'ordre donne soit un *)
(* sous-ordre du resultat. Par exemple, 2 hyps non mentionnee ne sont *)
(* pas echangees. Choix: les hyps mentionnees ne peuvent qu'etre *)
(* reculees par rapport aux autres (faire le contraire!) *)

let mt_q = (Id.Map.empty,[])
let push_val y = function
    (_,[] as q) -> q
  | (m, (x,l)::q) -> (m, (x,Id.Set.add y l)::q)
let push_item x v (m,l) =
  (Id.Map.add x v m, (x,Id.Set.empty)::l)
let mem_q x (m,_) = Id.Map.mem x m
let find_q x (m,q) =
  let v = Id.Map.find x m in
  let m' = Id.Map.remove x m in
  let rec find accs acc = function
      [] -> raise Not_found
    | [(x',l)] ->
        if Id.equal x x' then ((v,Id.Set.union accs l),(m',List.rev acc))
        else raise Not_found
    | (x',l as i)::((x'',l'')::q as itl) ->
        if Id.equal x x' then
          ((v,Id.Set.union accs l),
           (m',List.rev acc@(x'',Id.Set.add x (Id.Set.union l l''))::q))
        else find (Id.Set.union l accs) (i::acc) itl in
  find Id.Set.empty [] q

let occur_vars_in_decl env hyps d =
  if Id.Set.is_empty hyps then false else
    let ohyps = global_vars_set_of_decl env d in
    Id.Set.exists (fun h -> Id.Set.mem h ohyps) hyps

let reorder_context env sign ord =
  let ords = List.fold_right Id.Set.add ord Id.Set.empty in
  if not (Int.equal (List.length ord) (Id.Set.cardinal ords)) then
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
              pr_sequence pr_id
                (Id.Set.elements (Id.Set.inter h
                  (global_vars_set_of_decl env d))));
          step ord' expected ctxt_head mh (d::ctxt_tail)
      | _ ->
          (match ctxt_head with
            | [] -> error_no_such_hypothesis (List.hd ord)
            | (x,_,_ as d) :: ctxt ->
                if Id.Set.mem x expected then
                  step ord (Id.Set.remove x expected)
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
  if Id.List.mem x deps then
    error ("Cannot create self-referring hypothesis "^Id.to_string x);
  x::deps

(* Auxiliary functions for primitive MOVE tactic
 *
 * [move_hyp with_dep toleft (left,(hfrom,typfrom),right) hto] moves
 * hyp [hfrom] at location [hto] which belongs to the hyps on the
 * left side [left] of the full signature if [toleft=true] or to the hyps
 * on the right side [right] if [toleft=false].
 * If [with_dep] then dependent hypotheses are moved accordingly. *)

let move_location_eq m1 m2 = match m1, m2 with
| MoveAfter id1, MoveAfter id2 -> Id.equal id1 id2
| MoveBefore id1, MoveBefore id2 -> Id.equal id1 id2
| MoveLast, MoveLast -> true
| MoveFirst, MoveFirst -> true
| _ -> false

let rec get_hyp_after h = function
  | [] -> error_no_such_hypothesis h
  | (hyp,_,_) :: right ->
      if Id.equal hyp h then
	match right with (id,_,_)::_ -> MoveBefore id | [] -> MoveFirst
      else
       get_hyp_after h right

let split_sign hfrom hto l =
  let rec splitrec left toleft = function
    | [] -> error_no_such_hypothesis hfrom
    | (hyp,c,typ) as d :: right ->
      	if Id.equal hyp hfrom then
	  (left,right,d, toleft || move_location_eq hto MoveLast)
      	else
          let is_toleft = match hto with
          | MoveAfter h' | MoveBefore h' -> Id.equal hyp h'
          | _ -> false
          in
	  splitrec (d::left) (toleft || is_toleft)
	    right
  in
    splitrec [] false l

let hyp_of_move_location = function
  | MoveAfter id -> id
  | MoveBefore id -> id
  | _ -> assert false

let move_hyp toleft (left,(idfrom,_,_ as declfrom),right) hto =
  let env = Global.env() in
  let test_dep (hyp,c,typ as d) (hyp2,c,typ2 as d2) =
    if toleft
    then occur_var_in_decl env hyp2 d
    else occur_var_in_decl env hyp d2
  in
  let rec moverec first middle = function
    | [] ->
	if match hto with MoveFirst | MoveLast -> false | _ -> true then
	  error_no_such_hypothesis (hyp_of_move_location hto);
	List.rev first @ List.rev middle
    | (hyp,_,_) :: _ as right when move_location_eq hto (MoveBefore hyp) ->
	List.rev first @ List.rev middle @ right
    | (hyp,_,_) as d :: right ->
	let (first',middle') =
      	  if List.exists (test_dep d) middle then
	    if not (move_location_eq hto (MoveAfter hyp)) then
	      (first, d::middle)
            else
	      errorlabstrm "move_hyp" (str "Cannot move " ++ pr_id idfrom ++
	        Miscprint.pr_move_location pr_id hto ++
	        str (if toleft then ": it occurs in " else ": it depends on ")
	        ++ pr_id hyp ++ str ".")
          else
	    (d::first, middle)
	in
      	if move_location_eq hto (MoveAfter hyp) then
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

(**********************************************************************)


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
    | Proj (_, c) -> collrec deep acc c
    | _ -> fold_constr (collrec true) acc c
  in
  List.rev (collrec false [] c)

let check_meta_variables c =
  if not (List.distinct_f Int.compare (collect_meta_variables c)) then
    raise (RefinerError (NonLinearProof c))

let check_conv_leq_goal env sigma arg ty conclty =
  if !check then
    let evm, b = Reductionops.infer_conv env sigma ty conclty in
      if b then evm 
      else raise (RefinerError (BadType (arg,ty,conclty)))
  else sigma

exception Stop of constr list
let meta_free_prefix a =
  try
    let _ = Array.fold_left (fun acc a -> 
      if occur_meta a then raise (Stop acc)
      else a :: acc) [] a
    in a
  with Stop acc -> Array.rev_of_list acc

let goal_type_of env sigma c =
  if !check then type_of env sigma c
  else Retyping.get_type_of env sigma c

let rec mk_refgoals sigma goal goalacc conclty trm =
  let env = Goal.V82.env sigma goal in
  let hyps = Goal.V82.hyps sigma goal in
  let mk_goal hyps concl =
    Goal.V82.mk_goal sigma hyps concl (Goal.V82.extra sigma goal)
  in
    if (not !check) && not (occur_meta trm) then
      let t'ty = Retyping.get_type_of env sigma trm in
      let sigma = check_conv_leq_goal env sigma trm t'ty conclty in
        (goalacc,t'ty,sigma,trm)
    else
      match kind_of_term trm with
      | Meta _ ->
	let conclty = nf_betaiota sigma conclty in
	  if !check && occur_meta conclty then
	    raise (RefinerError (MetaInType conclty));
	  let (gl,ev,sigma) = mk_goal hyps conclty in
	  gl::goalacc, conclty, sigma, ev

      | Cast (t,k, ty) ->
	check_typability env sigma ty;
        let sigma = check_conv_leq_goal env sigma trm ty conclty in
	let res = mk_refgoals sigma goal goalacc ty t in
	(** we keep the casts (in particular VMcast and NATIVEcast) except
	    when they are annotating metas *)
	if isMeta t then begin
	  assert (k != VMcast && k != NATIVEcast);
	  res
	end else
	  let (gls,cty,sigma,ans) = res in
          let ans = if ans == t then trm else mkCast(ans,k,ty) in
	  (gls,cty,sigma,ans)

      | App (f,l) ->
	let (acc',hdty,sigma,applicand) =
	  if is_template_polymorphic env f then
	    let sigma, ty = 
	      (* Template sort-polymorphism of definition and inductive types *)
	      type_of_global_reference_knowing_conclusion env sigma f conclty
	    in
	      goalacc, ty, sigma, f
	  else
	    mk_hdgoals sigma goal goalacc f
	in
	let ((acc'',conclty',sigma), args) = mk_arggoals sigma goal acc' hdty l in
        let sigma = check_conv_leq_goal env sigma trm conclty' conclty in
        let ans = if applicand == f && args == l then trm else Term.mkApp (applicand, args) in
        (acc'',conclty',sigma, ans)

      | Proj (p,c) ->
	let (acc',cty,sigma,c') = mk_hdgoals sigma goal goalacc c in
	let c = mkProj (p, c') in
	let ty = get_type_of env sigma c in
	  (acc',ty,sigma,c)

      | Case (ci,p,c,lf) ->
	let (acc',lbrty,conclty',sigma,p',c') = mk_casegoals sigma goal goalacc p c in
	let sigma = check_conv_leq_goal env sigma trm conclty' conclty in
	let (acc'',sigma, rbranches) =
	  Array.fold_left2
            (fun (lacc,sigma,bacc) ty fi ->
	       let (r,_,s,b') = mk_refgoals sigma goal lacc ty fi in r,s,(b'::bacc))
            (acc',sigma,[]) lbrty lf
	in
        let lf' = Array.rev_of_list rbranches in
        let ans =
          if p' == p && c' == c && Array.equal (==) lf' lf then trm
          else Term.mkCase (ci,p',c',lf')
        in
	(acc'',conclty',sigma, ans)

      | _ ->
	if occur_meta trm then
	  anomaly (Pp.str "refiner called with a meta in non app/case subterm");
	let t'ty = goal_type_of env sigma trm in
	let sigma = check_conv_leq_goal env sigma trm t'ty conclty in
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
	  if is_template_polymorphic env f
	  then
	    let l' = meta_free_prefix l in	      
	   (goalacc,type_of_global_reference_knowing_parameters env sigma f l',sigma,f)
	  else mk_hdgoals sigma goal goalacc f
	in
	let ((acc'',conclty',sigma), args) = mk_arggoals sigma goal acc' hdty l in
        let ans = if applicand == f && args == l then trm else Term.mkApp (applicand, args) in
	(acc'',conclty',sigma, ans)

    | Case (ci,p,c,lf) ->
	let (acc',lbrty,conclty',sigma,p',c') = mk_casegoals sigma goal goalacc p c in
	let (acc'',sigma,rbranches) =
	  Array.fold_left2
            (fun (lacc,sigma,bacc) ty fi ->
	       let (r,_,s,b') = mk_refgoals sigma goal lacc ty fi in r,s,(b'::bacc))
            (acc',sigma,[]) lbrty lf
	in
	let lf' = Array.rev_of_list rbranches in
	let ans =
          if p' == p && c' == c && Array.equal (==) lf' lf then trm
          else Term.mkCase (ci,p',c',lf')
	in
	(acc'',conclty',sigma, ans)

    | Proj (p,c) ->
         let (acc',cty,sigma,c') = mk_hdgoals sigma goal goalacc c in
	 let c = mkProj (p, c') in
         let ty = get_type_of env sigma c in
	   (acc',ty,sigma,c)

    | _ ->
	if !check && occur_meta trm then
	  anomaly (Pp.str "refine called with a dependent meta");
	goalacc, goal_type_of env sigma trm, sigma, trm

and mk_arggoals sigma goal goalacc funty allargs =
  let foldmap (goalacc, funty, sigma) harg =
    let t = whd_betadeltaiota (Goal.V82.env sigma goal) sigma funty in
    let rec collapse t = match kind_of_term t with
    | LetIn (_, c1, _, b) -> collapse (subst1 c1 b)
    | _ -> t
    in
    let t = collapse t in
    match kind_of_term t with
    | Prod (_, c1, b) ->
      let (acc, hargty, sigma, arg) = mk_refgoals sigma goal goalacc c1 harg in
      (acc, subst1 harg b, sigma), arg
    | _ -> raise (RefinerError (CannotApply (t, harg)))
  in
  Array.smartfoldmap foldmap (goalacc, funty, sigma) allargs

and mk_casegoals sigma goal goalacc p c =
  let env = Goal.V82.env sigma goal in
  let (acc',ct,sigma,c') = mk_hdgoals sigma goal goalacc c in
  let (acc'',pt,sigma,p') = mk_hdgoals sigma goal acc' p in
  let indspec =
    try Tacred.find_hnf_rectype env sigma ct
    with Not_found -> anomaly (Pp.str "mk_casegoals") in
  let (lbrty,conclty) = type_case_branches_with_names env indspec p c in
  (acc'',lbrty,conclty,sigma,p',c')


let convert_hyp check sign sigma (id,b,bt as d) =
  let env = Global.env() in
  let reorder = ref [] in
  let sign' =
    apply_to_hyp sign id
      (fun _ (_,c,ct) _ ->
        let env = Global.env_of_context sign in
        if check && not (is_conv env sigma bt ct) then
	  error ("Incorrect change of the type of "^(Id.to_string id)^".");
        if check && not (Option.equal (is_conv env sigma) b c) then
	  error ("Incorrect change of the body of "^(Id.to_string id)^".");
       if check then reorder := check_decl_position env sign d;
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
    | Cut (b,replace,id,t) ->
(*        if !check && not (Retyping.get_sort_of env sigma t) then*)
        let (sg1,ev1,sigma) = mk_goal sign (nf_betaiota sigma t) in
	let sign,t,cl,sigma =
	  if replace then
	    let nexthyp = get_hyp_after id (named_context_of_val sign) in
	    let sign,t,cl,sigma = clear_hyps2 env sigma (Id.Set.singleton id) sign t cl in
	    move_hyp false ([],(id,None,t),named_context_of_val sign)
	      nexthyp,
	      t,cl,sigma
	  else
            (if !check && mem_named_context id (named_context_of_val sign) then
	      error ("Variable " ^ Id.to_string id ^ " is already declared.");
	     push_named_context_val (id,None,t) sign,t,cl,sigma) in
        let (sg2,ev2,sigma) = 
	  Goal.V82.mk_goal sigma sign cl (Goal.V82.extra sigma goal) in
	let oterm = Term.mkApp (mkNamedLambda id t ev2 , [| ev1 |]) in
	let sigma = Goal.V82.partial_solution_to sigma goal sg2 oterm in
        if b then ([sg1;sg2],sigma) else ([sg2;sg1],sigma)

    | FixRule (f,n,rest,j) ->
     	let rec check_ind env k cl =
          match kind_of_term (strip_outer_cast cl) with
            | Prod (na,c1,b) ->
            	if Int.equal k 1 then
		  try
		    fst (find_inductive env sigma c1)
		  with Not_found ->
		    error "Cannot do a fixpoint on a non inductive type."
            	else
		  check_ind (push_rel (na,None,c1) env) (k-1) b
            | _ -> error "Not enough products."
	in
	let ((sp,_),u) = check_ind env n cl in
	let firsts,lasts = List.chop j rest in
	let all = firsts@(f,n,cl)::lasts in
     	let rec mk_sign sign = function
	  | (f,n,ar)::oth ->
	      let ((sp',_),u')  = check_ind env n ar in
	      if not (eq_mind sp sp') then
		error ("Fixpoints should be on the same " ^
		       "mutual inductive declaration.");
	      if !check && mem_named_context f (named_context_of_val sign) then
		error
		  ("Name "^Id.to_string f^" already used in the environment");
	      mk_sign (push_named_context_val (f,None,ar) sign) oth
	  | [] ->
	      Evd.Monad.List.map (fun (_,_,c) sigma ->
                let gl,ev,sig' =
                  Goal.V82.mk_goal sigma sign c (Goal.V82.extra sigma goal) in
                (gl,ev),sig')
              all sigma
	in
	let (gls_evs,sigma) =  mk_sign sign all in
	let (gls,evs) = List.split gls_evs in
	let ids = List.map pi1 all in
	let evs = List.map (Vars.subst_vars (List.rev ids)) evs in
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
	let firsts,lasts = List.chop j others in
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
	  | [] -> 
              Evd.Monad.List.map (fun (_,c) sigma ->
                let gl,ev,sigma =
                  Goal.V82.mk_goal sigma sign c (Goal.V82.extra sigma goal) in
                (gl,ev),sigma)
              all sigma
     	in
	let (gls_evs,sigma) =  mk_sign sign all in
	let (gls,evs) = List.split gls_evs in
	let (ids,types) = List.split all in
	let evs = List.map (Vars.subst_vars (List.rev ids)) evs in
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

    (* And now the structural rules *)
    | Thin ids ->
        let ids = List.fold_left (fun accu x -> Id.Set.add x accu) Id.Set.empty ids in
	let (hyps,concl,nsigma) = clear_hyps env sigma ids sign cl in
	let (gl,ev,sigma) =
	  Goal.V82.mk_goal nsigma hyps concl (Goal.V82.extra nsigma goal)
	in
	let sigma = Goal.V82.partial_solution_to sigma goal gl ev in
	  ([gl], sigma)

    | Move (hfrom, hto) ->
  	let (left,right,declfrom,toleft) =
	  split_sign hfrom hto (named_context_of_val sign) in
  	let hyps' =
	  move_hyp toleft (left,declfrom,right) hto in
	let (gl,ev,sigma) = mk_goal hyps' cl in
	let sigma = Goal.V82.partial_solution_to sigma goal gl ev in
  	  ([gl], sigma)
