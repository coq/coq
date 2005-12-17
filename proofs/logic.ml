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
open Coqast
open Retyping
open Evarutil
 
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
  | CannotUnifyBindingType of constr * constr
  | CannotGeneralize of constr
  | IntroNeedsProduct
  | DoesNotOccurIn of constr * identifier
  | NoOccurrenceFound of constr

exception RefinerError of refiner_error

open Pretype_errors

let catchable_exception = function
  | Util.UserError _ | TypeError _ | RefinerError _
  | Stdpp.Exc_located(_,(Util.UserError _ | TypeError _ | RefinerError _ |
    Nametab.GlobalizationError _ | PretypeError (_,VarNotFound _) | 
    Indtypes.InductiveError (Indtypes.NotAllowedCaseAnalysis _ ))) -> true
  | _ -> false

let error_cannot_unify (m,n) =
  raise (RefinerError (CannotUnify (m,n)))

(* Tells if the refiner should check that the submitted rules do not
   produce invalid subgoals *)
let check = ref false

let without_check tac gl =
  let c = !check in
  check := false;
  try let r = tac gl in check := c; r with e -> check := c; raise e

let with_check = Options.with_option check
   
(************************************************************************)
(************************************************************************)
(* Implementation of the structural rules (moving and deleting
   hypotheses around) *)

let check_clear_forward cleared_ids used_ids whatfor =
  if !check && cleared_ids<>[] then
    Idset.iter
      (fun id' ->
        if List.mem id' cleared_ids then
          error (string_of_id id'^" is used in "^whatfor))
      used_ids

(* The Clear tactic: it scans the context for hypotheses to be removed
   (instead of iterating on the list of identifier to be removed, which
   forces the user to give them in order). *)
let clear_hyps ids gl =
  let env = Global.env() in
  let (nhyps,rmv) =
    Sign.fold_named_context
      (fun (id,c,ty as d) (hyps,rmv) ->
        if List.mem id ids then
          (hyps,id::rmv)
        else begin
          check_clear_forward rmv (global_vars_set_of_decl env d)
            ("hypothesis "^string_of_id id);
          (add_named_decl d hyps, rmv)
        end)
      gl.evar_hyps
      ~init:(empty_named_context,[]) in
  let ncl = gl.evar_concl in
  check_clear_forward rmv (global_vars_set env ncl) "conclusion";
  mk_goal nhyps ncl

(* The ClearBody tactic *)

(* [apply_to_hyp sign id f] splits [sign] into [tail::[id,_,_]::head] and
   returns [tail::(f head (id,_,_) tail)] *)
let apply_to_hyp sign id f =
  let found = ref false in
  let sign' =
    fold_named_context_both_sides
      (fun head (idc,c,ct as d) tail ->
	 if idc = id then begin
	   found := true; f head d tail
	 end else 
	   add_named_decl d head)
      sign ~init:empty_named_context
  in
  if (not !check) || !found then sign' else error "No such assumption"

(* Same but with whole environment *)
let apply_to_hyp2 env id f =
  let found = ref false in
  let env' =
    fold_named_context_both_sides
      (fun env (idc,c,ct as d) tail ->
	 if idc = id then begin
	   found := true; f env d tail
	 end else 
	   push_named d env)
      (named_context env) ~init:(reset_context env)
  in
  if (not !check) || !found then env' else error "No such assumption"

let apply_to_hyp_and_dependent_on sign id f g =
  let found = ref false in
  let sign =
    Sign.fold_named_context
      (fun (idc,_,_ as d) oldest ->
         if idc = id then (found := true; add_named_decl (f d) oldest)
         else if !found then add_named_decl (g d) oldest
         else add_named_decl d oldest)
      sign ~init:empty_named_context
  in
  if (not !check) || !found then sign else error "No such assumption"

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
  apply_to_hyp2 env id
    (fun env (_,c,t) tail ->
       match c with
         | None -> error ((string_of_id id)^" is not a local definition")
         | Some c ->
             let env' = push_named (id,None,t) env in
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
                       push_named d env'')
                    (List.rev tail) ~init:env');
             env')


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

let check_backward_dependencies sign d =
  if not (Idset.for_all
	    (fun id -> mem_named_context id sign)
	    (global_vars_set_of_decl (Global.env()) d))
  then
    error "Can't introduce at that location: free variable conflict"


let check_forward_dependencies id tail =
  let env = Global.env() in
  List.iter
    (function (id',_,_ as decl) ->
       if occur_var_in_decl env id decl then
	 error ((string_of_id id) ^ " is used in hypothesis " 
		^ (string_of_id id')))
    tail


let rename_hyp id1 id2 sign =
  apply_to_hyp_and_dependent_on sign id1
    (fun (_,b,t) -> (id2,b,t))
    (map_named_declaration (replace_vars [id1,mkVar id2]))

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

(************************************************************************)
(************************************************************************)
(* Implementation of the logical rules *)

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

let check_conv_leq_goal env sigma arg ty conclty =
  if !check & not (is_conv_leq env sigma ty conclty) then 
    raise (RefinerError (BadType (arg,ty,conclty)))

let goal_type_of env sigma c =
  (if !check then type_of else Retyping.get_type_of) env sigma c

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
	check_typability env sigma ty;
	check_conv_leq_goal env sigma trm ty conclty;
	mk_refgoals sigma goal goalacc ty t

    | App (f,l) ->
	let (acc',hdty) = mk_hdgoals sigma goal goalacc f in
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
	if occur_meta trm then raise (RefinerError (OccurMeta trm));
      	let t'ty = goal_type_of env sigma trm in
	check_conv_leq_goal env sigma trm t'ty conclty;
        (goalacc,t'ty)

(* Same as mkREFGOALS but without knowing te type of the term. Therefore,
 * Metas should be casted. *)

and mk_hdgoals sigma goal goalacc trm =
  let env = evar_env goal in
  let hyps = goal.evar_hyps in
  match kind_of_term trm with
    | Cast (c,ty) when isMeta c ->
	check_typability env sigma ty;
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

    | _ -> goalacc, goal_type_of env sigma trm

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


let error_use_instantiate () =
  errorlabstrm "Logic.prim_refiner"
    (str"cannot intro when there are open metavars in the domain type" ++
       spc () ++ str"- use Instantiate")

let convert_hyp sign sigma (id,b,bt as d) =
  apply_to_hyp sign id
    (fun sign (_,c,ct) _ ->
       let env = Global.env_of_context sign in
       if !check && not (is_conv env sigma bt ct) then
	 (* Just a warning in V8.0bugfix for compatibility *)
	 msgnl (str "Compatibility warning: Hazardeous change of the type of " ++ pr_id id ++ 
	       str " (not well-typed in current signature)");
       if !check && not (option_compare (is_conv env sigma) b c) then
	 msgnl (str "Compatibility warning: Hazardeous change of the body of " ++ pr_id id ++
	       str " (not well-typed in current signature)");
       add_named_decl d sign)


(************************************************************************)
(************************************************************************)
(* Primitive tactics are handled here *)

let prim_refiner r sigma goal =
  let env = evar_env goal in
  let sign = goal.evar_hyps in
  let cl = goal.evar_concl in
  match r with
    (* Logical rules *)
    | Intro id ->
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
	       raise (RefinerError IntroNeedsProduct))
	
    | Intro_replacing id ->
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
	       raise (RefinerError IntroNeedsProduct))
	
    | Cut (b,id,t) ->
    	if !check && mem_named_context id sign then
	  error "New variable is already declared";
        if occur_meta t then error_use_instantiate();
        let sg1 = mk_goal sign (nf_betaiota t) in
        let sg2 = mk_goal (add_named_decl (id,None,t) sign) cl in
        if b then [sg1;sg2] else [sg2;sg1]  

    | FixRule (f,n,rest) ->
     	let rec check_ind env k cl = 
          match kind_of_term (strip_outer_cast cl) with 
            | Prod (na,c1,b) -> 
            	if k = 1 then 
		  try 
		    fst (find_inductive env sigma c1)
		  with Not_found -> 
		    error "cannot do a fixpoint on a non inductive type"
            	else 
		  check_ind (push_rel (na,None,c1) env) (k-1) b
            | _ -> error "not enough products"
	in
	let (sp,_) = check_ind env n cl in
	let all = (f,n,cl)::rest in
     	let rec mk_sign sign = function 
	  | (f,n,ar)::oth ->
	      let (sp',_)  = check_ind env n ar in 
	      if not (sp=sp') then 
		error ("fixpoints should be on the same " ^ 
		       "mutual inductive declaration");
	      if !check && mem_named_context f sign then 
		error "name already used in the environment";
	      mk_sign (add_named_decl (f,None,ar) sign) oth
	  | [] -> 
	      List.map (fun (_,_,c) -> mk_goal sign c) all
	in 
	mk_sign sign all
	
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
			  "in coinductive types")
	in
	let all = (f,cl)::others in
     	List.iter (fun (_,c) -> check_is_coind env c) all;
        let rec mk_sign sign = function 
          | (f,ar)::oth ->
	      (try
                (let _ = Sign.lookup_named f sign in
                error "name already used in the environment")
              with
              |	Not_found ->
                  mk_sign (add_named_decl (f,None,ar) sign) oth)
	  | [] -> List.map (fun (_,c) -> mk_goal sign c) all
     	in 
	mk_sign sign all

    | Refine c ->
        if not (list_distinct (collect_meta_variables c)) then
          raise (RefinerError (NonLinearProof c));
	let (sgl,cl') = mk_refgoals sigma goal [] cl c in
	let sgl = List.rev sgl in
	sgl

    (* Conversion rules *)
    | Convert_concl cl' ->
	check_typability env sigma cl';
	if (not !check) || is_conv_leq env sigma cl' cl then
          let sg = mk_goal sign cl' in
          [sg]
	else 
	  error "convert-concl rule passed non-converting term"

    | Convert_hyp (id,copt,ty) ->
	[mk_goal (convert_hyp sign sigma (id,copt,ty)) cl]

    (* And now the structural rules *)
    | Thin ids -> 
	[clear_hyps ids goal]

    | ThinBody ids ->
	let clear_aux env id =
          let env' = remove_hyp_body env sigma id in
          if !check then recheck_typability (None,id) env' sigma cl;
          env'
	in
	let sign' = named_context (List.fold_left clear_aux env ids) in
     	let sg = mk_goal sign' cl in
     	[sg]

    | Move (withdep, hfrom, hto) ->
  	let (left,right,declfrom,toleft) = split_sign hfrom hto sign in
  	let hyps' = 
	  move_after withdep toleft (left,declfrom,right) hto in
  	[mk_goal hyps' cl]

    | Rename (id1,id2) ->
        if !check & id1 <> id2 & List.mem id2 (ids_of_named_context sign) then
          error ((string_of_id id2)^" is already used");
        let sign' = rename_hyp id1 id2 sign in
        let cl' = replace_vars [id1,mkVar id2] cl in
        [mk_goal sign' cl']

(************************************************************************)
(************************************************************************)
(* Extracting a proof term from the proof tree *)

(* Util *)
let rec rebind id1 id2 = function
  | [] -> []
  | id::l -> 
      if id = id1 then id2::l else
        let l' = rebind id1 id2 l in
        if id = id2 then
          (* TODO: find a more elegant way to hide a variable *)
          (id_of_string "_@")::l'
        else id::l'

let prim_extractor subfun vl pft =
  let cl = pft.goal.evar_concl in
  match pft.ref with
    | Some (Prim (Intro id), [spf]) ->
	(match kind_of_term (strip_outer_cast cl) with
	   | Prod (_,ty,_) ->
	       let cty = subst_vars vl ty in
	       mkLambda (Name id, cty, subfun (id::vl) spf)
	   | LetIn (_,b,ty,_) ->
	       let cb = subst_vars vl b in
	       let cty = subst_vars vl ty in
	       mkLetIn (Name id, cb, cty, subfun (id::vl) spf)
	   | _ -> error "incomplete proof!")
	
    | Some (Prim (Intro_replacing id),[spf]) ->
	(match kind_of_term (strip_outer_cast cl) with
	   | Prod (_,ty,_) ->
	       let cty = subst_vars vl ty in
	       mkLambda (Name id, cty, subfun (id::vl) spf)
	   | LetIn (_,b,ty,_) ->
	       let cb = subst_vars vl b in
	       let cty = subst_vars vl ty in
	       mkLetIn (Name id, cb, cty, subfun (id::vl) spf)
	   | _ -> error "incomplete proof!")

    | Some (Prim (Cut (b,id,t)),[spf1;spf2]) ->
        let spf1, spf2 = if b then spf1, spf2 else spf2, spf1 in
	mkLetIn (Name id,subfun vl spf1,subst_vars vl t,subfun (id::vl) spf2)

    | Some (Prim (FixRule (f,n,others)),spfl) ->
	let all = Array.of_list ((f,n,cl)::others) in
	let lcty = Array.map (fun (_,_,ar) -> subst_vars vl ar) all in
	let names = Array.map (fun (f,_,_) -> Name f) all in
	let vn = Array.map (fun (_,n,_) -> n-1) all in
	let newvl = List.fold_left (fun vl (id,_,_)->(id::vl)) (f::vl)others in
	let lfix = Array.map (subfun newvl) (Array.of_list spfl) in
	mkFix ((vn,0),(names,lcty,lfix))	

    | Some (Prim (Cofix (f,others)),spfl) ->
	let all = Array.of_list ((f,cl)::others) in
	let lcty = Array.map (fun (_,ar) -> subst_vars vl ar) all in
	let names  = Array.map (fun (f,_) -> Name f) all in
	let newvl = List.fold_left (fun vl (id,_)->(id::vl)) (f::vl) others in 
	let lfix = Array.map (subfun newvl) (Array.of_list spfl) in
	mkCoFix (0,(names,lcty,lfix))
	  
    | Some (Prim (Refine c),spfl) ->
	let mvl = collect_meta_variables c in
	let metamap = List.combine mvl (List.map (subfun vl) spfl) in
	let cc = subst_vars vl c in 
	plain_instance metamap cc

    (* Structural and conversion rules do not produce any proof *)
    | Some (Prim (Convert_concl _),[pf]) ->
	subfun vl pf
	
    | Some (Prim (Convert_hyp _),[pf]) ->
	subfun vl pf

    | Some (Prim (Thin _),[pf]) ->
     (* No need to make ids Anonymous in vl: subst_vars take the more recent *)
	subfun vl pf
	
    | Some (Prim (ThinBody _),[pf]) ->
	subfun vl pf
	
    | Some (Prim (Move _),[pf]) ->
	subfun vl pf

    | Some (Prim (Rename (id1,id2)),[pf]) ->
	subfun (rebind id1 id2 vl) pf

    | Some _ -> anomaly "prim_extractor"

    | None-> error "prim_extractor handed incomplete proof"
	  
(* Pretty-printer *)

open Printer

let prterm x = prterm_env (Global.env()) x

let pr_prim_rule_v7 = function
  | Intro id -> 
      str"Intro " ++ pr_id id
	
  | Intro_replacing id -> 
      (str"intro replacing "  ++ pr_id id)
	
  | Cut (b,id,t) ->
      if b then
        (str"Assert " ++ prterm t)
      else
        (str"Cut " ++ prterm t ++ str ";[Intro " ++ pr_id id ++ str "|Idtac]")
	
  | FixRule (f,n,[]) ->
      (str"Fix " ++ pr_id f ++ str"/" ++ int n)
      
  | FixRule (f,n,others) -> 
      let rec print_mut = function
	| (f,n,ar)::oth -> 
           pr_id f ++ str"/" ++ int n ++ str" : " ++ prterm ar ++ print_mut oth
        | [] -> mt () in
      (str"Fix " ++ pr_id f ++ str"/" ++ int n ++
         str" with " ++ print_mut others)

  | Cofix (f,[]) ->
      (str"Cofix " ++ pr_id f)

  | Cofix (f,others) ->
      let rec print_mut = function
	| (f,ar)::oth ->
	  (pr_id f ++ str" : " ++ prterm ar ++ print_mut oth)
        | [] -> mt () in
      (str"Cofix " ++ pr_id f ++  str" with " ++ print_mut others)

  | Refine c -> 
      str(if occur_meta c then "Refine " else "Exact ") ++
      Constrextern.with_meta_as_hole prterm c
      
  | Convert_concl c ->
      (str"Change "  ++ prterm c)
      
  | Convert_hyp (id,None,t) ->
      (str"Change "  ++ prterm t  ++ spc ()  ++ str"in "  ++ pr_id id)

  | Convert_hyp (id,Some c,t) ->
      (str"Change "  ++ prterm c  ++ spc ()  ++ str"in "
       ++ pr_id id ++ str" (Type of "  ++ pr_id id ++ str ")")
      
  | Thin ids ->
      (str"Clear "  ++ prlist_with_sep pr_spc pr_id ids)
      
  | ThinBody ids ->
      (str"ClearBody "  ++ prlist_with_sep pr_spc pr_id ids)
      
  | Move (withdep,id1,id2) ->
      (str (if withdep then "Dependent " else "") ++
	 str"Move "  ++ pr_id id1 ++ str " after " ++ pr_id id2)

  | Rename (id1,id2) ->
      (str "Rename " ++ pr_id id1 ++ str " into " ++ pr_id id2)

let pr_prim_rule_v8 = function
  | Intro id -> 
      str"intro " ++ pr_id id
	
  | Intro_replacing id -> 
      (str"intro replacing "  ++ pr_id id)
	
  | Cut (b,id,t) ->
      if b then
        (str"assert " ++ prterm t)
      else
        (str"cut " ++ prterm t ++ str ";[intro " ++ pr_id id ++ str "|idtac]")
	
  | FixRule (f,n,[]) ->
      (str"fix " ++ pr_id f ++ str"/" ++ int n)
      
  | FixRule (f,n,others) -> 
      let rec print_mut = function
	| (f,n,ar)::oth -> 
           pr_id f ++ str"/" ++ int n ++ str" : " ++ prterm ar ++ print_mut oth
        | [] -> mt () in
      (str"fix " ++ pr_id f ++ str"/" ++ int n ++
         str" with " ++ print_mut others)

  | Cofix (f,[]) ->
      (str"cofix " ++ pr_id f)

  | Cofix (f,others) ->
      let rec print_mut = function
	| (f,ar)::oth ->
	  (pr_id f ++ str" : " ++ prterm ar ++ print_mut oth)
        | [] -> mt () in
      (str"cofix " ++ pr_id f ++  str" with " ++ print_mut others)

  | Refine c -> 
      str(if occur_meta c then "refine " else "exact ") ++
      Constrextern.with_meta_as_hole prterm c
      
  | Convert_concl c ->
      (str"change "  ++ prterm c)
      
  | Convert_hyp (id,None,t) ->
      (str"change "  ++ prterm t  ++ spc ()  ++ str"in "  ++ pr_id id)

  | Convert_hyp (id,Some c,t) ->
      (str"change "  ++ prterm c  ++ spc ()  ++ str"in "
       ++ pr_id id ++ str" (type of "  ++ pr_id id ++ str ")")
      
  | Thin ids ->
      (str"clear "  ++ prlist_with_sep pr_spc pr_id ids)
      
  | ThinBody ids ->
      (str"clearbody "  ++ prlist_with_sep pr_spc pr_id ids)
      
  | Move (withdep,id1,id2) ->
      (str (if withdep then "dependent " else "") ++
	 str"move "  ++ pr_id id1 ++ str " after " ++ pr_id id2)

  | Rename (id1,id2) ->
      (str "rename " ++ pr_id id1 ++ str " into " ++ pr_id id2)

let pr_prim_rule t =
  if! Options.v7 then pr_prim_rule_v7 t else pr_prim_rule_v8 t
