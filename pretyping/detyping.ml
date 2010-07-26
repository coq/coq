(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Pp
open Util
open Univ
open Names
open Term
open Declarations
open Inductive
open Inductiveops
open Environ
open Sign
open Rawterm
open Nameops
open Termops
open Namegen
open Libnames
open Nametab
open Evd
open Mod_subst

let dl = dummy_loc

(****************************************************************************)
(* Tools for printing of Cases                                              *)

let encode_inductive r =
  let indsp = global_inductive r in
  let constr_lengths = mis_constr_nargs indsp in
  (indsp,constr_lengths)

(* Parameterization of the translation from constr to ast      *)

(* Tables for Cases printing under a "if" form, a "let" form,  *)

let has_two_constructors lc =
  Array.length lc = 2 (* & lc.(0) = 0 & lc.(1) = 0 *)

let isomorphic_to_tuple lc = (Array.length lc = 1)

let encode_bool r =
  let (_,lc as x) = encode_inductive r in
  if not (has_two_constructors lc) then
    user_err_loc (loc_of_reference r,"encode_if",
      str "This type has not exactly two constructors.");
  x

let encode_tuple r =
  let (_,lc as x) = encode_inductive r in
  if not (isomorphic_to_tuple lc) then
    user_err_loc (loc_of_reference r,"encode_tuple",
      str "This type cannot be seen as a tuple type.");
  x

module PrintingCasesMake =
  functor (Test : sig
     val encode : reference -> inductive * int array
     val member_message : std_ppcmds -> bool -> std_ppcmds
     val field : string
     val title : string
  end) ->
  struct
    type t = inductive * int array
    let encode = Test.encode
    let subst subst ((kn,i), ints as obj) =
      let kn' = subst_ind subst kn in
	if kn' == kn then obj else
	  (kn',i), ints
    let printer (ind,_) = pr_global_env Idset.empty (IndRef ind)
    let key = ["Printing";Test.field]
    let title = Test.title
    let member_message x = Test.member_message (printer x)
    let synchronous = true
  end

module PrintingCasesIf =
  PrintingCasesMake (struct
    let encode = encode_bool
    let field = "If"
    let title = "Types leading to pretty-printing of Cases using a `if' form: "
    let member_message s b =
      str "Cases on elements of " ++ s ++
      str
	(if b then " are printed using a `if' form"
         else " are not printed using a `if' form")
  end)

module PrintingCasesLet =
  PrintingCasesMake (struct
    let encode = encode_tuple
    let field = "Let"
    let title =
      "Types leading to a pretty-printing of Cases using a `let' form:"
    let member_message s b =
      str "Cases on elements of " ++ s ++
      str
	(if b then " are printed using a `let' form"
         else " are not printed using a `let' form")
  end)

module PrintingIf  = Goptions.MakeRefTable(PrintingCasesIf)
module PrintingLet = Goptions.MakeRefTable(PrintingCasesLet)

(* Flags.for printing or not wildcard and synthetisable types *)

open Goptions

let wildcard_value = ref true
let force_wildcard () = !wildcard_value

let _ = declare_bool_option
	  { optsync  = true;
	    optname  = "forced wildcard";
	    optkey   = ["Printing";"Wildcard"];
	    optread  = force_wildcard;
	    optwrite = (:=) wildcard_value }

let synth_type_value = ref true
let synthetize_type () = !synth_type_value

let _ = declare_bool_option
	  { optsync  = true;
	    optname  = "pattern matching return type synthesizability";
	    optkey   = ["Printing";"Synth"];
	    optread  = synthetize_type;
	    optwrite = (:=) synth_type_value }

let reverse_matching_value = ref true
let reverse_matching () = !reverse_matching_value

let _ = declare_bool_option
	  { optsync  = true;
	    optname  = "pattern-matching reversibility";
	    optkey   = ["Printing";"Matching"];
	    optread  = reverse_matching;
	    optwrite = (:=) reverse_matching_value }

(* Auxiliary function for MutCase printing *)
(* [computable] tries to tell if the predicate typing the result is inferable*)

let computable p k =
    (* We first remove as many lambda as the arity, then we look
       if it remains a lambda for a dependent elimination. This function
       works for normal eta-expanded term. For non eta-expanded or
       non-normal terms, it may affirm the pred is synthetisable
       because of an undetected ultimate dependent variable in the second
       clause, or else, it may affirms the pred non synthetisable
       because of a non normal term in the fourth clause.
       A solution could be to store, in the MutCase, the eta-expanded
       normal form of pred to decide if it depends on its variables

       Lorsque le prédicat est dépendant de manière certaine, on
       ne déclare pas le prédicat synthétisable (même si la
       variable dépendante ne l'est pas effectivement) parce que
       sinon on perd la réciprocité de la synthèse (qui, lui,
       engendrera un prédicat non dépendant) *)

  let sign,ccl = decompose_lam_assum p in
  (rel_context_length sign = k+1)
  &&
  noccur_between 1 (k+1) ccl

let avoid_flag isgoal = if isgoal then Some true else None

let lookup_name_as_displayed env t s =
  let rec lookup avoid n c = match kind_of_term c with
    | Prod (name,_,c') ->
	(match compute_displayed_name_in RenamingForGoal avoid name c' with
           | (Name id,avoid') -> if id=s then Some n else lookup avoid' (n+1) c'
	   | (Anonymous,avoid') -> lookup avoid' (n+1) (pop c'))
    | LetIn (name,_,_,c') ->
	(match compute_displayed_name_in RenamingForGoal avoid name c' with
           | (Name id,avoid') -> if id=s then Some n else lookup avoid' (n+1) c'
	   | (Anonymous,avoid') -> lookup avoid' (n+1) (pop c'))
    | Cast (c,_,_) -> lookup avoid n c
    | _ -> None
  in lookup (ids_of_named_context (named_context env)) 1 t

let lookup_index_as_renamed env t n =
  let rec lookup n d c = match kind_of_term c with
    | Prod (name,_,c') ->
	  (match compute_displayed_name_in RenamingForGoal [] name c' with
               (Name _,_) -> lookup n (d+1) c'
             | (Anonymous,_) ->
		 if n=0 then
		   Some (d-1)
		 else if n=1 then
		   Some d
		 else
		   lookup (n-1) (d+1) c')
    | LetIn (name,_,_,c') ->
	  (match compute_displayed_name_in RenamingForGoal [] name c' with
             | (Name _,_) -> lookup n (d+1) c'
             | (Anonymous,_) ->
		 if n=0 then
		   Some (d-1)
		 else if n=1 then
		   Some d
		 else
		   lookup (n-1) (d+1) c'
	  )
    | Cast (c,_,_) -> lookup n d c
    | _ -> if n=0 then Some (d-1) else None
  in lookup n 1 t

(**********************************************************************)
(* Fragile algorithm to reverse pattern-matching compilation          *)

let update_name na ((_,e),c) =
  match na with
  | Name _ when force_wildcard () & noccurn (list_index na e) c ->
      Anonymous
  | _ ->
      na

let rec decomp_branch n nal b (avoid,env as e) c =
  let flag = if b then RenamingForGoal else RenamingForCasesPattern in
  if n=0 then (List.rev nal,(e,c))
  else
    let na,c,f =
      match kind_of_term (strip_outer_cast c) with
	| Lambda (na,_,c) -> na,c,compute_displayed_let_name_in
	| LetIn (na,_,_,c) -> na,c,compute_displayed_name_in
	| _ ->
	    Name (id_of_string "x"),(applist (lift 1 c, [mkRel 1])),
	    compute_displayed_name_in in
    let na',avoid' = f flag avoid na c in
    decomp_branch (n-1) (na'::nal) b (avoid',add_name na' env) c

let rec build_tree na isgoal e ci cl =
  let mkpat n rhs pl = PatCstr(dl,(ci.ci_ind,n+1),pl,update_name na rhs) in
  let cnl = ci.ci_cstr_nargs in
  List.flatten
    (list_tabulate (fun i -> contract_branch isgoal e (cnl.(i),mkpat i,cl.(i)))
       (Array.length cl))

and align_tree nal isgoal (e,c as rhs) = match nal with
  | [] -> [[],rhs]
  | na::nal ->
    match kind_of_term c with
    | Case (ci,p,c,cl) when c = mkRel (list_index na (snd e))
	& (* don't contract if p dependent *)
	computable p (ci.ci_pp_info.ind_nargs) ->
	let clauses = build_tree na isgoal e ci cl in
	List.flatten
          (List.map (fun (pat,rhs) ->
	      let lines = align_tree nal isgoal rhs in
	      List.map (fun (hd,rest) -> pat::hd,rest) lines)
	    clauses)
    | _ ->
	let pat = PatVar(dl,update_name na rhs) in
	let mat = align_tree nal isgoal rhs in
	List.map (fun (hd,rest) -> pat::hd,rest) mat

and contract_branch isgoal e (cn,mkpat,b) =
  let nal,rhs = decomp_branch cn [] isgoal e b in
  let mat = align_tree nal isgoal rhs in
  List.map (fun (hd,rhs) -> (mkpat rhs hd,rhs)) mat

(**********************************************************************)
(* Transform internal representation of pattern-matching into list of *)
(* clauses                                                            *)

let is_nondep_branch c n =
  try
    let sign,ccl = decompose_lam_n_assum n c in
    noccur_between 1 (rel_context_length sign) ccl
  with _ -> (* Not eta-expanded or not reduced *)
    false

let extract_nondep_branches test c b n =
  let rec strip n r = if n=0 then r else
    match r with
      | RLambda (_,_,_,_,t) -> strip (n-1) t
      | RLetIn (_,_,_,t) -> strip (n-1) t
      | _ -> assert false in
  if test c n then Some (strip n b) else None

let it_destRLambda_or_LetIn_names n c =
  let rec aux n nal c =
    if n=0 then (List.rev nal,c) else match c with
      | RLambda (_,na,_,_,c) -> aux (n-1) (na::nal) c
      | RLetIn (_,na,_,c) -> aux (n-1) (na::nal) c
      | _ ->
          (* eta-expansion *)
	  let rec next l =
	    let x = next_ident_away (id_of_string "x") l in
	    (* Not efficient but unusual and no function to get free rawvars *)
(* 	    if occur_rawconstr x c then next (x::l) else x in *)
	    x
	  in
	  let x = next (free_rawvars c) in
	  let a = RVar (dl,x) in
	  aux (n-1) (Name x :: nal)
            (match c with
              | RApp (loc,p,l) -> RApp (loc,c,l@[a])
              | _ -> (RApp (dl,c,[a])))
  in aux n [] c

let detype_case computable detype detype_eqns testdep avoid data p c bl =
  let (indsp,st,nparams,consnargsl,k) = data in
  let synth_type = synthetize_type () in
  let tomatch = detype c in
  let alias, aliastyp, pred=
    if (not !Flags.raw_print) & synth_type & computable & Array.length bl<>0
    then
      Anonymous, None, None
    else
      match Option.map detype p with
        | None -> Anonymous, None, None
        | Some p ->
            let nl,typ = it_destRLambda_or_LetIn_names k p in
	    let n,typ = match typ with
              | RLambda (_,x,_,t,c) -> x, c
	      | _ -> Anonymous, typ in
	    let aliastyp =
	      if List.for_all ((=) Anonymous) nl then None
	      else Some (dl,indsp,nparams,nl) in
            n, aliastyp, Some typ
  in
  let constructs = Array.init (Array.length bl) (fun i -> (indsp,i+1)) in
  let tag =
    try
      if !Flags.raw_print then
        RegularStyle
      else if st = LetPatternStyle then
	st
      else if PrintingLet.active (indsp,consnargsl) then
	LetStyle
      else if PrintingIf.active (indsp,consnargsl) then
	IfStyle
      else
	st
    with Not_found -> st
  in
  match tag with
  | LetStyle when aliastyp = None ->
      let bl' = Array.map detype bl in
      let (nal,d) = it_destRLambda_or_LetIn_names consnargsl.(0) bl'.(0) in
      RLetTuple (dl,nal,(alias,pred),tomatch,d)
  | IfStyle when aliastyp = None ->
      let bl' = Array.map detype bl in
      let nondepbrs =
	array_map3 (extract_nondep_branches testdep) bl bl' consnargsl in
      if array_for_all ((<>) None) nondepbrs then
	RIf (dl,tomatch,(alias,pred),
             Option.get nondepbrs.(0),Option.get nondepbrs.(1))
      else
	let eqnl = detype_eqns constructs consnargsl bl in
	RCases (dl,tag,pred,[tomatch,(alias,aliastyp)],eqnl)
  | _ ->
      let eqnl = detype_eqns constructs consnargsl bl in
      RCases (dl,tag,pred,[tomatch,(alias,aliastyp)],eqnl)

let detype_sort = function
  | Prop c -> RProp c
  | Type u -> RType (Some u)

type binder_kind = BProd | BLambda | BLetIn

(**********************************************************************)
(* Main detyping function                                             *)

let detype_anonymous = ref (fun loc n -> anomaly "detype: index to an anonymous variable")
let set_detype_anonymous f = detype_anonymous := f

let rec detype (isgoal:bool) avoid env t =
  match kind_of_term (collapse_appl t) with
    | Rel n ->
      (try match lookup_name_of_rel n env with
	 | Name id   -> RVar (dl, id)
	 | Anonymous -> !detype_anonymous dl n
       with Not_found ->
	 let s = "_UNBOUND_REL_"^(string_of_int n)
	 in RVar (dl, id_of_string s))
    | Meta n ->
	(* Meta in constr are not user-parsable and are mapped to Evar *)
	REvar (dl, n, None)
    | Var id ->
	(try
	  let _ = Global.lookup_named id in RRef (dl, VarRef id)
	 with _ ->
	  RVar (dl, id))
    | Sort s -> RSort (dl,detype_sort s)
    | Cast (c1,k,c2) ->
	RCast(dl,detype isgoal avoid env c1, CastConv (k, detype isgoal avoid env c2))
    | Prod (na,ty,c) -> detype_binder isgoal BProd avoid env na ty c
    | Lambda (na,ty,c) -> detype_binder isgoal BLambda avoid env na ty c
    | LetIn (na,b,_,c) -> detype_binder isgoal BLetIn avoid env na b c
    | App (f,args) ->
	RApp (dl,detype isgoal avoid env f,
              array_map_to_list (detype isgoal avoid env) args)
    | Const sp -> RRef (dl, ConstRef sp)
    | Evar (ev,cl) ->
        REvar (dl, ev,
               Some (List.map (detype isgoal avoid env) (Array.to_list cl)))
    | Ind ind_sp ->
	RRef (dl, IndRef ind_sp)
    | Construct cstr_sp ->
	RRef (dl, ConstructRef cstr_sp)
    | Case (ci,p,c,bl) ->
	let comp = computable p (ci.ci_pp_info.ind_nargs) in
	detype_case comp (detype isgoal avoid env)
	  (detype_eqns isgoal avoid env ci comp)
	  is_nondep_branch avoid
	  (ci.ci_ind,ci.ci_pp_info.style,ci.ci_npar,
	   ci.ci_cstr_nargs,ci.ci_pp_info.ind_nargs)
	  (Some p) c bl
    | Fix (nvn,recdef) -> detype_fix isgoal avoid env nvn recdef
    | CoFix (n,recdef) -> detype_cofix isgoal avoid env n recdef

and detype_fix isgoal avoid env (vn,_ as nvn) (names,tys,bodies) =
  let def_avoid, def_env, lfi =
    Array.fold_left
      (fun (avoid, env, l) na ->
	 let id = next_name_away na avoid in
	 (id::avoid, add_name (Name id) env, id::l))
      (avoid, env, []) names in
  let n = Array.length tys in
  let v = array_map3
    (fun c t i -> share_names isgoal (i+1) [] def_avoid def_env c (lift n t))
    bodies tys vn in
  RRec(dl,RFix (Array.map (fun i -> Some i, RStructRec) (fst nvn), snd nvn),Array.of_list (List.rev lfi),
       Array.map (fun (bl,_,_) -> bl) v,
       Array.map (fun (_,_,ty) -> ty) v,
       Array.map (fun (_,bd,_) -> bd) v)

and detype_cofix isgoal avoid env n (names,tys,bodies) =
  let def_avoid, def_env, lfi =
    Array.fold_left
      (fun (avoid, env, l) na ->
	 let id = next_name_away na avoid in
	 (id::avoid, add_name (Name id) env, id::l))
      (avoid, env, []) names in
  let ntys = Array.length tys in
  let v = array_map2
    (fun c t -> share_names isgoal 0 [] def_avoid def_env c (lift ntys t))
    bodies tys in
  RRec(dl,RCoFix n,Array.of_list (List.rev lfi),
       Array.map (fun (bl,_,_) -> bl) v,
       Array.map (fun (_,_,ty) -> ty) v,
       Array.map (fun (_,bd,_) -> bd) v)

and share_names isgoal n l avoid env c t =
  match kind_of_term c, kind_of_term t with
    (* factorize even when not necessary to have better presentation *)
    | Lambda (na,t,c), Prod (na',t',c') ->
        let na = match (na,na') with
            Name _, _ -> na
          | _, Name _ -> na'
          | _ -> na in
        let t = detype isgoal avoid env t in
	let id = next_name_away na avoid in
        let avoid = id::avoid and env = add_name (Name id) env in
        share_names isgoal (n-1) ((Name id,Explicit,None,t)::l) avoid env c c'
    (* May occur for fix built interactively *)
    | LetIn (na,b,t',c), _ when n > 0 ->
        let t' = detype isgoal avoid env t' in
        let b = detype isgoal avoid env b in
	let id = next_name_away na avoid in
        let avoid = id::avoid and env = add_name (Name id) env in
        share_names isgoal n ((Name id,Explicit,Some b,t')::l) avoid env c t
    (* Only if built with the f/n notation or w/o let-expansion in types *)
    | _, LetIn (_,b,_,t) when n > 0 ->
	share_names isgoal n l avoid env c (subst1 b t)
    (* If it is an open proof: we cheat and eta-expand *)
    | _, Prod (na',t',c') when n > 0 ->
        let t' = detype isgoal avoid env t' in
	let id = next_name_away na' avoid in
        let avoid = id::avoid and env = add_name (Name id) env in
        let appc = mkApp (lift 1 c,[|mkRel 1|]) in
        share_names isgoal (n-1) ((Name id,Explicit,None,t')::l) avoid env appc c'
    (* If built with the f/n notation: we renounce to share names *)
    | _ ->
        if n>0 then warning "Detyping.detype: cannot factorize fix enough";
        let c = detype isgoal avoid env c in
        let t = detype isgoal avoid env t in
        (List.rev l,c,t)

and detype_eqns isgoal avoid env ci computable constructs consnargsl bl =
  try
    if !Flags.raw_print or not (reverse_matching ()) then raise Exit;
    let mat = build_tree Anonymous isgoal (avoid,env) ci bl in
    List.map (fun (pat,((avoid,env),c)) -> (dl,[],[pat],detype isgoal avoid env c))
      mat
  with _ ->
    Array.to_list
      (array_map3 (detype_eqn isgoal avoid env) constructs consnargsl bl)

and detype_eqn isgoal avoid env constr construct_nargs branch =
  let make_pat x avoid env b ids =
    if force_wildcard () & noccurn 1 b then
      PatVar (dl,Anonymous),avoid,(add_name Anonymous env),ids
    else
      let id = next_name_away_in_cases_pattern x avoid in
      PatVar (dl,Name id),id::avoid,(add_name (Name id) env),id::ids
  in
  let rec buildrec ids patlist avoid env n b =
    if n=0 then
      (dl, ids,
       [PatCstr(dl, constr, List.rev patlist,Anonymous)],
       detype isgoal avoid env b)
    else
      match kind_of_term b with
	| Lambda (x,_,b) ->
	    let pat,new_avoid,new_env,new_ids = make_pat x avoid env b ids in
            buildrec new_ids (pat::patlist) new_avoid new_env (n-1) b

	| LetIn (x,_,_,b) ->
	    let pat,new_avoid,new_env,new_ids = make_pat x avoid env b ids in
            buildrec new_ids (pat::patlist) new_avoid new_env (n-1) b

	| Cast (c,_,_) ->    (* Oui, il y a parfois des cast *)
	    buildrec ids patlist avoid env n c

	| _ -> (* eta-expansion : n'arrivera plus lorsque tous les
                  termes seront construits à partir de la syntaxe Cases *)
            (* nommage de la nouvelle variable *)
	    let new_b = applist (lift 1 b, [mkRel 1]) in
            let pat,new_avoid,new_env,new_ids =
	      make_pat Anonymous avoid env new_b ids in
	    buildrec new_ids (pat::patlist) new_avoid new_env (n-1) new_b

  in
  buildrec [] [] avoid env construct_nargs branch

and detype_binder isgoal bk avoid env na ty c =
  let flag = if isgoal then RenamingForGoal else (RenamingElsewhereFor c) in
  let na',avoid' =
    if bk = BLetIn then compute_displayed_let_name_in flag avoid na c
    else compute_displayed_name_in flag avoid na c in
  let r =  detype isgoal avoid' (add_name na' env) c in
  match bk with
  | BProd -> RProd (dl, na',Explicit,detype false avoid env ty, r)
  | BLambda -> RLambda (dl, na',Explicit,detype false avoid env ty, r)
  | BLetIn -> RLetIn (dl, na',detype false avoid env ty, r)

let rec detype_rel_context where avoid env sign =
  let where = Option.map (fun c -> it_mkLambda_or_LetIn c sign) where in
  let rec aux avoid env = function
  | [] -> []
  | (na,b,t)::rest ->
      let na',avoid' =
	match where with
	| None -> na,avoid
	| Some c ->
	    if b<>None then
	      compute_displayed_let_name_in (RenamingElsewhereFor c) avoid na c
	    else
	      compute_displayed_name_in (RenamingElsewhereFor c) avoid na c in
      let b = Option.map (detype false avoid env) b in
      let t = detype false avoid env t in
      (na',Explicit,b,t) :: aux avoid' (add_name na' env) rest
  in aux avoid env (List.rev sign)

(**********************************************************************)
(* Module substitution: relies on detyping                            *)

let rec subst_cases_pattern subst pat =
  match pat with
  | PatVar _ -> pat
  | PatCstr (loc,((kn,i),j),cpl,n) ->
      let kn' = subst_ind subst kn
      and cpl' = list_smartmap (subst_cases_pattern subst) cpl in
	if kn' == kn && cpl' == cpl then pat else
	  PatCstr (loc,((kn',i),j),cpl',n)

let rec subst_rawconstr subst raw =
  match raw with
  | RRef (loc,ref) ->
      let ref',t = subst_global subst ref in
	if ref' == ref then raw else
         detype false [] [] t

  | RVar _ -> raw
  | REvar _ -> raw
  | RPatVar _ -> raw

  | RApp (loc,r,rl) ->
      let r' = subst_rawconstr subst r
      and rl' = list_smartmap (subst_rawconstr subst) rl in
	if r' == r && rl' == rl then raw else
	  RApp(loc,r',rl')

  | RLambda (loc,n,bk,r1,r2) ->
      let r1' = subst_rawconstr subst r1 and r2' = subst_rawconstr subst r2 in
	if r1' == r1 && r2' == r2 then raw else
	  RLambda (loc,n,bk,r1',r2')

  | RProd (loc,n,bk,r1,r2) ->
      let r1' = subst_rawconstr subst r1 and r2' = subst_rawconstr subst r2 in
	if r1' == r1 && r2' == r2 then raw else
	  RProd (loc,n,bk,r1',r2')

  | RLetIn (loc,n,r1,r2) ->
      let r1' = subst_rawconstr subst r1 and r2' = subst_rawconstr subst r2 in
	if r1' == r1 && r2' == r2 then raw else
	  RLetIn (loc,n,r1',r2')

  | RCases (loc,sty,rtno,rl,branches) ->
      let rtno' = Option.smartmap (subst_rawconstr subst) rtno
      and rl' = list_smartmap (fun (a,x as y) ->
        let a' = subst_rawconstr subst a in
        let (n,topt) = x in
        let topt' = Option.smartmap
          (fun (loc,(sp,i),x,y as t) ->
            let sp' = subst_ind subst sp in
            if sp == sp' then t else (loc,(sp',i),x,y)) topt in
        if a == a' && topt == topt' then y else (a',(n,topt'))) rl
      and branches' = list_smartmap
			(fun (loc,idl,cpl,r as branch) ->
			   let cpl' =
			     list_smartmap (subst_cases_pattern subst) cpl
			   and r' = subst_rawconstr subst r in
			     if cpl' == cpl && r' == r then branch else
			       (loc,idl,cpl',r'))
			branches
      in
	if rtno' == rtno && rl' == rl && branches' == branches then raw else
	  RCases (loc,sty,rtno',rl',branches')

  | RLetTuple (loc,nal,(na,po),b,c) ->
      let po' = Option.smartmap (subst_rawconstr subst) po
      and b' = subst_rawconstr subst b
      and c' = subst_rawconstr subst c in
	if po' == po && b' == b && c' == c then raw else
          RLetTuple (loc,nal,(na,po'),b',c')

  | RIf (loc,c,(na,po),b1,b2) ->
      let po' = Option.smartmap (subst_rawconstr subst) po
      and b1' = subst_rawconstr subst b1
      and b2' = subst_rawconstr subst b2
      and c' = subst_rawconstr subst c in
	if c' == c & po' == po && b1' == b1 && b2' == b2 then raw else
          RIf (loc,c',(na,po'),b1',b2')

  | RRec (loc,fix,ida,bl,ra1,ra2) ->
      let ra1' = array_smartmap (subst_rawconstr subst) ra1
      and ra2' = array_smartmap (subst_rawconstr subst) ra2 in
      let bl' = array_smartmap
        (list_smartmap (fun (na,k,obd,ty as dcl) ->
          let ty' = subst_rawconstr subst ty in
          let obd' = Option.smartmap (subst_rawconstr subst) obd in
          if ty'==ty & obd'==obd then dcl else (na,k,obd',ty')))
        bl in
	if ra1' == ra1 && ra2' == ra2 && bl'==bl then raw else
	  RRec (loc,fix,ida,bl',ra1',ra2')

  | RSort _ -> raw

  | RHole (loc,ImplicitArg (ref,i,b)) ->
      let ref',_ = subst_global subst ref in
	if ref' == ref then raw else
	  RHole (loc,InternalHole)
  | RHole (loc, (BinderType _ | QuestionMark _ | CasesType | InternalHole |
      TomatchTypeParameter _ | GoalEvar | ImpossibleCase | MatchingVar _)) ->
      raw

  | RCast (loc,r1,k) ->
      (match k with
	   CastConv (k,r2) ->
	     let r1' = subst_rawconstr subst r1 and r2' = subst_rawconstr subst r2 in
	       if r1' == r1 && r2' == r2 then raw else
		 RCast (loc,r1', CastConv (k,r2'))
	 | CastCoerce ->
	     let r1' = subst_rawconstr subst r1 in
	       if r1' == r1 then raw else RCast (loc,r1',k))
  | RDynamic _ -> raw

(* Utilities to transform kernel cases to simple pattern-matching problem *)

let simple_cases_matrix_of_branches ind brns brs =
  list_map2_i (fun i n b ->
      let nal,c = it_destRLambda_or_LetIn_names n b in
      let mkPatVar na = PatVar (dummy_loc,na) in
      let p = PatCstr (dummy_loc,(ind,i+1),List.map mkPatVar nal,Anonymous) in
      let ids = map_succeed Nameops.out_name nal in
      (dummy_loc,ids,[p],c))
    0 brns brs

let return_type_of_predicate ind nparams nrealargs_ctxt pred =
  let nal,p = it_destRLambda_or_LetIn_names (nrealargs_ctxt+1) pred in
  (List.hd nal, Some (dummy_loc, ind, nparams, List.tl nal)), Some p
