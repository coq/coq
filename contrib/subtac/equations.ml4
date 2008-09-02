(* -*- compile-command: "make -C ../.. bin/coqtop.byte" -*- *)
(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4deps: "parsing/grammar.cma" i*)
(*i camlp4use: "pa_extend.cmo" i*) 

(* $Id: subtac_cases.ml 11198 2008-07-01 17:03:43Z msozeau $ *)

open Cases
open Util
open Names
open Nameops
open Term
open Termops
open Declarations
open Inductiveops
open Environ
open Sign
open Reductionops
open Typeops
open Type_errors

open Rawterm
open Retyping
open Pretype_errors
open Evarutil
open Evarconv
open List
open Libnames

type pat =
  | PRel of int
  | PCstr of constructor * pat list
  | PInnac of constr
      
let rec constr_of_pat = function
  | PRel i -> mkRel i
  | PCstr (c, p) -> 
      let c' = mkConstruct c in
	mkApp (c', Array.of_list (constrs_of_pats p))
  | PInnac r -> r
      
and constrs_of_pats l = map constr_of_pat l

let rec pat_vars = function
  | PRel i -> Intset.singleton i
  | PCstr (c, p) -> pats_vars p
  | PInnac _ -> Intset.empty

and pats_vars l = 
  fold_left (fun vars p -> 
    let pvars = pat_vars p in
    let inter = Intset.inter pvars vars in
      if inter = Intset.empty then
	Intset.union pvars vars
      else error ("Non-linear pattern: variable " ^
		     string_of_int (Intset.choose inter) ^ " appears twice"))
    Intset.empty l

let rec pats_of_constrs l = map pat_of_constr l
and pat_of_constr c = 
  match kind_of_term c with
  | Rel i -> PRel i
  | App (f, args) when isConstruct f -> 
      PCstr (destConstruct f, pats_of_constrs (Array.to_list args))
  | Construct f -> PCstr (f, [])
  | _ -> PInnac c

let innacs_of_constrs l = map (fun x -> PInnac x) l

exception Conflict

let rec pmatch p c =
  match p, kind_of_term c with
  | PRel i, t -> [i, c]
  | PCstr (c, pl), App (c', l') when kind_of_term c' = Construct c -> 
      pmatches pl (Array.to_list l')
  | PCstr (c, []), Construct c' when c' = c -> []
  | PInnac _, _ -> []
  | _, _ -> raise Conflict

and pmatches pl l =
  match pl, l with
  | [], [] -> []
  | hd :: tl, hd' :: tl' -> pmatch hd hd' @ pmatches tl tl'
  | _ -> raise Conflict

let pattern_matches pl l = pmatches pl l

(** Specialize by a substitution. *)

let subst_tele s = replace_vars (List.map (fun (id, _, t) -> id, t) s)

let subst_rel_subst k s c = 
  let rec aux depth c =
    match kind_of_term c with
    | Rel n -> 
	let k = n - depth in 
	  if k >= 0 then 
	    try lift depth (assoc k s) 
	    with Not_found -> c
	  else c
    | _ -> map_constr_with_binders succ aux depth c
  in aux k c
    
let subst_context s ctx =
  let (_, ctx') = fold_right 
    (fun (id, b, t) (k, ctx') ->
      (succ k, (id, Option.map (subst_rel_subst k s) b, subst_rel_subst k s t) :: ctx'))
    ctx (0, [])
  in ctx'

let subst_rel_context k cstr ctx = 
  let (_, ctx') = fold_right 
    (fun (id, b, t) (k, ctx') ->
      (succ k, (id, Option.map (substnl [cstr] k) b, substnl [cstr] k t) :: ctx'))
    ctx (k, [])
  in ctx'

let rec lift_pat n k p = 
  match p with
  | PRel i ->
      if i >= k then PRel (i + n)
      else p
  | PCstr(c, pl) -> PCstr (c, lift_pats n k pl)
  | PInnac r -> PInnac (liftn n k r)
      
and lift_pats n k = map (lift_pat n k)

let rec subst_pat k t p = 
  match p with
  | PRel i -> 
      if i = k then t
      else if i > k then PRel (pred i)
      else p
  | PCstr(c, pl) ->
      PCstr (c, subst_pats k t pl)
  | PInnac r -> PInnac (substnl [constr_of_pat t] k r)

and subst_pats k t = map (subst_pat k t)

let rec specialize s p = 
  match p with
  | PRel i -> 
      if mem_assoc i s then PInnac (assoc i s)
      else p
  | PCstr(c, pl) ->
      PCstr (c, specialize_pats s pl)
  | PInnac r -> PInnac (specialize_constr s r)

and specialize_constr s c = subst_rel_subst 0 s c
and specialize_pats s = map (specialize s)

let lift_contextn n k sign =
  let rec liftrec k = function
    | (na,c,t)::sign ->
	(na,Option.map (liftn n k) c,liftn n k t)::(liftrec (k-1) sign)
    | [] -> []
  in
  liftrec (rel_context_length sign + k) sign

type program = 
  signature * clause list

and signature = identifier * rel_context * constr

and clause = rel_context * constr list * (constr, identifier located) rhs

and lhs = pat list

and ('a, 'b) rhs = 
  | Program of 'a
  | Empty of 'b

type splitting = 
  | Compute of rel_context * lhs * (constr, int) rhs
  | Split of rel_context * lhs * int * inductive_family *
      unification_result array * splitting option array

and unification_result = 
  rel_context * rel_context * constr * pat * substitution option

and substitution = (int * constr) list

type problem = rel_context * identifier * pat list

(* let vars_of_tele = map (fun (id, _, _) -> mkVar id) *)

let rels_of_tele tele = rel_list 0 (List.length tele)

let patvars_of_tele tele = map (fun c -> PRel (destRel c)) (rels_of_tele tele)

let split_solves split (delta, id, pats) =
  match split with
  | Compute (ctx, lhs, rhs) -> delta = ctx && pats = lhs
  | Split (ctx, lhs, id, indf, us, ls) -> delta = ctx && pats = lhs

let ids_of_constr c = 
  let rec aux vars c = 
    match kind_of_term c with
    | Var id -> Idset.add id vars
    | _ -> fold_constr aux vars c
  in aux Idset.empty c

let ids_of_constrs = 
  fold_left (fun acc x -> Idset.union (ids_of_constr x) acc) Idset.empty

let idset_of_list =
  fold_left (fun s x -> Idset.add x s) Idset.empty

let intset_of_list =
  fold_left (fun s x -> Intset.add x s) Intset.empty

let solves split (delta, id, pats as prob) = 
  split_solves split prob && 
  Intset.equal (pats_vars pats) (intset_of_list (map destRel (rels_of_tele delta)))

let check_judgment ctx c t =
  ignore(Typing.check (push_rel_context ctx (Global.env ())) Evd.empty c t); true

let check_context env ctx =
  fold_right
    (fun (_, _, t as decl) env -> 
      ignore(Typing.sort_of env Evd.empty t); push_rel decl env)
    ctx env

let split_context n c =
  let after, before = list_chop n c in
    match before with
    | hd :: tl -> after, hd, tl
    | [] -> raise (Invalid_argument "split_context")
	
let split_tele n ctx =
  let rec aux after n l =
    match n, l with
    | 0, decl :: before -> before, decl, List.rev after
    | n, decl :: before -> aux (decl :: after) (pred n) before
    | _ -> raise (Invalid_argument "split_tele")
  in aux [] n ctx

let add_var_subst subst n c =
  if mem_assoc n subst then 
    if eq_constr (assoc n subst) c then subst
    else raise Conflict
  else (n, c) :: subst
    
let rec unify env subst x y =
  match kind_of_term x, kind_of_term y with
  | Rel n, _ -> add_var_subst subst n y
  | _, Rel n -> add_var_subst subst n x
  | App (c, l), App (c', l') when eq_constr c c' ->
      unify_constrs env subst (Array.to_list l) (Array.to_list l')
  | _, _ -> if eq_constr x y then subst else raise Conflict

and unify_constrs env subst l l' = 
  if List.length l = List.length l' then
    fold_left2 (unify env) subst l l'
  else raise Conflict

let substituted_context subst ctx =
  let substitute_in_ctx n c ctx =
    let rec aux k after = function
      | [] -> assert false
      | decl :: before -> 
	  if k = n then subst_rel_context 0 c (rev after) @ before
	  else aux (succ k) (decl :: after) before
    in aux 1 [] ctx
  in
  let substitute_in_subst n c s =
    map (fun (k', c') ->
      let k' = if k' < n then k' else pred k' in
	(k', substnl [c] (pred n) c'))
      s
  in
  let recsubst = Array.of_list (list_map_i (fun i _ -> mkRel i) 1 ctx) in
  let record_subst k t =
    Array.iteri (fun i c ->
      if i < k then recsubst.(i) <- substnl [t] (succ (k - i)) c
      else if i = k then recsubst.(i) <- t
      else recsubst.(i) <- lift (-1) c)
      recsubst
  in
  let rec aux ctx' = function
    | [] -> ctx'
    | (k, t) :: rest ->
	let t' = lift (-k) t in (* caution, not always well defined *)
	let ctx' = substitute_in_ctx k t' ctx' in
	let rest' = substitute_in_subst k t' rest in
	  record_subst (pred k) (lift (-1) t);
	  aux ctx' rest'
  in
  let ctx' = aux ctx subst in
    filter (fun (i, c) -> if isRel c then i <> destRel c else true)
      (Array.to_list (Array.mapi (fun i x -> (succ i, x)) recsubst)), ctx'
    
let unify_type before ty =
  try
    let envb = push_rel_context before (Global.env()) in
    let IndType (indf, args) = find_rectype envb Evd.empty ty in
    let ind, params = dest_ind_family indf in
(*     let vs = params @ args in *)
    let vs = args in
    let cstrs = Inductiveops.arities_of_constructors envb ind in
    let cstrs = 
      Array.mapi (fun i ty ->
	let ty = prod_applist ty params in
	let ctx, ty = decompose_prod_assum ty in
	let env' = push_rel_context ctx (Global.env ()) in
	let IndType (indf, args) = find_rectype env' Evd.empty ty in
	let ind, params = dest_ind_family indf in
	let constr = applist (mkConstruct (ind, succ i), params @ rels_of_tele ctx) in
	let constrpat = PCstr ((ind, succ i), innacs_of_constrs params @ patvars_of_tele ctx) in
	  env', ctx, constr, constrpat, (* params @  *)args)
	cstrs
    in
      Array.map (fun (env', ctxc, c, cpat, us) -> 
	let beforelen = length before and ctxclen = length ctxc in
	let fullctx = (* lift_contextn beforelen 1  *)ctxc @ before in
(* 	let c = liftn beforelen (succ ctxclen) c and cpat = lift_pat beforelen ctxclen cpat in *)
	  try
	    let fullenv = push_rel_context fullctx (Global.env ()) in
	    let vs' = map (lift ctxclen) vs 
	    and us' = map (liftn beforelen (succ ctxclen)) us in
	    let subst = unify_constrs fullenv [] us' vs' in
	    let subst', ctx' = substituted_context subst fullctx in
	      (ctx', ctxc, c, cpat, Some subst')
	  with Conflict -> 
	    (fullctx, ctxc, c, cpat, None)) cstrs, indf
  with Not_found -> (* not an inductive type *)
    raise (Invalid_argument "unify_type: Not an inductive type")

let rec id_of_rel n l =
  match n, l with
  | 0, (Name id, _, _) :: tl -> id
  | n, _ :: tl -> id_of_rel (pred n) tl
  | _, _ -> raise (Invalid_argument "id_of_rel")
      
let rec valid_splitting (f, delta, t, pats) tree = 
  split_solves tree (delta, f, pats) && 
    valid_splitting_tree (f, delta, t) tree
    
and valid_splitting_tree (f, delta, t) = function
  | Compute (ctx, lhs, Program rhs) -> 
      let subst = constrs_of_pats lhs in 
	ignore(check_judgment ctx rhs (substl subst t)); true

  | Compute (ctx, lhs, Empty split) -> 
      let before, (x, _, ty), after = split_context split ctx in
      let unify, _ = unify_type before ty in
	array_for_all (fun (_, _, _, _, x) -> x = None) unify
	  
  | Split (ctx, lhs, rel, indf, unifs, ls) -> 
      let before, (id, _, ty), after = split_tele (pred rel) ctx in
      let unify, indf' = unify_type before ty in
	assert(indf = indf');
	if not (array_exists (fun (_, _, _, _, x) -> x <> None) unify) then false
	else
	  let ok, splits = 
	    Array.fold_left (fun (ok, splits as acc) (ctx', ctxc, cstr, cstrpat, subst) -> 
	      match subst with
	      | None -> acc
	      | Some subst ->
(* 		  let env' = push_rel_context ctx' (Global.env ()) in *)
(* 		  let ctx_correct =  *)
(* 		    ignore(check_context env' (subst_context subst ctxc)); *)
(* 		    ignore(check_context env' (subst_context subst before)); *)
(* 		    true *)
(* 		  in  *)
		  let newdelta = 
		    subst_context subst (subst_rel_context 0 cstr 
					    (lift_contextn (length ctxc) 0 after)) @ before in
		  let liftpats = lift_pats (length ctxc) rel lhs in
		  let newpats = specialize_pats subst (subst_pats rel cstrpat liftpats) in
		    (ok, (f, newdelta, newpats) :: splits))
	      (true, []) unify
	  in
	  let subst = List.map2 (fun (id, _, _) x -> out_name id, x) delta (constrs_of_pats lhs) in
	  let t' = replace_vars subst t in
	    ok && for_all 
	      (fun (f, delta', pats') -> 
		array_exists (function None -> false | Some tree -> valid_splitting (f, delta', t', pats') tree) ls) splits
	      
let valid_tree (f, delta, t) tree = 
  valid_splitting (f, delta, t, patvars_of_tele delta) tree

let find_split curpats patcs =
  let rec find_split_pat curpat patc =
    match kind_of_term patc with
    | Rel _ -> (* The pattern's a variable, don't split *) None
    | App (f, args) when isConstruct f ->
	let f = destConstruct f in
	  (match curpat with
	  | PCstr (f', args') when f = f' -> (* Already split at this level, continue *)
	      find_split_pats args' (Array.to_list args)
	  | PRel i -> (* Split on i *) Some i
	  | _ -> None)
    | Construct f ->
	(match curpat with
	| PCstr (f', []) when f = f' -> (* Already split at this level, no args *) None
	| PRel i -> (* Split on i *) Some i
	| _ -> None)
    | _ -> None

  and find_split_pats curpats patcs =
    assert(List.length curpats = List.length patcs);
    fold_left2 (fun acc -> 
      match acc with
      | None -> find_split_pat | _ -> fun _ _ -> acc)
      None curpats patcs
  in find_split_pats curpats patcs
      
open Pp
open Termops

let pr_constr_pat env c =
  let pr = print_constr_env env c in
    match kind_of_term c with
    | App _ -> str "(" ++ pr ++ str ")"
    | _ -> pr

let pr_clause env (delta, patcs, rhs) =
  let env = push_rel_context delta env in
    prlist_with_sep spc (pr_constr_pat env) patcs 

let pr_clauses env =
  prlist_with_sep fnl (pr_clause env)

let rec split_on env fdt var delta curpats clauses =
  let before, (id, _, ty), after = split_tele (pred var) delta in
  let unify, indf = unify_type before ty in
  let clauses = ref clauses in
  let splits = 
    Array.map (fun (ctx', ctxc, cstr, cstrpat, s) ->
      match s with
      | None -> None
      | Some s -> 
	  (* ctx' |- s cstr, s cstrpat *)
	  let newdelta =
	    subst_context s (subst_rel_context 0 cstr 
				(lift_contextn (length ctxc) 1 after)) @ ctx' in
	  let liftpats = 
	    (* delta |- curpats -> before; ctxc; id; after |- liftpats *)
	    lift_pats (length ctxc) (succ var) curpats 
	  in
	  let liftpat = (* before; ctxc |- cstrpat -> before; ctxc; after |- liftpat *)
	    lift_pat (pred var) 1 cstrpat
	  in
	  let substpat = (* before; ctxc; after |- liftpats[id:=liftpat] *)
	    subst_pats var liftpat liftpats 
	  in
	  let lifts = (* before; ctxc |- s : newdelta ->
			 before; ctxc; after |- lifts : newdelta ; after *)
	    map (fun (k,x) -> (pred var + k, lift (pred var) x)) s
	  in
	  let newpats = specialize_pats lifts substpat in
	  let matching, rest = partition (fun (delta', patcs, rhs) ->
	    try ignore(pattern_matches newpats patcs); true with Conflict -> false)
	    !clauses
	  in
	    clauses := rest;
	    if matching = [] then (
	      (* Try finding a splittable variable *)
	      let (id, _) = 
		fold_right (fun (id, _, ty as decl) (accid, ctx) -> 
		  match accid with 
		  | Some _ -> (accid, ctx)
		  | None -> 
		      let unify, indf = unify_type ctx ty in
			if array_for_all (fun (_, _, _, _, x) -> x = None) unify then
			  (Some id, ctx)
			else (None, decl :: ctx))
		  newdelta (None, [])
	      in 
		match id with
		| None ->
		    errorlabstrm "deppat"
	      	      (str "Non-exhaustive pattern-matching, no clause found for:" ++ fnl () ++
	      		  pr_clause env (newdelta, constrs_of_pats newpats, Empty var))
		| Some id -> 
		    Some (Compute (newdelta, newpats, 
				  Empty (fst (lookup_rel_id (out_name id) newdelta))))
	    ) else (
	      let splitting = make_split_aux env fdt newdelta newpats matching in
		Some splitting))
      unify
  in
    assert(!clauses = []);
    Split (delta, curpats, var, indf, unify, splits)
      
and make_split_aux env (f, d, t as fdt) delta curpats clauses =
  match clauses with
  (delta', patcs, rhs) :: clauses' ->
    (match find_split curpats patcs with
    | None -> (* No need to split anymore *)
	let res = Compute (delta', pats_of_constrs patcs, rhs) in
	  if clauses' <> [] then 
	    errorlabstrm "make_split_aux"
	      (str "Overlapping clauses:" ++ fnl () ++ pr_clauses env clauses)
	  else res
    | Some var -> split_on env fdt var delta curpats clauses)
  | [] -> error "No clauses left"

let make_split env (f, delta, t) clauses =
  make_split_aux env (f, delta, t) delta (patvars_of_tele delta) clauses
    
open Evd
open Evarutil

let lift_substitution n s = map (fun (k, x) -> (k + n, x)) s
let map_substitution s t = map (subst_rel_subst 0 s) t

let term_of_tree isevar env (i, delta, ty) tree =
  let rec aux = function
    | Compute (ctx, lhs, Program rhs) -> 
	let ty' = substl (rev (constrs_of_pats lhs)) ty in
	let body = it_mkLambda_or_LetIn rhs ctx and typ = it_mkProd_or_LetIn ty' ctx in
	  mkCast(body, DEFAULTcast, typ), typ

    | Compute (ctx, lhs, Empty split) ->
	let ty' = substl (rev (constrs_of_pats lhs)) ty in
	let split = (Name (id_of_string "split"), 
		    Some (Class_tactics.coq_nat_of_int (1 + (length ctx - split))),
		    Lazy.force Class_tactics.coq_nat)
	in
	let ty' = it_mkProd_or_LetIn ty' ctx in
	let let_ty' = mkLambda_or_LetIn split (lift 1 ty') in
	let term = e_new_evar isevar env ~src:(dummy_loc, QuestionMark true) let_ty' in
	  term, ty'
	    
    | Split (ctx, lhs, rel, indf, unif, sp) -> 
	let before, decl, after = split_tele (pred rel) ctx in
	let ty' = substl (rev (constrs_of_pats lhs)) ty in
	let branches = 
	  array_map2 (fun (ctx', ctxc, cstr, cstrpat, subst) split -> 
	    match split with
	    | Some s -> aux s
	    | None -> 
		(* dead code, inversion will find a proof of False by splitting on the rel'th hyp *)
		Class_tactics.coq_nat_of_int rel, Lazy.force Class_tactics.coq_nat)
	    unif sp 
	in
	let branches_ctx =
	  Array.mapi (fun i (br, brt) -> (id_of_string ("m_" ^ string_of_int i), Some br, brt))
	    branches
	in
	let n, branches_lets = 
	  Array.fold_left (fun (n, lets) (id, b, t) -> 
	    (succ n, (Name id, Option.map (lift n) b, lift n t) :: lets))
	    (0, []) branches_ctx
	in
	let liftctx = lift_contextn (Array.length branches) 0 ctx in
	let case =
	  let ty = it_mkProd_or_LetIn ty' liftctx in
	  let ty = it_mkLambda_or_LetIn ty branches_lets in
	  let nbbranches = (Name (id_of_string "branches"), 
			   Some (Class_tactics.coq_nat_of_int (length branches_lets)),
			   Lazy.force Class_tactics.coq_nat)
	  in
	  let nbdiscr = (Name (id_of_string "target"), 
			Some (Class_tactics.coq_nat_of_int (length before)),
			Lazy.force Class_tactics.coq_nat)
	  in
	  let ty = it_mkLambda_or_LetIn (lift 2 ty) [nbbranches;nbdiscr] in
	  let term = e_new_evar isevar env ~src:(dummy_loc, QuestionMark true) ty in
	    term
	in       
	let casetyp = it_mkProd_or_LetIn ty' ctx in
	  mkCast(case, DEFAULTcast, casetyp), casetyp

  in aux tree

open Topconstr
open Constrintern
open Decl_kinds

type equation = identifier located * constr_expr list * (constr_expr, identifier located) rhs

let locate_reference qid =
  match Nametab.extended_locate qid with
    | TrueGlobal ref -> true
    | SyntacticDef kn -> true

let is_global id =
  try 
    locate_reference (make_short_qualid id)
  with Not_found -> 
    false

let is_freevar ids env x =
  try
    if Idset.mem x ids then false
    else
      try ignore(Environ.lookup_named x env) ; false
      with _ -> not (is_global x)
  with _ -> true
  
let ids_of_patc c ?(bound=Idset.empty) l = 
  let found id bdvars l =
    if not (is_freevar bdvars (Global.env ()) (snd id)) then l
    else if List.exists (fun (_, id') -> id' = snd id) l then l 
    else id :: l 
  in
  let rec aux bdvars l c = match c with
    | CRef (Ident lid) -> found lid bdvars l
    | CNotation (_, "{ _ : _ | _ }", (CRef (Ident (_, id))) :: _) when not (Idset.mem id bdvars) ->
	fold_constr_expr_with_binders (fun a l -> Idset.add a l) aux (Idset.add id bdvars) l c
    | c -> fold_constr_expr_with_binders (fun a l -> Idset.add a l) aux bdvars l c
  in aux bound l c
    
let interp_pats isevar env impls pats sign =
  let vars = fold_left (fun acc patc -> ids_of_patc patc acc) [] pats in
  let varsctx, env' = 
    fold_right (fun (loc, id) (ctx, env) ->
      let decl =
	let ty = e_new_evar isevar env ~src:(loc, BinderType (Name id)) (new_Type ()) in
	  (Name id, None, ty) 
      in
	decl::ctx, push_rel decl env)
      vars ([], env)
  in
  let patcs = 
    fold_left2 (fun subst pat (_, _, ty) -> 
      let ty = substl subst ty in
	interp_casted_constr_evars isevar env' ~impls pat ty :: subst)
      [] pats (List.rev sign)
  in
    isevar := nf_evar_defs !isevar;
    (nf_rel_context_evar (Evd.evars_of !isevar) varsctx, 
    nf_env_evar (Evd.evars_of !isevar) env',
    map (nf_evar (Evd.evars_of !isevar)) patcs)
      
let interp_eqn isevar env impls sign arity (idl, pats, rhs) =
  let ctx, env', patcs = interp_pats isevar env impls pats sign in
  let rhs' = match rhs with
    | Program p -> 
	Program (interp_casted_constr_evars isevar env' ~impls p (substl patcs arity))
    | Empty lid -> Empty (fst (lookup_rel_id (snd lid) ctx))
  in (ctx, rev patcs, rhs')	

open Entries

let define_by_eqs i l t eqs =
  let env = Global.env () in
  let isevar = ref (create_evar_defs Evd.empty) in
  let (env', sign), impls = interp_context_evars isevar env l in
  let arity = interp_type_evars isevar env' t in
  let is_recursive, fixenv = 
    let occur_eqn (_, _, rhs) =
      match rhs with
      | Program c -> occur_var_constr_expr i c
      | _ -> false
    in 
      if exists occur_eqn eqs then 
	let ty = it_mkProd_or_LetIn arity sign in
	let fixenv = push_rel (Name i, None, ty) env in
	  true, fixenv
      else false, env
  in
  let equations = map (interp_eqn isevar fixenv ([],[]) sign arity) eqs in
  let sign = nf_rel_context_evar (Evd.evars_of !isevar) sign in
  let arity = nf_evar (Evd.evars_of !isevar) arity in
  let prob = (i, sign, arity) in
  let fixenv = nf_env_evar (Evd.evars_of !isevar) fixenv in
  let split = make_split fixenv prob equations in
    (* if valid_tree prob split then *)
  let t, ty = term_of_tree isevar fixenv prob split in
  let t = 
    if is_recursive then
      let firstsplit = 
	match split with
	| Split (ctx, lhs, rel, indf, unif, sp) -> (length ctx - rel)
	| _ -> 0
      in mkFix (([|firstsplit|], 0), ([|Name i|], [|ty|], [|t|]))
    else t
  in
  let undef = undefined_evars !isevar in
  let obls, t', ty' = Eterm.eterm_obligations env i !isevar (Evd.evars_of undef) 0 t ty in
    ignore(Subtac_obligations.add_definition i t' ty' obls)
      
module Gram = Pcoq.Gram
module Vernac = Pcoq.Vernac_
module Tactic = Pcoq.Tactic

module DeppatGram =
struct
  let gec s = Gram.Entry.create ("Deppat."^s)

  let deppat_equations : equation list Gram.Entry.e = gec "deppat_equations"

  let binders_let2 : local_binder list Gram.Entry.e = gec "binders_let2"
end

open Rawterm
open DeppatGram 
open Util
open Pcoq
open Prim
open Constr

GEXTEND Gram
  GLOBAL: (* deppat_gallina_loc *) deppat_equations binders_let2;
 
  deppat_equations:
    [ [ l = LIST1 equation SEP ";" -> l ] ]
  ;

  binders_let2:
    [ [ l = binders_let -> l ] ]
  ;

  equation:
    [ [ c = Constr.lconstr; r=rhs ->
      match c with
      | CApp (loc, (None, CRef (Ident lid)), l) ->
	  (lid, List.map fst l, r)
      | _ -> error "Error parsing equation" ] ]
  ;

  rhs:
    [ [ ":=!"; id = identref -> Empty id
      |":="; c = Constr.lconstr -> Program c
    ] ]
  ;
  
  END

type 'a deppat_equations_argtype = (equation list, 'a) Genarg.abstract_argument_type

let (wit_deppat_equations : Genarg.tlevel deppat_equations_argtype),
  (globwit_deppat_equations : Genarg.glevel deppat_equations_argtype),
  (rawwit_deppat_equations : Genarg.rlevel deppat_equations_argtype) =
  Genarg.create_arg "deppat_equations"

type 'a binders_let2_argtype = (local_binder list, 'a) Genarg.abstract_argument_type

let (wit_binders_let2 : Genarg.tlevel binders_let2_argtype),
  (globwit_binders_let2 : Genarg.glevel binders_let2_argtype),
  (rawwit_binders_let2 : Genarg.rlevel binders_let2_argtype) =
  Genarg.create_arg "binders_let2"


VERNAC COMMAND EXTEND Define_equations
| [ "Equations" ident(i) binders_let2(l) ":" lconstr(t) ":=" deppat_equations(eqs) ] ->
    [ define_by_eqs i l t eqs ]
END

open Tacmach
open Tacexpr
open Tactics
open Tacticals

let contrib_tactics_path =
  make_dirpath (List.map id_of_string ["Equality";"Program";"Coq"])

let tactics_tac s =
  lazy(make_kn (MPfile contrib_tactics_path) (make_dirpath []) (mk_label s))

let destruct_last args =
  Tacinterp.eval_tactic (TacArg(TacCall(dummy_loc, 
				       ArgArg(dummy_loc, Lazy.force (tactics_tac "destruct_last")),args)))
    
let rec int_of_coq_nat c = 
  match kind_of_term c with
  | App (f, [| arg |]) -> succ (int_of_coq_nat arg)
  | _ -> 0

let solve_equations_goal tac gl =
  let concl = pf_concl gl in
  let targetn, branchesn, targ, brs, b =
    match kind_of_term concl with
    | LetIn (Name target, targ, _, b) ->
	(match kind_of_term b with
	| LetIn (Name branches, brs, _, b) ->
	    target, branches, int_of_coq_nat targ, int_of_coq_nat brs, b
	| _ -> error "Unnexpected goal")
    | _ -> error "Unnexpected goal"
  in
  let branches, b = 
    let rec aux n c =
      if n = 0 then [], c
      else match kind_of_term c with
      | LetIn (Name id, br, brt, b) -> 
	  let rest, b = aux (pred n) b in
	    (id, br, brt) :: rest, b
      | _ -> error "Unnexpected goal"
    in aux brs b
  in 
  let ids = targetn :: branchesn :: map pi1 branches in
  let cleantac = tclTHEN (intros_using ids) (thin ids) in
  let dotac = tclDO (succ targ) intro in
  let subtacs = 
    tclTHENS (destruct_last [])
      (map (fun (id, br, brt) -> tclTHEN (letin_tac None (Name id) br onConcl) tac) branches)
  in tclTHENLIST [cleantac ; dotac ; subtacs] gl
      
TACTIC EXTEND solve_equations
  [ "solve_equations" tactic(tac) ] -> [ solve_equations_goal (snd tac) ]
END
