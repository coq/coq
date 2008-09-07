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
  | PInac of constr

let coq_inacc = lazy (Coqlib.gen_constant "equations" ["Program";"Equality"] "inaccessible_pattern")
  
let mkInac env c =
  mkApp (Lazy.force coq_inacc, [| Typing.type_of env Evd.empty c ; c |])
    
let rec constr_of_pat ?(inacc=true) env = function
  | PRel i -> mkRel i
  | PCstr (c, p) -> 
      let c' = mkConstruct c in
	mkApp (c', Array.of_list (constrs_of_pats ~inacc env p))
  | PInac r -> 
      if inacc then try mkInac env r with _ -> r else r
      
and constrs_of_pats ?(inacc=true) env l = map (constr_of_pat ~inacc env) l

let rec pat_vars = function
  | PRel i -> Intset.singleton i
  | PCstr (c, p) -> pats_vars p
  | PInac _ -> Intset.empty

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
  | App (f, [| a ; c |]) when eq_constr f (Lazy.force coq_inacc) ->
      PInac c
  | App (f, args) when isConstruct f ->
      PCstr (destConstruct f, pats_of_constrs (Array.to_list args))
  | Construct f -> PCstr (f, [])
  | _ -> PInac c

let inaccs_of_constrs l = map (fun x -> PInac x) l

exception Conflict

let rec pmatch p c =
  match p, c with
  | PRel i, t -> true
(*   | _, PRel i -> true *)
  | PCstr (c, pl), PCstr (c', pl') when c = c' -> pmatches pl pl'
  | PInac _, _ -> true
  | _, _ -> false

and pmatches pl l =
  match pl, l with
  | [], [] -> true
  | hd :: tl, hd' :: tl' -> pmatch hd hd' && pmatches tl tl'
  | _ -> false

let pattern_matches pl l = pmatches pl l

(* let rec pmatch p c = *)
(*   match p, kind_of_term c with *)
(*   | PRel i, t -> true *)
(*   | t, Rel n -> true *)
(*   | PCstr (c, pl), App (c', l') when kind_of_term c' = Construct c ->  *)
(*       pmatches pl (Array.to_list l') *)
(*   | PCstr (c, []), Construct c' when c' = c -> true *)
(*   | PInac _, _ -> true *)
(*   | _, _ -> false *)

(* and pmatches pl l = *)
(*   match pl, l with *)
(*   | [], [] -> true *)
(*   | hd :: tl, hd' :: tl' -> pmatch hd hd' && pmatches tl tl' *)
(*   | _ -> false *)

(* let pattern_matches pl l = pmatches pl l *)

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
  | PInac r -> PInac (liftn n k r)
      
and lift_pats n k = map (lift_pat n k)

let rec subst_pat env k t p = 
  match p with
  | PRel i -> 
      if i = k then t
      else if i > k then PRel (pred i)
      else p
  | PCstr(c, pl) ->
      PCstr (c, subst_pats env k t pl)
  | PInac r -> PInac (substnl [constr_of_pat ~inacc:false env t] (pred k) r)

and subst_pats env k t = map (subst_pat env k t)

let rec specialize s p = 
  match p with
  | PRel i -> 
      if mem_assoc i s then PInac (assoc i s)
      else p
  | PCstr(c, pl) ->
      PCstr (c, specialize_pats s pl)
  | PInac r -> PInac (specialize_constr s r)

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

and clause = lhs * (constr, int) rhs

and lhs = rel_context * identifier * pat list

and ('a, 'b) rhs = 
  | Program of 'a
  | Empty of 'b

type splitting = 
  | Compute of clause
  | Split of lhs * int * inductive_family *
      unification_result array * splitting option array
      
and unification_result = 
  rel_context * int * constr * pat * substitution option

and substitution = (int * constr) list

type problem = identifier * lhs

let rels_of_tele tele = rel_list 0 (List.length tele)

let patvars_of_tele tele = map (fun c -> PRel (destRel c)) (rels_of_tele tele)

let split_solves split prob =
  match split with
  | Compute (lhs, rhs) -> lhs = prob
  | Split (lhs, id, indf, us, ls) -> lhs = prob

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

let rec add_var_subst env subst n c =
  if mem_assoc n subst then
    let t = assoc n subst in
      if eq_constr t c then subst
      else unify env subst t c
  else 
    let rel = mkRel n in
      if rel = c then subst
      else if dependent rel c then raise Conflict
      else (n, c) :: subst
    
and unify env subst x y =
  match kind_of_term x, kind_of_term y with
  | Rel n, _ -> add_var_subst env subst n y
  | _, Rel n -> add_var_subst env subst n x
  | App (c, l), App (c', l') when eq_constr c c' ->
      unify_constrs env subst (Array.to_list l) (Array.to_list l')
  | _, _ -> if eq_constr x y then subst else raise Conflict

and unify_constrs (env : env) subst l l' = 
  if List.length l = List.length l' then
    fold_left2 (unify env) subst l l'
  else raise Conflict

let substituted_context subst ctx =
  let substitute_in_ctx n c ctx =
    let rec aux k after = function
      | [] -> []
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
	  record_subst (pred k) (liftn (-1) k t);
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
    let vs = map (Reduction.whd_betadeltaiota envb) args in
    let cstrs = Inductiveops.arities_of_constructors envb ind in
    let cstrs = 
      Array.mapi (fun i ty ->
	let ty = prod_applist ty params in
	let ctx, ty = decompose_prod_assum ty in
	let ctx, ids = 
	  let ids = ids_of_rel_context ctx in
	    fold_right (fun (n, b, t as decl) (acc, ids) ->
	      match n with Name _ -> (decl :: acc), ids
	      | Anonymous -> let id = next_name_away Anonymous ids in
			       ((Name id, b, t) :: acc), (id :: ids))
	      ctx ([], ids)
	in
	let env' = push_rel_context ctx (Global.env ()) in
	let IndType (indf, args) = find_rectype env' Evd.empty ty in
	let ind, params = dest_ind_family indf in
	let constr = applist (mkConstruct (ind, succ i), params @ rels_of_tele ctx) in
	let constrpat = PCstr ((ind, succ i), inaccs_of_constrs params @ patvars_of_tele ctx) in
	  env', ctx, constr, constrpat, (* params @  *)args)
	cstrs
    in
    let res = 
      Array.map (fun (env', ctxc, c, cpat, us) -> 
	let _beforelen = length before and ctxclen = length ctxc in
	let fullctx = ctxc @ before in
	  try
	    let fullenv = push_rel_context fullctx (Global.env ()) in
	    let vs' = map (lift ctxclen) vs in
	    let subst = unify_constrs fullenv [] us vs' in
	    let subst', ctx' = substituted_context subst fullctx in
	      (ctx', ctxclen, c, cpat, Some subst')
	  with Conflict -> 
	    (fullctx, ctxclen, c, cpat, None)) cstrs
    in Some (res, indf)
  with Not_found -> (* not an inductive type *)
    None

let rec id_of_rel n l =
  match n, l with
  | 0, (Name id, _, _) :: tl -> id
  | n, _ :: tl -> id_of_rel (pred n) tl
  | _, _ -> raise (Invalid_argument "id_of_rel")

let constrs_of_lhs ?(inacc=true) env (ctx, _, pats) = 
  constrs_of_pats ~inacc (push_rel_context ctx env) pats
      
let rec valid_splitting (f, delta, t, pats) tree = 
  split_solves tree (delta, f, pats) && 
    valid_splitting_tree (f, delta, t) tree
    
and valid_splitting_tree (f, delta, t) = function
  | Compute (lhs, Program rhs) -> 
      let subst = constrs_of_lhs ~inacc:false (Global.env ()) lhs in 
	ignore(check_judgment (pi1 lhs) rhs (substl subst t)); true

  | Compute ((ctx, id, lhs), Empty split) -> 
      let before, (x, _, ty), after = split_context split ctx in
      let unify = 
	match unify_type before ty with
	| Some (unify, _) -> unify 
	| None -> assert false
      in
	array_for_all (fun (_, _, _, _, x) -> x = None) unify
	  
  | Split ((ctx, id, lhs), rel, indf, unifs, ls) -> 
      let before, (id, _, ty), after = split_tele (pred rel) ctx in
      let unify, indf' = Option.get (unify_type before ty) in
	assert(indf = indf');
	if not (array_exists (fun (_, _, _, _, x) -> x <> None) unify) then false
	else
	  let ok, splits = 
	    Array.fold_left (fun (ok, splits as acc) (ctx', ctxlen, cstr, cstrpat, subst) -> 
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
					    (lift_contextn ctxlen 0 after)) @ before in
		  let liftpats = lift_pats ctxlen rel lhs in
		  let newpats = specialize_pats subst (subst_pats (Global.env ()) rel cstrpat liftpats) in
		    (ok, (f, newdelta, newpats) :: splits))
	      (true, []) unify
	  in
	  let subst = List.map2 (fun (id, _, _) x -> out_name id, x) delta 
	    (constrs_of_pats ~inacc:false (Global.env ()) lhs) 
	  in
	  let t' = replace_vars subst t in
	    ok && for_all 
	      (fun (f, delta', pats') -> 
		array_exists (function None -> false | Some tree -> valid_splitting (f, delta', t', pats') tree) ls) splits
	      
let valid_tree (f, delta, t) tree = 
  valid_splitting (f, delta, t, patvars_of_tele delta) tree

let find_split (_, _, curpats : lhs) (_, _, patcs : lhs) =
  let rec find_split_pat curpat patc =
    match patc with
    | PRel _ -> (* The pattern's a variable, don't split *) None
    | PCstr (f, args) ->
	(match curpat with
	| PCstr (f', args') when f = f' -> (* Already split at this level, continue *)
	    find_split_pats args' args
	| PRel i -> (* Split on i *) Some i
	| _ -> None)
    | PInac _ -> None

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

let pr_pat env c =
  try 
    let patc = constr_of_pat env c in
      try pr_constr_pat env patc with _ -> str"pr_constr_pat raised an exception"
  with _ -> str"constr_of_pat raised an exception"
    
let pr_context env c =
  let pr_decl (id,b,_) = match id with Name id -> pr_id id | Anonymous -> str"_" in
    prlist_with_sep pr_spc pr_decl (List.rev c)
(*   Printer.pr_rel_context env c *)

let pr_lhs env (delta, f, patcs) =
  let env = push_rel_context delta env in
  let ctx = pr_context env delta in
    (if delta = [] then ctx else str "[" ++ ctx ++ str "]" ++ spc ())
    ++ pr_id f ++ spc () ++ prlist_with_sep spc (pr_pat env) patcs

let pr_rhs env = function
  | Empty var -> spc () ++ str ":=!" ++ spc () ++ print_constr_env env (mkRel var)
  | Program rhs -> spc () ++ str ":=" ++ spc () ++ print_constr_env env rhs
      
let pr_clause env (lhs, rhs) =
  pr_lhs env lhs ++ 
    (let env' = push_rel_context (pi1 lhs) env in
       pr_rhs env' rhs)
    
(* let pr_splitting env = function *)
(*   | Compute cl -> str "Compute " ++ pr_clause env cl *)
(*   | Split (lhs, n, indf, results, splits) -> *)

(* let pr_unification_result (ctx, n, c, pat, subst) = *)
  
(*       unification_result array * splitting option array *)

let pr_clauses env =
  prlist_with_sep fnl (pr_clause env)
    

let lhs_matches (delta, _, patcs : lhs) (delta', _, patcs' : lhs) =
  pattern_matches patcs patcs'

let rec split_on env var (delta, f, curpats as lhs) clauses =
  let before, (id, _, ty), after = split_tele (pred var) delta in
  let unify, indf = 
    match unify_type before ty with 
    | Some r -> r
    | None -> assert false (* We decided... so it better be inductive *)
  in
  let clauses = ref clauses in
  let splits = 
    Array.map (fun (ctx', ctxlen, cstr, cstrpat, s) ->
      match s with
      | None -> None
      | Some s -> 
	  (* ctx' |- s cstr, s cstrpat *)
	  let newdelta =
	    subst_context s (subst_rel_context 0 cstr 
				(lift_contextn ctxlen 1 after)) @ ctx' in
	  let liftpats = 
	    (* delta |- curpats -> before; ctxc; id; after |- liftpats *)
	    lift_pats ctxlen (succ var) curpats 
	  in
	  let liftpat = (* before; ctxc |- cstrpat -> before; ctxc; after |- liftpat *)
	    lift_pat (pred var) 1 cstrpat
	  in
	  let substpat = (* before; ctxc; after |- liftpats[id:=liftpat] *)
	    subst_pats env var liftpat liftpats 
	  in
	  let lifts = (* before; ctxc |- s : newdelta ->
			 before; ctxc; after |- lifts : newdelta ; after *)
	    map (fun (k,x) -> (pred var + k, lift (pred var) x)) s
	  in
	  let newpats = specialize_pats lifts substpat in
	  let newlhs = (newdelta, f, newpats) in
	  let matching, rest = partition (fun (lhs, rhs) -> lhs_matches newlhs lhs) !clauses in
	    clauses := rest;
	    if matching = [] then (
	      (* Try finding a splittable variable *)
	      let (id, _) = 
		fold_right (fun (id, _, ty as decl) (accid, ctx) -> 
		  match accid with 
		  | Some _ -> (accid, ctx)
		  | None -> 
		      match unify_type ctx ty with
		      | Some (unify, indf) ->
			  if array_for_all (fun (_, _, _, _, x) -> x = None) unify then
			    (Some id, ctx)
			  else (None, decl :: ctx)
		      | None -> (None, decl :: ctx))
		  newdelta (None, [])
	      in 
		match id with
		| None ->
		    errorlabstrm "deppat"
	      	      (str "Non-exhaustive pattern-matching, no clause found for:" ++ fnl () ++
	      		  pr_lhs env newlhs)
		| Some id -> 
		    Some (Compute (newlhs, Empty (fst (lookup_rel_id (out_name id) newdelta))))
	    ) else (
	      let splitting = make_split_aux env newlhs matching in
		Some splitting))
      unify
  in
    if !clauses <> [] then
      errorlabstrm "deppat"
	(str "Impossible clauses:" ++ fnl () ++ pr_clauses env !clauses);
    Split (lhs, var, indf, unify, splits)
      
and make_split_aux env lhs clauses =
  let split = 
    fold_left (fun acc (lhs', rhs) -> 
      match acc with 
      | None -> find_split lhs lhs'
      | _ -> acc) None clauses
  in 
    match split with
    | Some var -> split_on env var lhs clauses
    | None ->
	(match clauses with
	| [] -> error "No clauses left"
	| [(lhs, rhs)] ->
	    (* No need to split anymore *)
	    Compute (lhs, rhs)
(* 	    (match rhs with *)
(* 	    | Program _ -> *)
(* 		Compute (delta', pats_of_constrs patcs, rhs) *)
(* 	    | Empty split -> (\* TODO : Check unify_type inductive type *\) *)
(* 		Compute (delta', pats_of_constrs patcs, rhs) *)
		  (* 	    	errorlabstrm "deppat" *)
		  (* 		  (str "Splitting on " ++ pr_id x ++ str " of type " ++  *)
		  (* 		      pr_constr_env (push_rel_context before env)  *)
		  (* 		      an empty type, on variable)) *)
	| _ ->
	    errorlabstrm "make_split_aux"
	      (str "Overlapping clauses:" ++ fnl () ++ pr_clauses env clauses))

let make_split env (f, delta, t) clauses =
  make_split_aux env (delta, f, patvars_of_tele delta) clauses
    
open Evd
open Evarutil

let lift_substitution n s = map (fun (k, x) -> (k + n, x)) s
let map_substitution s t = map (subst_rel_subst 0 s) t

let term_of_tree status isevar env (i, delta, ty) tree =
  let rec aux = function
    | Compute ((ctx, _, pats as lhs), Program rhs) -> 
	let ty' = substl (rev (constrs_of_lhs ~inacc:false env lhs)) ty in
	let body = it_mkLambda_or_LetIn rhs ctx and typ = it_mkProd_or_LetIn ty' ctx in
	  mkCast(body, DEFAULTcast, typ), typ

    | Compute ((ctx, _, pats as lhs), Empty split) ->
	let ty' = substl (rev (constrs_of_lhs ~inacc:false env lhs)) ty in
	let split = (Name (id_of_string "split"), 
		    Some (Class_tactics.coq_nat_of_int (1 + (length ctx - split))),
		    Lazy.force Class_tactics.coq_nat)
	in
	let ty' = it_mkProd_or_LetIn ty' ctx in
	let let_ty' = mkLambda_or_LetIn split (lift 1 ty') in
	let term = e_new_evar isevar env ~src:(dummy_loc, QuestionMark (Define true)) let_ty' in
	  term, ty'
	    
    | Split ((ctx, _, pats as lhs), rel, indf, unif, sp) -> 
	let before, decl, after = split_tele (pred rel) ctx in
	let ty' = substl (rev (constrs_of_lhs ~inacc:false env lhs)) ty in
	let branches = 
	  array_map2 (fun (ctx', ctxlen, cstr, cstrpat, subst) split -> 
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
	  let term = e_new_evar isevar env ~src:(dummy_loc, QuestionMark status) ty in
	    term
	in       
	let casetyp = it_mkProd_or_LetIn ty' ctx in
	  mkCast(case, DEFAULTcast, casetyp), casetyp

  in aux tree

open Topconstr
open Constrintern
open Decl_kinds

type equation = constr_expr * (constr_expr, identifier located) rhs

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

let interp_pats i isevar env impls pat sign recu =
  let bound = Idset.singleton i in
  let vars = ids_of_patc pat ~bound [] in
  let varsctx, env' = 
    fold_right (fun (loc, id) (ctx, env) ->
      let decl =
	let ty = e_new_evar isevar env ~src:(loc, BinderType (Name id)) (new_Type ()) in
	  (Name id, None, ty) 
      in
	decl::ctx, push_rel decl env)
      vars ([], env)
  in
  let pats =
    let patenv = match recu with None -> env' | Some ty -> push_named (i, None, ty) env' in
    let patt, _ = interp_constr_evars_impls ~evdref:isevar patenv ~impls:([],[]) pat in
      match kind_of_term patt with
      | App (m, args) -> 
	  if not (eq_constr m (mkRel (succ (length varsctx)))) then
	    user_err_loc (constr_loc pat, "interp_pats",
			 str "Expecting a pattern for " ++ pr_id i)
	  else Array.to_list args
      | _ -> user_err_loc (constr_loc pat, "interp_pats",
			  str "Error parsing pattern: unnexpected left-hand side")
  in
    isevar := nf_evar_defs !isevar;
    (nf_rel_context_evar (Evd.evars_of !isevar) varsctx, 
    nf_env_evar (Evd.evars_of !isevar) env',
    rev_map (nf_evar (Evd.evars_of !isevar)) pats)
      
let interp_eqn i isevar env impls sign arity recu (pats, rhs) =
  let ctx, env', patcs = interp_pats i isevar env impls pats sign recu in
  let rhs' = match rhs with
    | Program p -> 
	Program (interp_casted_constr_evars isevar env' ~impls p (substl patcs arity))
    | Empty lid -> Empty (fst (lookup_rel_id (snd lid) ctx))
  in ((ctx, i, pats_of_constrs (rev patcs)), rhs')	

open Entries

open Tacmach
open Tacexpr
open Tactics
open Tacticals

let contrib_tactics_path =
  make_dirpath (List.map id_of_string ["Equality";"Program";"Coq"])

let tactics_tac s =
  make_kn (MPfile contrib_tactics_path) (make_dirpath []) (mk_label s)
    
let equations_tac = lazy 
  (Tacinterp.eval_tactic 
      (TacArg(TacCall(dummy_loc, 
		     ArgArg(dummy_loc, tactics_tac "equations"), []))))

let define_by_eqs i l t nt eqs =
  let env = Global.env () in
  let isevar = ref (create_evar_defs Evd.empty) in
  let (env', sign), impls = interp_context_evars isevar env l in
  let arity = interp_type_evars isevar env' t in
  let ty = it_mkProd_or_LetIn arity sign in
  let data = Command.compute_interning_datas env [] [i] [ty] [impls] in
  let fixdecls = [(Name i, None, ty)] in
  let fixenv = push_rel_context fixdecls env in
  let equations = 
    States.with_heavy_rollback (fun () -> 
      Option.iter (Command.declare_interning_data data) nt;
      map (interp_eqn i isevar fixenv data sign arity None) eqs) ()
  in
  let sign = nf_rel_context_evar (Evd.evars_of !isevar) sign in
  let arity = nf_evar (Evd.evars_of !isevar) arity in
  let prob = (i, sign, arity) in
  let fixenv = nf_env_evar (Evd.evars_of !isevar) fixenv in
  let fixdecls = nf_rel_context_evar (Evd.evars_of !isevar) fixdecls in
    (*   let ce = check_evars fixenv Evd.empty !isevar in *)
    (*   List.iter (function (_, _, Program rhs) -> ce rhs | _ -> ()) equations; *)
  let is_recursive, env' =
    let occur_eqn ((ctx, _, _), rhs) =
      match rhs with
      | Program c -> dependent (mkRel (succ (length ctx))) c
      | _ -> false
    in if exists occur_eqn equations then true, fixenv else false, env
  in
  let split = make_split env' prob equations in
    (* if valid_tree prob split then *)
  let status = (* if is_recursive then Expand else *) Define false in
  let t, ty = term_of_tree status isevar env' prob split in
  let undef = undefined_evars !isevar in
  let t, ty = if is_recursive then 
    (it_mkLambda_or_LetIn t fixdecls, it_mkProd_or_LetIn ty fixdecls)
    else t, ty
  in
  let obls, t', ty' = 
    Eterm.eterm_obligations env i !isevar (Evd.evars_of undef) 0 ~status t ty
  in
    if is_recursive then
      ignore(Subtac_obligations.add_mutual_definitions [(i, t', ty', impls, obls)] [] 
		~tactic:(Lazy.force equations_tac)
		(Command.IsFixpoint [None, CStructRec]))
    else
      ignore(Subtac_obligations.add_definition
		~implicits:impls i t' ty' ~tactic:(Lazy.force equations_tac) obls)
      
module Gram = Pcoq.Gram
module Vernac = Pcoq.Vernac_
module Tactic = Pcoq.Tactic

module DeppatGram =
struct
  let gec s = Gram.Entry.create ("Deppat."^s)

  let deppat_equations : equation list Gram.Entry.e = gec "deppat_equations"

  let binders_let2 : local_binder list Gram.Entry.e = gec "binders_let2"

(*   let where_decl : decl_notation Gram.Entry.e = gec "where_decl" *)

end

open Rawterm
open DeppatGram 
open Util
open Pcoq
open Prim
open Constr
open G_vernac

GEXTEND Gram
  GLOBAL: (* deppat_gallina_loc *) deppat_equations binders_let2;
 
  deppat_equations:
    [ [ l = LIST1 equation SEP ";" -> l ] ]
  ;

  binders_let2:
    [ [ l = binders_let -> l ] ]
  ;

  equation:
    [ [ c = Constr.lconstr; r=rhs -> (c, r) ] ]
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

type 'a decl_notation_argtype = (Vernacexpr.decl_notation, 'a) Genarg.abstract_argument_type

let (wit_decl_notation : Genarg.tlevel decl_notation_argtype),
  (globwit_decl_notation : Genarg.glevel decl_notation_argtype),
  (rawwit_decl_notation : Genarg.rlevel decl_notation_argtype) =
  Genarg.create_arg "decl_notation"



VERNAC COMMAND EXTEND Define_equations
| [ "Equations" ident(i) binders_let2(l) ":" lconstr(t) ":=" deppat_equations(eqs)
      decl_notation(nt) ] ->
    [ define_by_eqs i l t nt eqs ]
END
    
let rec int_of_coq_nat c = 
  match kind_of_term c with
  | App (f, [| arg |]) -> succ (int_of_coq_nat arg)
  | _ -> 0

let solve_equations_goal destruct_tac tac gl =
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
    tclTHENS destruct_tac
      (map (fun (id, br, brt) -> tclTHEN (letin_tac None (Name id) br onConcl) tac) branches)
  in tclTHENLIST [cleantac ; dotac ; subtacs] gl
    
TACTIC EXTEND solve_equations
  [ "solve_equations" tactic(destruct) tactic(tac) ] -> [ solve_equations_goal (snd destruct) (snd tac) ]
END
