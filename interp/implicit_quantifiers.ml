(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2011     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*i*)
open Names
open Decl_kinds
open Term
open Sign
open Evd
open Environ
open Nametab
open Mod_subst
open Util
open Rawterm
open Topconstr
open Libnames
open Typeclasses
open Typeclasses_errors
open Pp
open Libobject
open Nameops
(*i*)

let generalizable_table = ref Idpred.empty

let _ =
  Summary.declare_summary "generalizable-ident"
    { Summary.freeze_function = (fun () -> !generalizable_table);
      Summary.unfreeze_function = (fun r -> generalizable_table := r);
      Summary.init_function = (fun () -> generalizable_table := Idpred.empty) }

let declare_generalizable_ident table (loc,id) =
  if id <> root_of_id id then
    user_err_loc(loc,"declare_generalizable_ident",
    (pr_id id ++ str
      " is not declarable as generalizable identifier: it must have no trailing digits, quote, or _"));
  if Idpred.mem id table then
    user_err_loc(loc,"declare_generalizable_ident",
		(pr_id id++str" is already declared as a generalizable identifier"))
  else Idpred.add id table

let add_generalizable gen table =
  match gen with
  | None -> Idpred.empty
  | Some [] -> Idpred.full
  | Some l -> List.fold_left (fun table lid -> declare_generalizable_ident table lid)
      table l

let cache_generalizable_type (_,(local,cmd)) =
  generalizable_table := add_generalizable cmd !generalizable_table

let load_generalizable_type _ (_,(local,cmd)) =
  generalizable_table := add_generalizable cmd !generalizable_table
    
let (in_generalizable, _) =
  declare_object {(default_object "GENERALIZED-IDENT") with
    load_function = load_generalizable_type;
    cache_function = cache_generalizable_type;
    classify_function = (fun (local, _ as obj) -> if local then Dispose else Keep obj)
  }
    
let declare_generalizable local gen =
 Lib.add_anonymous_leaf (in_generalizable (local, gen))

let find_generalizable_ident id = Idpred.mem (root_of_id id) !generalizable_table

let ids_of_list l =
  List.fold_right Idset.add l Idset.empty

let locate_reference qid =
  match Nametab.locate_extended qid with
    | TrueGlobal ref -> true
    | SynDef kn -> true

let is_global id =
  try
    locate_reference (qualid_of_ident id)
  with Not_found ->
    false

let is_freevar ids env x =
  try
    if Idset.mem x ids then false
    else
      try ignore(Environ.lookup_named x env) ; false
      with _ -> not (is_global x)
  with _ -> true

(* Auxiliary functions for the inference of implicitly quantified variables. *)

let ungeneralizable loc id =
  user_err_loc (loc, "Generalization", 
	       str "Unbound and ungeneralizable variable " ++ pr_id id)

let free_vars_of_constr_expr c ?(bound=Idset.empty) l =
  let found loc id bdvars l =
    if List.mem id l then l
    else if is_freevar bdvars (Global.env ()) id
    then
      if find_generalizable_ident id then id :: l
      else ungeneralizable loc id
    else l
  in
  let rec aux bdvars l c = match c with
    | CRef (Ident (loc,id)) -> found loc id bdvars l
    | CNotation (_, "{ _ : _ | _ }", (CRef (Ident (_, id)) :: _, [], [])) when not (Idset.mem id bdvars) ->
	fold_constr_expr_with_binders (fun a l -> Idset.add a l) aux (Idset.add id bdvars) l c
    | c -> fold_constr_expr_with_binders (fun a l -> Idset.add a l) aux bdvars l c
  in aux bound l c

let ids_of_names l =
  List.fold_left (fun acc x -> match snd x with Name na -> na :: acc | Anonymous -> acc) [] l

let free_vars_of_binders ?(bound=Idset.empty) l (binders : local_binder list) =
  let rec aux bdvars l c = match c with
      ((LocalRawAssum (n, _, c)) :: tl) ->
	let bound = ids_of_names n in
	let l' = free_vars_of_constr_expr c ~bound:bdvars l in
	  aux (Idset.union (ids_of_list bound) bdvars) l' tl

    | ((LocalRawDef (n, c)) :: tl) ->
	let bound = match snd n with Anonymous -> [] | Name n -> [n] in
	let l' = free_vars_of_constr_expr c ~bound:bdvars l in
	  aux (Idset.union (ids_of_list bound) bdvars) l' tl

    | [] -> bdvars, l
  in aux bound l binders

let add_name_to_ids set na =
  match na with
  | Anonymous -> set
  | Name id -> Idset.add id set

let generalizable_vars_of_rawconstr ?(bound=Idset.empty) ?(allowed=Idset.empty) =
  let rec vars bound vs = function
    | RVar (loc,id) ->
	if is_freevar bound (Global.env ()) id then
	  if List.mem_assoc id vs then vs
	  else (id, loc) :: vs
	else vs
    | RApp (loc,f,args) -> List.fold_left (vars bound) vs (f::args)
    | RLambda (loc,na,_,ty,c) | RProd (loc,na,_,ty,c) | RLetIn (loc,na,ty,c) ->
	let vs' = vars bound vs ty in
	let bound' = add_name_to_ids bound na in
	vars bound' vs' c
    | RCases (loc,sty,rtntypopt,tml,pl) ->
	let vs1 = vars_option bound vs rtntypopt in
	let vs2 = List.fold_left (fun vs (tm,_) -> vars bound vs tm) vs1 tml in
	List.fold_left (vars_pattern bound) vs2 pl
    | RLetTuple (loc,nal,rtntyp,b,c) ->
	let vs1 = vars_return_type bound vs rtntyp in
	let vs2 = vars bound vs1 b in
	let bound' = List.fold_left add_name_to_ids bound nal in
	vars bound' vs2 c
    | RIf (loc,c,rtntyp,b1,b2) ->
	let vs1 = vars_return_type bound vs rtntyp in
	let vs2 = vars bound vs1 c in
	let vs3 = vars bound vs2 b1 in
	vars bound vs3 b2
    | RRec (loc,fk,idl,bl,tyl,bv) ->
	let bound' = Array.fold_right Idset.add idl bound in
	let vars_fix i vs fid =
	  let vs1,bound1 =
	    List.fold_left
	      (fun (vs,bound) (na,k,bbd,bty) ->
		 let vs' = vars_option bound vs bbd in
		 let vs'' = vars bound vs' bty in
		 let bound' = add_name_to_ids bound na in
		 (vs'',bound')
	      )
	      (vs,bound')
	      bl.(i)
	  in
	  let vs2 = vars bound1 vs1 tyl.(i) in
	  vars bound1 vs2 bv.(i)
	in
	array_fold_left_i vars_fix vs idl
    | RCast (loc,c,k) -> let v = vars bound vs c in
	(match k with CastConv (_,t) -> vars bound v t | _ -> v)
    | (RSort _ | RHole _ | RRef _ | REvar _ | RPatVar _ | RDynamic _) -> vs

  and vars_pattern bound vs (loc,idl,p,c) =
    let bound' = List.fold_right Idset.add idl bound  in
    vars bound' vs c

  and vars_option bound vs = function None -> vs | Some p -> vars bound vs p

  and vars_return_type bound vs (na,tyopt) =
    let bound' = add_name_to_ids bound na in
    vars_option bound' vs tyopt
  in fun rt -> 
    let vars = List.rev (vars bound [] rt) in
      List.iter (fun (id, loc) ->
	if not (Idset.mem id allowed || find_generalizable_ident id) then 
	  ungeneralizable loc id) vars;
      vars

let rec make_fresh ids env x =
  if is_freevar ids env x then x else make_fresh ids env (Nameops.lift_subscript x)

let next_ident_away_from id avoid = make_fresh avoid (Global.env ()) id

let next_name_away_from na avoid =
  match na with
  | Anonymous -> make_fresh avoid (Global.env ()) (id_of_string "anon")
  | Name id -> make_fresh avoid (Global.env ()) id

let combine_params avoid fn applied needed =
  let named, applied =
    List.partition
      (function
	  (t, Some (loc, ExplByName id)) ->
	    if not (List.exists (fun (_, (id', _, _)) -> Name id = id') needed) then
	      user_err_loc (loc,"",str "Wrong argument name: " ++ Nameops.pr_id id);
	    true
	| _ -> false) applied
  in
  let named = List.map
    (fun x -> match x with (t, Some (loc, ExplByName id)) -> id, t | _ -> assert false)
    named
  in
  let needed = List.filter (fun (_, (_, b, _)) -> b = None) needed in
  let rec aux ids avoid app need =
    match app, need with
	[], [] -> List.rev ids, avoid

      | app, (_, (Name id, _, _)) :: need when List.mem_assoc id named ->
	  aux (List.assoc id named :: ids) avoid app need

      | (x, None) :: app, (None, (Name id, _, _)) :: need ->
	  aux (x :: ids) avoid app need

      | _, (Some cl, (_, _, _) as d) :: need ->
	  let t', avoid' = fn avoid d in
	    aux (t' :: ids) avoid' app need

      | x :: app, (None, _) :: need -> aux (fst x :: ids) avoid app need

      | [], (None, _ as decl) :: need ->
	  let t', avoid' = fn avoid decl in
	    aux (t' :: ids) avoid' app need

      | (x,_) :: _, [] ->
	  user_err_loc (constr_loc x,"",str "Typeclass does not expect more arguments")
  in aux [] avoid applied needed

let combine_params_freevar =
  fun avoid (_, (na, _, _)) ->
    let id' = next_name_away_from na avoid in
      (CRef (Ident (dummy_loc, id')), Idset.add id' avoid)

let destClassApp cl =
  match cl with
    | CApp (loc, (None, CRef ref), l) -> loc, ref, List.map fst l
    | CAppExpl (loc, (None, ref), l) -> loc, ref, l
    | CRef ref -> loc_of_reference ref, ref, []
    | _ -> raise Not_found

let destClassAppExpl cl =
  match cl with
    | CApp (loc, (None, CRef ref), l) -> loc, ref, l
    | CRef ref -> loc_of_reference ref, ref, []
    | _ -> raise Not_found

let implicit_application env ?(allow_partial=true) f ty =
  let is_class =
    try
      let (loc, r, _ as clapp) = destClassAppExpl ty in
      let (loc, qid) = qualid_of_reference r in
      let gr = Nametab.locate qid in
	if Typeclasses.is_class gr then Some (clapp, gr) else None
    with Not_found -> None
  in
    match is_class with
    | None -> ty, env
    | Some ((loc, id, par), gr) ->
	let avoid = Idset.union env (ids_of_list (free_vars_of_constr_expr ty ~bound:env [])) in
	let c, avoid =
	  let c = class_info gr in
	  let (ci, rd) = c.cl_context in
	  if not allow_partial then
	    begin
	      let applen = List.fold_left (fun acc (x, y) -> if y = None then succ acc else acc) 0 par in
	      let needlen = List.fold_left (fun acc x -> if x = None then succ acc else acc) 0 ci in
		if needlen <> applen then
		  Typeclasses_errors.mismatched_ctx_inst (Global.env ()) Parameters (List.map fst par) rd
	    end;
	  let pars = List.rev (List.combine ci rd) in
	  let args, avoid = combine_params avoid f par pars in
	    CAppExpl (loc, (None, id), args), avoid
	in c, avoid

let implicits_of_rawterm ?(with_products=true) l =
  let rec aux i c =
    let abs loc na bk t b =
      let rest = aux (succ i) b in
	if bk = Implicit then
	  let name =
	    match na with
	    | Name id -> Some id
	    | Anonymous -> None
	  in
	    (ExplByPos (i, name), (true, true, true)) :: rest
	else rest
    in
      match c with
      | RProd (loc, na, bk, t, b) ->
	  if with_products then abs loc na bk t b
	  else 
	    (if bk = Implicit then
	       msg_warning (str "Ignoring implicit status of product binder " ++ 
			      pr_name na ++ str " and following binders");
	     [])
      | RLambda (loc, na, bk, t, b) -> abs loc na bk t b
      | RLetIn (loc, na, t, b) -> aux i b
      | _ -> []
  in aux 1 l
