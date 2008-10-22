(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
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
(*i*)

let ids_of_list l = 
  List.fold_right Idset.add l Idset.empty

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

(* Auxilliary functions for the inference of implicitly quantified variables. *)    

let free_vars_of_constr_expr c ?(bound=Idset.empty) l = 
  let found id bdvars l = 
    if List.mem id l then l 
    else if not (is_freevar bdvars (Global.env ()) id)
    then l else id :: l 
  in
  let rec aux bdvars l c = match c with
    | CRef (Ident (_,id)) -> found id bdvars l
    | CNotation (_, "{ _ : _ | _ }", (CRef (Ident (_, id)) :: _, [])) when not (Idset.mem id bdvars) ->
	fold_constr_expr_with_binders (fun a l -> Idset.add a l) aux (Idset.add id bdvars) l c
    | c -> fold_constr_expr_with_binders (fun a l -> Idset.add a l) aux bdvars l c
  in aux bound l c

let add_name_to_ids set na = 
  match na with 
  | Anonymous -> set 
  | Name id -> Idset.add id set 
	
let free_vars_of_rawconstr ?(bound=Idset.empty) =
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
  in 
  fun rt -> List.rev (vars bound [] rt)
      

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

let rec make_fresh ids env x =
  if is_freevar ids env x then x else make_fresh ids env (Nameops.lift_ident x)

let freevars_of_ids env ids = 
  List.filter (is_freevar env (Global.env())) ids

let binder_list_of_ids ids =
  List.map (fun id -> LocalRawAssum ([dummy_loc, Name id], Default Implicit, CHole (dummy_loc, None))) ids
      
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
    
let combine_params_freevar avoid applied needed =
  combine_params avoid
    (fun avoid (_, (na, _, _)) -> 
      let id' = next_name_away_from na avoid in
	(CRef (Ident (dummy_loc, id')), Idset.add id' avoid))
    applied needed

let destClassApp cl =
  match cl with
    | CApp (loc, (None,CRef ref), l) -> loc, ref, List.map fst l
    | CAppExpl (loc, (None, ref), l) -> loc, ref, l
    | CRef ref -> loc_of_reference ref, ref, []
    | _ -> raise Not_found
      
let destClassAppExpl cl =
  match cl with
    | CApp (loc, (None,CRef ref), l) -> loc, ref, l
    | CRef ref -> loc_of_reference ref, ref, []
    | _ -> raise Not_found

let full_class_binder env (loc, id, l) gr = 
  let avoid = 
    Idset.union env (ids_of_list 
			(free_vars_of_constr_expr (CApp (loc, (None, mkRefC id), l)) ~bound:env []))
  in
  let c, avoid =
    let c = class_info gr in
    let (ci, rd) = c.cl_context in
    let pars = List.rev (List.combine ci rd) in
    let args, avoid = combine_params_freevar avoid l pars in
      CAppExpl (loc, (None, id), args), avoid
  in c

let implicits_of_rawterm l = 
  let rec aux i c = 
    match c with
	RProd (loc, na, bk, t, b) | RLambda (loc, na, bk, t, b) -> 
	  let rest = aux (succ i) b in
	    if bk = Implicit then
	      let name =
		match na with
		    Name id -> Some id
		  | Anonymous -> None
	      in
		(ExplByPos (i, name), (true, true)) :: rest
	    else rest
      | RLetIn (loc, na, t, b) -> aux i b
      | _ -> []
  in aux 1 l
