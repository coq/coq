(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i*)
open Util
open Names
open Libnames
open Nameops
open Termops
open Reductionops
open Term
open Glob_term
open Sign
open Environ
open Pattern
(*i*)

(* Given a term with second-order variables in it,
   represented by Meta's, and possibly applied using [SOAPP] to
   terms, this function will perform second-order, binding-preserving,
   matching, in the case where the pattern is a pattern in the sense
   of Dale Miller.

   ALGORITHM:

   Given a pattern, we decompose it, flattening Cast's and apply's,
   recursing on all operators, and pushing the name of the binder each
   time we descend a binder.

   When we reach a first-order variable, we ask that the corresponding
   term's free-rels all be higher than the depth of the current stack.

   When we reach a second-order application, we ask that the
   intersection of the free-rels of the term and the current stack be
   contained in the arguments of the application, and in that case, we
   construct a LAMBDA with the names on the stack.

 *)

type bound_ident_map = (identifier * identifier) list

exception PatternMatchingFailure

let constrain (n,(ids,m as x)) (names,terms as subst) =
  try
    let (ids',m') = List.assoc n terms in
    if ids = ids' && eq_constr m m' then subst
    else raise PatternMatchingFailure
  with
      Not_found ->
        if List.mem_assoc n names then
          Flags.if_verbose Pp.warning
              ("Collision between bound variable "^string_of_id n^
                 " and a metavariable of same name.");
        (names,(n,x)::terms)

let add_binders na1 na2 (names,terms as subst) =
  match na1, na2 with
  | Name id1, Name id2 ->
      if List.mem_assoc id1 names then
        (Flags.if_verbose Pp.warning
          ("Collision between bound variables of name "^string_of_id id1);
         (names,terms))
      else
        (if List.mem_assoc id1 terms then
            Flags.if_verbose Pp.warning
              ("Collision between bound variable "^string_of_id id1^
                  " and another bound variable of same name.");
         ((id1,id2)::names,terms));
  | _ -> subst

let build_lambda toabstract stk (m : constr) =
  let rec buildrec m p_0 p_1 = match p_0,p_1 with
    | (_, []) -> m
    | (n, (_,na,t)::tl) ->
	if List.mem n toabstract then
          buildrec (mkLambda (na,t,m)) (n+1) tl
        else
	  buildrec (lift (-1) m) (n+1) tl
  in
  buildrec m 1 stk

let same_case_structure (_,cs1,ind,_) ci2 br1 br2 =
  match ind with
  | Some ind -> ind = ci2.ci_ind
  | None -> cs1 = ci2.ci_cstr_ndecls

let rec list_insert f a = function
  | [] -> [a]
  | b::l when f a b -> a::b::l
  | b::l when a = b -> raise PatternMatchingFailure
  | b::l -> b :: list_insert f a l

let extract_bound_vars =
  let rec aux k = function
  | ([],_) -> []
  | (n::l,(na1,na2,_)::stk) when k = n ->
      begin match na1,na2 with
      | Name id1,Name _ -> list_insert (<) id1 (aux (k+1) (l,stk))
      | Name _,Anonymous -> anomaly "Unnamed bound variable"
      | Anonymous,_ -> raise PatternMatchingFailure
      end
  | (l,_::stk) -> aux (k+1) (l,stk)
  | (_,[]) -> assert false
  in aux 1

let dummy_constr = mkProp

let rec make_renaming ids = function
  | (Name id,Name _,_)::stk ->
      let renaming = make_renaming ids stk in
      (try mkRel (list_index id ids) :: renaming
       with Not_found -> dummy_constr :: renaming)
  | (_,_,_)::stk ->
      dummy_constr :: make_renaming ids stk
  | [] ->
      []

let merge_binding allow_bound_rels stk n cT subst =
  let depth = List.length stk in
  let c =
    if depth = 0 then
      (* Optimization *)
      ([],cT)
    else
      let frels = Intset.elements (free_rels cT) in
      let frels = List.filter (fun i -> i <= depth) frels in
      if allow_bound_rels then
	let frels = Sort.list (<) frels in
	let canonically_ordered_vars = extract_bound_vars (frels,stk) in
	let renaming = make_renaming canonically_ordered_vars stk in
	(canonically_ordered_vars, substl renaming cT)
      else if frels = [] then
	([],lift (-depth) cT)
      else
	raise PatternMatchingFailure in
  constrain (n,c) subst

let matches_core convert allow_partial_app allow_bound_rels pat c =
  let conv = match convert with
    | None -> eq_constr
    | Some (env,sigma) -> is_conv env sigma in
  let rec sorec stk subst p t =
    let cT = strip_outer_cast t in
    match p,kind_of_term cT with
      | PSoApp (n,args),m ->
	  let relargs =
	    List.map
	      (function
		 | PRel n -> n
		 | _ -> error "Only bound indices allowed in second order pattern matching.")
	      args in
	  let frels = Intset.elements (free_rels cT) in
	  if list_subset frels relargs then
	    constrain (n,([],build_lambda relargs stk cT)) subst
	  else
	    raise PatternMatchingFailure

      | PMeta (Some n), m -> merge_binding allow_bound_rels stk n cT subst

      | PMeta None, m -> subst

      | PRef (VarRef v1), Var v2 when v1 = v2 -> subst

      | PVar v1, Var v2 when v1 = v2 -> subst

      | PRef ref, _ when conv (constr_of_global ref) cT -> subst

      | PRel n1, Rel n2 when n1 = n2 -> subst

      | PSort (GProp c1), Sort (Prop c2) when c1 = c2 -> subst

      | PSort (GType _), Sort (Type _) -> subst

      | PApp (p, [||]), _ -> sorec stk subst p t

      | PApp (PApp (h, a1), a2), _ ->
          sorec stk subst (PApp(h,Array.append a1 a2)) t

      | PApp (PMeta (Some n),args1), App (c2,args2) when allow_partial_app ->
          let p = Array.length args2 - Array.length args1 in
          if p>=0 then
            let args21, args22 = array_chop p args2 in
	    let c = mkApp(c2,args21) in
            let subst = merge_binding allow_bound_rels stk n c subst in
            array_fold_left2 (sorec stk) subst args1 args22
          else raise PatternMatchingFailure

      | PApp (c1,arg1), App (c2,arg2) ->
        (try array_fold_left2 (sorec stk) (sorec stk subst c1 c2) arg1 arg2
         with Invalid_argument _ -> raise PatternMatchingFailure)

      | PProd (na1,c1,d1), Prod(na2,c2,d2) ->
	  sorec ((na1,na2,c2)::stk)
            (add_binders na1 na2 (sorec stk subst c1 c2)) d1 d2

      | PLambda (na1,c1,d1), Lambda(na2,c2,d2) ->
	  sorec ((na1,na2,c2)::stk)
            (add_binders na1 na2 (sorec stk subst c1 c2)) d1 d2

      | PLetIn (na1,c1,d1), LetIn(na2,c2,t2,d2) ->
	  sorec ((na1,na2,t2)::stk)
            (add_binders na1 na2 (sorec stk subst c1 c2)) d1 d2

      | PIf (a1,b1,b1'), Case (ci,_,a2,[|b2;b2'|]) ->
	  let ctx,b2 = decompose_lam_n_assum ci.ci_cstr_ndecls.(0) b2 in
	  let ctx',b2' = decompose_lam_n_assum ci.ci_cstr_ndecls.(1) b2' in
	  let n = rel_context_length ctx in
          let n' = rel_context_length ctx' in
	  if noccur_between 1 n b2 & noccur_between 1 n' b2' then
	    let s =
	      List.fold_left (fun l (na,_,t) -> (Anonymous,na,t)::l) stk ctx in
	    let s' =
	      List.fold_left (fun l (na,_,t) -> (Anonymous,na,t)::l) stk ctx' in
	    let b1 = lift_pattern n b1 and b1' = lift_pattern n' b1' in
  	    sorec s' (sorec s (sorec stk subst a1 a2) b1 b2) b1' b2'
          else
            raise PatternMatchingFailure

      | PCase (ci1,p1,a1,br1), Case (ci2,p2,a2,br2) ->
	  if same_case_structure ci1 ci2 br1 br2 then
  	    array_fold_left2 (sorec stk)
	      (sorec stk (sorec stk subst a1 a2) p1 p2) br1 br2
          else
            raise PatternMatchingFailure

      |	PFix c1, Fix _ when eq_constr (mkFix c1) cT -> subst
      |	PCoFix c1, CoFix _ when eq_constr (mkCoFix c1) cT -> subst
      | _ -> raise PatternMatchingFailure

  in
  let names,terms = sorec [] ([],[]) pat c in
  (names,Sort.list (fun (a,_) (b,_) -> a<b) terms)

let matches_core_closed convert allow_partial_app pat c =
  let names,subst = matches_core convert allow_partial_app false pat c in
  (names, List.map (fun (a,(_,b)) -> (a,b)) subst)

let extended_matches = matches_core None true true

let matches c p = snd (matches_core_closed None true c p)

let special_meta = (-1)

(* Tells if it is an authorized occurrence and if the instance is closed *)
let authorized_occ partial_app closed pat c mk_ctx next =
  try
    let sigma = matches_core_closed None partial_app pat c in
    if closed && not (List.for_all (fun (_,c) -> closed0 c) (snd sigma))
    then next ()
    else sigma, mk_ctx (mkMeta special_meta), next
  with
    PatternMatchingFailure -> next ()

(* Tries to match a subterm of [c] with [pat] *)
let sub_match ?(partial_app=false) ?(closed=true) pat c =
  let rec aux c mk_ctx next =
  match kind_of_term c with
  | Cast (c1,k,c2) ->
      authorized_occ partial_app closed pat c mk_ctx (fun () ->
        let mk_ctx lc = mk_ctx (mkCast (List.hd lc, k,c2)) in
        try_aux [c1] mk_ctx next)
  | Lambda (x,c1,c2) ->
      authorized_occ partial_app closed pat c mk_ctx (fun () ->
        let mk_ctx lc = mk_ctx (mkLambda (x,List.hd lc,List.nth lc 1)) in
        try_aux [c1;c2] mk_ctx next)
  | Prod (x,c1,c2) ->
      authorized_occ partial_app closed pat c mk_ctx (fun () ->
        let mk_ctx lc = mk_ctx (mkProd (x,List.hd lc,List.nth lc 1)) in
        try_aux [c1;c2] mk_ctx next)
  | LetIn (x,c1,t,c2) ->
      authorized_occ partial_app closed pat c mk_ctx (fun () ->
        let mk_ctx = function [c1;c2] -> mkLetIn (x,c1,t,c2) | _ -> assert false
        in try_aux [c1;c2] mk_ctx next)
  | App (c1,lc) ->
      authorized_occ partial_app closed pat c mk_ctx (fun () ->
        let topdown = true in
	if partial_app then
          if topdown then
            let lc1 = Array.sub lc 0 (Array.length lc - 1) in
            let app = mkApp (c1,lc1) in
            let mk_ctx = function
              | [app';c] -> mk_ctx (mkApp (app',[|c|]))
              | _ -> assert false in
	    try_aux [app;array_last lc] mk_ctx next
          else
            let rec aux2 app args next =
              match args with
              | [] ->
                  let mk_ctx le =
                    mk_ctx (mkApp (List.hd le, Array.of_list (List.tl le))) in
	          try_aux (c1::Array.to_list lc) mk_ctx next
	      | arg :: args ->
                  let app = mkApp (app,[|arg|]) in
                  let next () = aux2 app args next in
                  let mk_ctx ce = mk_ctx (mkApp (ce, Array.of_list args)) in
                  aux app mk_ctx next in
            aux2 c1 (Array.to_list lc) next
        else
          let mk_ctx le =
            mk_ctx (mkApp (List.hd le, Array.of_list (List.tl le))) in
	  try_aux (c1::Array.to_list lc) mk_ctx next)
  | Case (ci,hd,c1,lc) ->
      authorized_occ partial_app closed pat c mk_ctx (fun () ->
        let mk_ctx le =
          mk_ctx (mkCase (ci,hd,List.hd le,Array.of_list (List.tl le))) in
        try_aux (c1::Array.to_list lc) mk_ctx next)
  | Construct _ | Fix _ | Ind _|CoFix _ |Evar _|Const _
  | Rel _|Meta _|Var _|Sort _ ->
      authorized_occ partial_app closed pat c mk_ctx next

  (* Tries [sub_match] for all terms in the list *)
  and try_aux lc mk_ctx next =
    let rec try_sub_match_rec lacc = function
      | [] -> next ()
      | c::tl ->
          let mk_ctx ce = mk_ctx (List.rev_append lacc (ce::tl)) in
          let next () = try_sub_match_rec (c::lacc) tl in
          aux c mk_ctx next in
    try_sub_match_rec [] lc in
  aux c (fun x -> x) (fun () -> raise PatternMatchingFailure)

type subterm_matching_result =
    (bound_ident_map * patvar_map) * constr * (unit -> subterm_matching_result)

let match_subterm pat c = sub_match pat c

let match_appsubterm pat c = sub_match ~partial_app:true pat c

let match_subterm_gen app pat c = sub_match ~partial_app:app pat c

let is_matching pat c =
  try let _ = matches pat c in true
  with PatternMatchingFailure -> false

let is_matching_appsubterm ?(closed=true) pat c =
  try let _ = sub_match ~partial_app:true ~closed pat c in true
  with PatternMatchingFailure -> false

let matches_conv env sigma c p =
  snd (matches_core_closed (Some (env,sigma)) false c p)

let is_matching_conv env sigma pat n =
  try let _ = matches_conv env sigma pat n in true
  with PatternMatchingFailure -> false

