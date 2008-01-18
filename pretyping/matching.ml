(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

(*i*)
open Util
open Names
open Libnames
open Nameops
open Termops
open Reductionops
open Term
open Rawterm
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

exception PatternMatchingFailure

let constrain (n,m) sigma =
  if List.mem_assoc n sigma then
    if eq_constr m (List.assoc n sigma) then sigma
    else raise PatternMatchingFailure
  else 
    (n,m)::sigma
    
let build_lambda toabstract stk (m : constr) = 
  let rec buildrec m p_0 p_1 = match p_0,p_1 with 
    | (_, []) -> m
    | (n, (na,t)::tl) -> 
	if List.mem n toabstract then
          buildrec (mkLambda (na,t,m)) (n+1) tl
        else 
	  buildrec (lift (-1) m) (n+1) tl
  in 
  buildrec m 1 stk

let memb_metavars m n =
  match (m,n) with
    | (None, _)     -> true
    | (Some mvs, n) -> List.mem n mvs

let eq_context ctxt1 ctxt2 = array_for_all2 eq_constr ctxt1 ctxt2

let same_case_structure (_,cs1,ind,_) ci2 br1 br2 =
  match ind with
  | Some ind -> ind = ci2.ci_ind
  | None -> cs1 = ci2.ci_cstr_nargs

let matches_core convert allow_partial_app pat c = 
  let rec sorec stk sigma p t =
    let cT = strip_outer_cast t in
    match p,kind_of_term cT with
      | PSoApp (n,args),m ->
	  let relargs =
	    List.map
	      (function
		 | PRel n -> n
		 | _ -> error "Only bound indices allowed in second order pattern matching")
	      args in
	  let frels = Intset.elements (free_rels cT) in
	  if list_subset frels relargs then
	    constrain (n,build_lambda relargs stk cT) sigma
	  else
	    raise PatternMatchingFailure

      | PMeta (Some n), m ->
	  let depth = List.length stk in
          if depth = 0 then
            (* Optimisation *)
            constrain (n,cT) sigma
          else
	    let frels = Intset.elements (free_rels cT) in
            if List.for_all (fun i -> i > depth) frels then
	      constrain (n,lift (-depth) cT) sigma
            else 
	      raise PatternMatchingFailure

      | PMeta None, m -> sigma

      | PRef (VarRef v1), Var v2 when v1 = v2 -> sigma

      | PVar v1, Var v2 when v1 = v2 -> sigma

      | PRef ref, _ when constr_of_global ref = cT -> sigma

      | PRel n1, Rel n2 when n1 = n2 -> sigma

      | PSort (RProp c1), Sort (Prop c2) when c1 = c2 -> sigma

      | PSort (RType _), Sort (Type _) -> sigma

      | PApp (p, [||]), _ -> sorec stk sigma p t

      | PApp (PApp (h, a1), a2), _ ->
          sorec stk sigma (PApp(h,Array.append a1 a2)) t

      | PApp (PMeta (Some n),args1), App (c2,args2) when allow_partial_app ->
          let p = Array.length args2 - Array.length args1 in
          if p>=0 then
            let args21, args22 = array_chop p args2 in
            let sigma =
	      let depth = List.length stk in
              let c = mkApp(c2,args21) in
	      let frels = Intset.elements (free_rels c) in
              if List.for_all (fun i -> i > depth) frels then
	        constrain (n,lift (-depth) c) sigma
              else
	        raise PatternMatchingFailure in
            array_fold_left2 (sorec stk) sigma args1 args22
          else raise PatternMatchingFailure

      | PApp (c1,arg1), App (c2,arg2) ->
        (try array_fold_left2 (sorec stk) (sorec stk sigma c1 c2) arg1 arg2
         with Invalid_argument _ -> raise PatternMatchingFailure)

      | PProd (na1,c1,d1), Prod(na2,c2,d2) ->
	  sorec ((na2,c2)::stk) (sorec stk sigma c1 c2) d1 d2

      | PLambda (na1,c1,d1), Lambda(na2,c2,d2) ->
	  sorec ((na2,c2)::stk) (sorec stk sigma c1 c2) d1 d2

      | PLetIn (na1,c1,d1), LetIn(na2,c2,t2,d2) ->
	  sorec ((na2,t2)::stk) (sorec stk sigma c1 c2) d1 d2

      | PRef (ConstRef _ as ref), _ when convert <> None ->
	  let (env,evars) = Option.get convert in
	  let c = constr_of_global ref in
	  if is_conv env evars c cT then sigma
	  else raise PatternMatchingFailure

      | PIf (a1,b1,b1'), Case (ci,_,a2,[|b2;b2'|]) ->
	  let ctx,b2 = decompose_lam_n_assum ci.ci_cstr_nargs.(0) b2 in
	  let ctx',b2' = decompose_lam_n_assum ci.ci_cstr_nargs.(1) b2' in
	  let n = rel_context_length ctx in
          let n' = rel_context_length ctx' in
	  if noccur_between 1 n b2 & noccur_between 1 n' b2' then
	    let s = List.fold_left (fun l (na,_,t) -> (na,t)::l) stk ctx in
	    let s' = List.fold_left (fun l (na,_,t) -> (na,t)::l) stk ctx' in
	    let b1 = lift_pattern n b1 and b1' = lift_pattern n' b1' in
  	    sorec s' (sorec s (sorec stk sigma a1 a2) b1 b2) b1' b2'
          else
            raise PatternMatchingFailure

      | PCase (ci1,p1,a1,br1), Case (ci2,p2,a2,br2) ->
	  if same_case_structure ci1 ci2 br1 br2 then
  	    array_fold_left2 (sorec stk) 
	      (sorec stk (sorec stk sigma a1 a2) p1 p2) br1 br2
          else
            raise PatternMatchingFailure

      |	PFix c1, Fix _ when eq_constr (mkFix c1) cT -> sigma
      |	PCoFix c1, CoFix _ when eq_constr (mkCoFix c1) cT -> sigma
      | _ -> raise PatternMatchingFailure

  in 
  Sort.list (fun (a,_) (b,_) -> a<b) (sorec [] [] pat c)

let matches = matches_core None false

let pmatches = matches_core None true

(* To skip to the next occurrence *)
exception NextOccurrence of int

(* Tells if it is an authorized occurrence and if the instance is closed *)
let authorized_occ nocc mres =
  if not (List.for_all (fun (_,c) -> closed0 c) (fst mres)) then
    raise PatternMatchingFailure;
  if nocc = 0 then mres
  else raise (NextOccurrence nocc)

let special_meta = (-1)

(* Tries to match a subterm of [c] with [pat] *)
let rec sub_match nocc pat c =
  match kind_of_term c with
  | Cast (c1,k,c2) ->
    (try authorized_occ nocc ((matches pat c), mkMeta special_meta) with
    | PatternMatchingFailure ->
      let (lm,lc) = try_sub_match nocc pat [c1] in
      (lm,mkCast (List.hd lc, k,c2))
    | NextOccurrence nocc ->
      let (lm,lc) = try_sub_match (nocc - 1) pat [c1] in
      (lm,mkCast (List.hd lc, k,c2)))
 | Lambda (x,c1,c2) ->
    (try authorized_occ nocc ((matches pat c), mkMeta special_meta) with
    | PatternMatchingFailure ->
      let (lm,lc) = try_sub_match nocc pat [c1;c2] in
      (lm,mkLambda (x,List.hd lc,List.nth lc 1))
    | NextOccurrence nocc ->
      let (lm,lc) = try_sub_match (nocc - 1) pat [c1;c2] in
      (lm,mkLambda (x,List.hd lc,List.nth lc 1)))
  | Prod (x,c1,c2) ->
    (try authorized_occ nocc ((matches pat c), mkMeta special_meta) with
    | PatternMatchingFailure ->
      let (lm,lc) = try_sub_match nocc pat [c1;c2] in
      (lm,mkProd (x,List.hd lc,List.nth lc 1))
    | NextOccurrence nocc ->
      let (lm,lc) = try_sub_match (nocc - 1) pat [c1;c2] in
      (lm,mkProd (x,List.hd lc,List.nth lc 1)))
  | LetIn (x,c1,t2,c2) ->
    (try authorized_occ nocc ((matches pat c), mkMeta special_meta) with
    | PatternMatchingFailure ->
      let (lm,lc) = try_sub_match nocc pat [c1;t2;c2] in
      (lm,mkLetIn (x,List.hd lc,List.nth lc 1,List.nth lc 2))
    | NextOccurrence nocc ->
      let (lm,lc) = try_sub_match (nocc - 1) pat [c1;t2;c2] in
      (lm,mkLetIn (x,List.hd lc,List.nth lc 1,List.nth lc 2)))
  | App (c1,lc) ->
    (try authorized_occ nocc ((matches pat c), mkMeta special_meta) with
    | PatternMatchingFailure ->
      let (lm,le) = try_sub_match nocc pat (c1::(Array.to_list lc)) in
      (lm,mkApp (List.hd le, Array.of_list (List.tl le)))
    | NextOccurrence nocc ->
      let (lm,le) = try_sub_match (nocc - 1) pat (c1::(Array.to_list lc)) in
      (lm,mkApp (List.hd le, Array.of_list (List.tl le))))
  | Case (ci,hd,c1,lc) ->
    (try authorized_occ nocc ((matches pat c), mkMeta special_meta) with
    | PatternMatchingFailure ->
      let (lm,le) = try_sub_match nocc pat (c1::Array.to_list lc) in
      (lm,mkCase (ci,hd,List.hd le,Array.of_list (List.tl le)))
    | NextOccurrence nocc ->
      let (lm,le) = try_sub_match (nocc - 1) pat (c1::Array.to_list lc) in
      (lm,mkCase (ci,hd,List.hd le,Array.of_list (List.tl le))))
  | Construct _ | Fix _ | Ind _|CoFix _ |Evar _|Const _
  | Rel _|Meta _|Var _|Sort _ ->
    (try authorized_occ nocc ((matches pat c),mkMeta special_meta) with
    | PatternMatchingFailure -> raise (NextOccurrence nocc)
    | NextOccurrence nocc -> raise (NextOccurrence (nocc - 1)))

(* Tries [sub_match] for all terms in the list *)
and try_sub_match nocc pat lc =
  let rec try_sub_match_rec nocc pat lacc = function
    | [] -> raise (NextOccurrence nocc)
    | c::tl ->
      (try 
         let (lm,ce) = sub_match nocc pat c in
         (lm,lacc@(ce::tl))
       with
      | NextOccurrence nocc -> try_sub_match_rec nocc pat (lacc@[c]) tl) in
  try_sub_match_rec nocc pat [] lc

let match_subterm nocc pat c =
  try sub_match nocc pat c
  with NextOccurrence _ -> raise PatternMatchingFailure

let is_matching pat n =
  try let _ = matches pat n in true
  with PatternMatchingFailure -> false

let matches_conv env sigma = matches_core (Some (env,sigma)) false

let is_matching_conv env sigma pat n =
  try let _ = matches_conv env sigma pat n in true
  with PatternMatchingFailure -> false

