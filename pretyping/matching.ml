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

let matches_core convert allow_partial_app pat c = 
  let rec sorec stk sigma p t =
    let cT = strip_outer_cast t in
    match p,kind_of_term cT with
      | PSoApp (n,args),m ->
	  let relargs =
	    List.map
	      (function
		 | PRel n -> n
		 | _ -> error "Only bound indices are currently allowed in second order pattern matching")
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

      | PRef ref, _ when constr_of_reference ref = cT -> sigma

      | PRel n1, Rel n2 when n1 = n2 -> sigma

      | PSort (RProp c1), Sort (Prop c2) when c1 = c2 -> sigma

      | PSort (RType _), Sort (Type _) -> sigma

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
	  let (env,evars) = out_some convert in
	  let c = constr_of_reference ref in
	  if is_conv env evars c cT then sigma
	  else raise PatternMatchingFailure

      | PCase (_,_,a1,br1), Case (_,_,a2,br2) ->
	  (* On ne teste pas le prédicat *)
          if (Array.length br1) = (Array.length br2) then
  	    array_fold_left2 (sorec stk) (sorec stk sigma a1 a2) br1 br2
          else
            raise PatternMatchingFailure
      (* À faire *)
      |	PFix f0, Fix f1 when f0 = f1 -> sigma
      |	PCoFix c0, CoFix c1 when c0 = c1 -> sigma
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
  | Cast (c1,c2) ->
    (try authorized_occ nocc ((matches pat c), mkMeta special_meta) with
    | PatternMatchingFailure ->
      let (lm,lc) = try_sub_match nocc pat [c1] in
      (lm,mkCast (List.hd lc, c2))
    | NextOccurrence nocc ->
      let (lm,lc) = try_sub_match (nocc - 1) pat [c1] in
      (lm,mkCast (List.hd lc, c2)))
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

let is_matching pat n =
  try let _ = matches pat n in true
  with PatternMatchingFailure -> false

let matches_conv env sigma = matches_core (Some (env,sigma)) false

let is_matching_conv env sigma pat n =
  try let _ = matches_conv env sigma pat n in true
  with PatternMatchingFailure -> false

