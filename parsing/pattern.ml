
(* $Id$ *)

open Util
(* open Generic *)
open Names
open Term
open Reduction
open Rawterm

type constr_pattern =
  | PRef of Term.constr array reference
  | PRel of int
  | PApp of constr_pattern * constr_pattern array
  | PSoApp of int * constr_pattern list
  | PBinder of binder_kind * name * constr_pattern * constr_pattern
  | PSort of rawsort
  | PMeta of int option
  | PCase of constr_pattern option * constr_pattern * constr_pattern array
(*i
  | Prec of loc * fix_kind * identifier array * 
      constr_pattern array * constr_pattern array
i*)

let rec occur_meta_pattern = function
  | PApp (f,args) ->
      (occur_meta_pattern f) or (array_exists occur_meta_pattern args)
  | PBinder(_,na,t,c)  -> (occur_meta_pattern t) or (occur_meta_pattern c)
  | PCase(None,c,br)   ->
      (occur_meta_pattern c) or (array_exists occur_meta_pattern br)
  | PCase(Some p,c,br) ->
      (occur_meta_pattern p) or
      (occur_meta_pattern c) or (array_exists occur_meta_pattern br)
  | PMeta _ | PSoApp _ -> true
  | PRel _ | PSort _   -> false

  (* On suppose que les ctxt des cstes ne contient pas de meta *)
  | PRef _             -> false

type constr_label =
  | ConstNode of section_path
  | IndNode of inductive_path
  | CstrNode of constructor_path
  | VarNode of identifier
(*
  | ... 
*)

exception BoundPattern;;

let label_of_ref = function
  | RConst (sp,_)     -> ConstNode sp
  | RInd (sp,_)       -> IndNode sp
  | RConstruct (sp,_) -> CstrNode sp
  | RVar id           -> VarNode id
  | REVar _           -> raise BoundPattern

let rec head_pattern_bound t =
  match t with
    | PBinder ((BProd|BLetIn),_,_,b) -> head_pattern_bound b 
    | PApp (c,args)         -> head_pattern_bound c
    | PCase (p,c,br)        -> head_pattern_bound c
    | PRef r                -> label_of_ref r
    | PRel _ | PMeta _ | PSoApp _  | PSort _ -> raise BoundPattern
    | PBinder(BLambda,_,_,_) -> anomaly "head_pattern_bound: not a type"

let head_of_constr_reference c = match kind_of_term c with
  | IsConst (sp,_) -> ConstNode sp
  | IsMutConstruct (sp,_) -> CstrNode sp
  | IsMutInd (sp,_) -> IndNode sp
  | IsVar id -> VarNode id
  | _ -> anomaly "Not a rigid reference"


(* Second part : Given a term with second-order variables in it,
   represented by Meta's, and possibly applied using XTRA[$SOAPP] to
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

let constrain ((n : int),(m : constr)) sigma =
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
	  buildrec (pop m) (n+1) tl
  in 
  buildrec m 1 stk

let memb_metavars m n =
  match (m,n) with
    | (None, _)     -> true
    | (Some mvs, n) -> List.mem n mvs

let eq_context ctxt1 ctxt2 = array_for_all2 eq_constr ctxt1 ctxt2

let matches_core convert pat c = 
  let rec sorec stk sigma p t =
    let cT = whd_castapp t in
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
	  let frels = Intset.elements (free_rels cT) in
          if List.for_all (fun i -> i > depth) frels then
	    constrain (n,lift (-depth) cT) sigma
          else 
	    raise PatternMatchingFailure

      | PMeta None, m -> sigma

      | PRef (RVar v1), IsVar v2 when v1 = v2 -> sigma

      | PRef (RConst (sp1,ctxt1)), IsConst (sp2,ctxt2) 
	  when sp1 = sp2 && eq_context ctxt1 ctxt2 -> sigma

      | PRef (RInd (sp1,ctxt1)), IsMutInd (sp2,ctxt2) 
	  when sp1 = sp2 && eq_context ctxt1 ctxt2 -> sigma

      | PRef (RConstruct (sp1,ctxt1)), IsMutConstruct (sp2,ctxt2) 
	  when sp1 = sp2 && eq_context ctxt1 ctxt2 -> sigma

      | PRel n1, IsRel n2 when n1 = n2 -> sigma

      | PSort (RProp c1), IsSort (Prop c2) when c1 = c2 -> sigma

      | PSort RType, IsSort (Type _) -> sigma

      | PApp (c1,arg1), IsAppL (c2,arg2) ->
	  array_fold_left2 (sorec stk) (sorec stk sigma c1 c2) arg1 arg2

      | PBinder(BProd,na1,c1,d1), IsProd(na2,c2,d2) ->
	  sorec ((na2,c2)::stk) (sorec stk sigma c1 c2) d1 d2

      | PBinder(BLambda,na1,c1,d1), IsLambda(na2,c2,d2) ->
	  sorec ((na2,c2)::stk) (sorec stk sigma c1 c2) d1 d2

      | PBinder(BLetIn,na1,c1,d1), IsLetIn(na2,c2,t2,d2) ->
	  sorec ((na2,t2)::stk) (sorec stk sigma c1 c2) d1 d2

      | PRef (RConst (sp1,ctxt1)), IsConst (sp2,ctxt2) 
          when sp1 = sp2 && eq_context ctxt1 ctxt2 -> sigma

      | PRef (RConst (sp1,ctxt1)), _ when convert <> None ->
	  let (env,evars) = out_some convert in
	  if is_conv env evars (mkConst (sp1,ctxt1)) cT then sigma
	  else raise PatternMatchingFailure

      | PCase (_,a1,br1), IsMutCase (_,_,a2,br2) ->
	  (* On ne teste pas le prédicat *)
	  array_fold_left2 (sorec stk) (sorec stk sigma a1 a2)
	    br1 br2

      | _,(IsFix _ | IsCoFix _) ->
	  error "somatch: not implemented"

      | _ -> raise PatternMatchingFailure

  in 
  Sort.list (fun (a,_) (b,_) -> a<b) (sorec [] [] pat c)

let matches = matches_core None

(* To skip to the next occurrence *)
exception NextOccurrence of int

(* Tells if it is an authorized occurrence *)
let authorized_occ nocc mres =
  if nocc = 0 then mres
  else raise (NextOccurrence nocc)

(* Tries matches according to the occurrence *)
let rec try_matches nocc pat = function
  | [] -> raise (NextOccurrence nocc)
  | c::tl ->
    (try authorized_occ nocc (matches pat c) with
    | PatternMatchingFailure -> (try_matches nocc pat tl)
    | NextOccurrence nocc -> (try_matches (nocc - 1) pat tl))

(* Tries to match a subterm of [c] with [pat] *)
let rec sub_match nocc pat c =
  match kind_of_term c with
  | IsCast (c1,c2) ->
    (try authorized_occ nocc ((matches pat c), mkMeta (-1)) with
    | PatternMatchingFailure ->
      let (lm,lc) = try_sub_match nocc pat [c1] in
      (lm,mkCast (List.hd lc, c2))
    | NextOccurrence nocc ->
      let (lm,lc) = try_sub_match (nocc - 1) pat [c1] in
      (lm,mkCast (List.hd lc, c2)))
  | IsLambda (x,c1,c2) ->
    (try authorized_occ nocc ((matches pat c), mkMeta (-1)) with
    | PatternMatchingFailure ->
      let (lm,lc) = try_sub_match nocc pat [c1;c2] in
      (lm,mkLambda (x,List.hd lc,List.nth lc 1))
    | NextOccurrence nocc ->
      let (lm,lc) = try_sub_match (nocc - 1) pat [c1;c2] in
      (lm,mkLambda (x,List.hd lc,List.nth lc 1)))
  | IsProd (x,c1,c2) ->
    (try authorized_occ nocc ((matches pat c), mkMeta (-1)) with
    | PatternMatchingFailure ->
      let (lm,lc) = try_sub_match nocc pat [c1;c2] in
      (lm,mkProd (x,List.hd lc,List.nth lc 1))
    | NextOccurrence nocc ->
      let (lm,lc) = try_sub_match (nocc - 1) pat [c1;c2] in
      (lm,mkProd (x,List.hd lc,List.nth lc 1)))
  | IsLetIn (x,c1,t2,c2) ->
    (try authorized_occ nocc ((matches pat c), mkMeta (-1)) with
    | PatternMatchingFailure ->
      let (lm,lc) = try_sub_match nocc pat [c1;t2;c2] in
      (lm,mkLetIn (x,List.hd lc,List.nth lc 1,List.nth lc 2))
    | NextOccurrence nocc ->
      let (lm,lc) = try_sub_match (nocc - 1) pat [c1;t2;c2] in
      (lm,mkLetIn (x,List.hd lc,List.nth lc 1,List.nth lc 2)))
  | IsAppL (c1,lc) ->
    (try authorized_occ nocc ((matches pat c), mkMeta (-1)) with
    | PatternMatchingFailure ->
      let (lm,le) = try_sub_match nocc pat (c1::(Array.to_list lc)) in
      (lm,mkAppList le)
    | NextOccurrence nocc ->
      let (lm,le) = try_sub_match (nocc - 1) pat (c1::(Array.to_list lc)) in
      (lm,mkAppList le))
  | IsMutCase (ci,hd,c1,lc) ->
    (try authorized_occ nocc ((matches pat c), mkMeta (-1)) with
    | PatternMatchingFailure ->
      let (lm,le) = try_sub_match nocc pat (c1::Array.to_list lc) in
      (lm,mkMutCaseL (ci,hd,List.hd le,List.tl le))
    | NextOccurrence nocc ->
      let (lm,le) = try_sub_match (nocc - 1) pat (c1::Array.to_list lc) in
      (lm,mkMutCaseL (ci,hd,List.hd le,List.tl le)))
  | IsMutConstruct _ | IsFix _ | IsMutInd _|IsCoFix _ |IsEvar _|IsConst _
  | IsRel _|IsMeta _|IsVar _|IsXtra _|IsSort _ ->
    (try authorized_occ nocc ((matches pat c),mkMeta (-1)) with
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

let matches_conv env sigma = matches_core (Some (env,sigma))

let is_matching_conv env sigma pat n =
  try let _ = matches_conv env sigma pat n in true
  with PatternMatchingFailure -> false

let rec pattern_of_constr t =
  match kind_of_term t with
    | IsRel n  -> PRel n
    | IsMeta n -> PMeta (Some n)
    | IsVar id -> PRef (RVar id)
    | IsSort (Prop c) -> PSort (RProp c)
    | IsSort (Type _) -> PSort RType
    | IsCast (c,_)      -> pattern_of_constr c
    | IsLetIn (na,c,_,b)   ->
	PBinder (BLetIn,na,pattern_of_constr c,pattern_of_constr b)
    | IsProd (na,c,b)   ->
	PBinder (BProd,na,pattern_of_constr c,pattern_of_constr b)
    | IsLambda (na,c,b) ->
	PBinder (BLambda,na,pattern_of_constr c,pattern_of_constr b)
    | IsAppL (f,args)   ->
	PApp (pattern_of_constr f, Array.map pattern_of_constr args)
    | IsConst (cst_sp,ctxt)         ->
	PRef (RConst (cst_sp, ctxt))
    | IsMutInd (ind_sp,ctxt)        ->
	PRef (RInd (ind_sp, ctxt))
    | IsMutConstruct (cstr_sp,ctxt) ->
	PRef (RConstruct (cstr_sp, ctxt))
    | IsEvar (n,ctxt) ->
	PRef (REVar (n,ctxt))
    | IsMutCase (ci,p,a,br) ->
	PCase (Some (pattern_of_constr p),pattern_of_constr a,
	       Array.map pattern_of_constr br)
    | IsFix _ | IsCoFix _ ->
	error "pattern_of_constr: (co)fix currently not supported"
    | IsXtra _   -> anomaly "No longer supported"
