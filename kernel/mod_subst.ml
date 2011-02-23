(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Created by Claudio Sacerdoti from contents of term.ml, names.ml and
   new support for constant inlining in functor application, Nov 2004 *)
(* Optimizations and bug fixes by Élie Soubiran, from Feb 2008 *)

(* This file provides types and functions for managing name
   substitution in module constructions *)

open Pp
open Util
open Names
open Term

(* For Inline, the int is an inlining level, and the constr (if present)
   is the term into which we should inline *)

type delta_hint =
  | Inline of int * constr option
  | Equiv of kernel_name

(* NB: earlier constructor Prefix_equiv of module_path
   is now stored in a separate table, see Deltamap.t below *)

module Deltamap = struct
  type t = module_path MPmap.t * delta_hint KNmap.t
  let empty = MPmap.empty, KNmap.empty
  let add_kn kn hint (mm,km) = (mm,KNmap.add kn hint km)
  let add_mp mp mp' (mm,km) = (MPmap.add mp mp' mm, km)
  let remove_mp mp (mm,km) = (MPmap.remove mp mm, km)
  let find_mp mp map = MPmap.find mp (fst map)
  let find_kn kn map = KNmap.find kn (snd map)
  let mem_mp mp map = MPmap.mem mp (fst map)
  let mem_kn kn map = KNmap.mem kn (snd map)
  let fold_kn f map i = KNmap.fold f (snd map) i
  let fold fmp fkn (mm,km) i =
    MPmap.fold fmp mm (KNmap.fold fkn km i)
  let join map1 map2 = fold add_mp add_kn map1 map2
end

type delta_resolver = Deltamap.t

let empty_delta_resolver = Deltamap.empty

module MBImap = Map.Make
  (struct
    type t = mod_bound_id
    let compare = Pervasives.compare
   end)

module Umap = struct
  type 'a t = 'a MPmap.t * 'a MBImap.t
  let empty = MPmap.empty, MBImap.empty
  let add_mbi mbi x (m1,m2) = (m1,MBImap.add mbi x m2)
  let add_mp mp x (m1,m2) = (MPmap.add mp x m1, m2)
  let find_mp mp map = MPmap.find mp (fst map)
  let find_mbi mbi map = MBImap.find mbi (snd map)
  let mem_mp mp map = MPmap.mem mp (fst map)
  let mem_mbi mbi map = MBImap.mem mbi (snd map)
  let iter_mbi f map = MBImap.iter f (snd map)
  let fold fmp fmbi (m1,m2) i =
    MPmap.fold fmp m1 (MBImap.fold fmbi m2 i)
  let join map1 map2 = fold add_mp add_mbi map1 map2
end

type substitution = (module_path * delta_resolver) Umap.t

let empty_subst = Umap.empty

let add_mbid mbid mp resolve = Umap.add_mbi mbid (mp,resolve)
let add_mp mp1 mp2 resolve = Umap.add_mp mp1 (mp2,resolve)

let map_mbid mbid mp resolve = add_mbid mbid mp resolve empty_subst
let map_mp mp1 mp2 resolve = add_mp mp1 mp2 resolve empty_subst

let add_inline_delta_resolver con lev =
  Deltamap.add_kn (user_con con) (Inline (lev,None))

let add_inline_constr_delta_resolver con lev cstr =
  Deltamap.add_kn (user_con con) (Inline (lev, Some cstr))

let add_constant_delta_resolver con =
  Deltamap.add_kn (user_con con) (Equiv (canonical_con con))

let add_mind_delta_resolver mind =
  Deltamap.add_kn (user_mind mind) (Equiv (canonical_mind mind))

let add_mp_delta_resolver mp1 mp2 =
  Deltamap.add_mp mp1 mp2

let mp_in_delta mp =
  Deltamap.mem_mp mp

let kn_in_delta kn resolver =
  try
    match Deltamap.find_kn kn resolver with
      | Equiv _ -> true
      | Inline _ -> false
  with Not_found -> false

let con_in_delta con resolver = kn_in_delta (user_con con) resolver
let mind_in_delta mind resolver = kn_in_delta (user_mind mind) resolver

let delta_of_mp resolve mp =
 try Deltamap.find_mp mp resolve with Not_found -> mp

let remove_mp_delta_resolver resolver mp =
  Deltamap.remove_mp mp resolver

let rec find_prefix resolve mp =
  let rec sub_mp = function
    | MPdot(mp,l) as mp_sup ->
	(try Deltamap.find_mp mp_sup resolve
	 with Not_found -> MPdot(sub_mp mp,l))
    | p -> Deltamap.find_mp p resolve
  in
  try sub_mp mp with Not_found -> mp

exception Change_equiv_to_inline of (int * constr)

let solve_delta_kn resolve kn =
  try
    match Deltamap.find_kn kn resolve with
      | Equiv kn1 -> kn1
      | Inline (lev, Some c) ->	raise (Change_equiv_to_inline (lev,c))
      | Inline (_, None) -> raise Not_found
  with Not_found ->
    let mp,dir,l = repr_kn kn in
    let new_mp = find_prefix resolve mp in
    if mp == new_mp then
      kn
    else
      make_kn new_mp dir l

let gen_of_delta resolve x kn fix_can =
  try
    let new_kn = solve_delta_kn resolve kn in
    if kn == new_kn then x else fix_can new_kn
  with _ -> x

let constant_of_delta resolve con =
  let kn = user_con con in
  gen_of_delta resolve con kn (constant_of_kn_equiv kn)

let constant_of_delta2 resolve con =
  let kn, kn' = canonical_con con, user_con con in
  gen_of_delta resolve con kn (constant_of_kn_equiv kn')

let mind_of_delta resolve mind =
  let kn = user_mind mind in
  gen_of_delta resolve mind kn (mind_of_kn_equiv kn)

let mind_of_delta2 resolve mind =
  let kn, kn' = canonical_mind mind, user_mind mind in
  gen_of_delta resolve mind kn (mind_of_kn_equiv kn')

let inline_of_delta inline resolver =
  match inline with
    | None -> []
    | Some inl_lev ->
      let extract kn hint l =
	match hint with
	  | Inline (lev,_) -> if lev <= inl_lev then (lev,kn)::l else l
	  | _ -> l
      in
      Deltamap.fold_kn extract resolver []

let find_inline_of_delta kn resolve =
  match Deltamap.find_kn kn resolve with
    | Inline (_,o) -> o
    | _ -> raise Not_found

let constant_of_delta_with_inline resolve con =
  let kn1,kn2 = canonical_con con,user_con con in
  try find_inline_of_delta kn2 resolve
  with Not_found ->
    try find_inline_of_delta kn1 resolve
    with Not_found -> None

let string_of_hint = function
  | Inline _ -> "inline"
  | Equiv kn -> string_of_kn kn

let debug_string_of_delta resolve =
  let kn_to_string kn hint s =
    s^", "^(string_of_kn kn)^"=>"^(string_of_hint hint)
  in
  let mp_to_string mp mp' s =
    s^", "^(string_of_mp mp)^"=>"^(string_of_mp mp')
  in
  Deltamap.fold mp_to_string kn_to_string resolve ""

let list_contents sub =
  let one_pair (mp,reso) = (string_of_mp mp,debug_string_of_delta reso) in
  let mp_one_pair mp0 p l = (string_of_mp mp0, one_pair p)::l in
  let mbi_one_pair mbi p l = (debug_string_of_mbid mbi, one_pair p)::l in
  Umap.fold mp_one_pair mbi_one_pair sub []

let debug_string_of_subst sub =
  let l = List.map (fun (s1,(s2,s3)) -> s1^"|->"^s2^"["^s3^"]")
    (list_contents sub)
  in
  "{" ^ String.concat "; " l ^ "}"

let debug_pr_delta resolve =
  str (debug_string_of_delta resolve)

let debug_pr_subst sub =
  let l = list_contents sub in
  let f (s1,(s2,s3)) = hov 2 (str s1 ++ spc () ++ str "|-> " ++ str s2 ++
			      spc () ++ str "[" ++ str s3 ++ str "]")
  in
  str "{" ++ hov 2 (prlist_with_sep pr_comma f l) ++ str "}"

let subst_mp0 sub mp = (* 's like subst *)
 let rec aux mp =
  match mp with
    | MPfile sid -> Umap.find_mp mp sub
    | MPbound bid ->
	begin
	  try Umap.find_mbi bid sub
	  with Not_found -> Umap.find_mp mp sub
	end
    | MPdot (mp1,l) as mp2 ->
	begin
	  try Umap.find_mp mp2 sub
	  with Not_found ->
	    let mp1',resolve = aux mp1 in
	    MPdot (mp1',l),resolve
	end
 in
 try Some (aux mp) with Not_found -> None

let subst_mp sub mp =
 match subst_mp0 sub mp with
    None -> mp
  | Some (mp',_) -> mp'

let subst_kn_delta sub kn =
 let mp,dir,l = repr_kn kn in
  match subst_mp0 sub mp with
     Some (mp',resolve) ->
      solve_delta_kn resolve (make_kn mp' dir l)
   | None -> kn


let subst_kn sub kn =
 let mp,dir,l = repr_kn kn in
  match subst_mp0 sub mp with
     Some (mp',_) ->
      (make_kn mp' dir l)
   | None -> kn

exception No_subst

type sideconstantsubst =
  | User
  | Canonical

let gen_subst_mp f sub mp1 mp2 =
  match subst_mp0 sub mp1, subst_mp0 sub mp2 with
    | None, None -> raise No_subst
    | Some (mp',resolve), None -> User, (f mp' mp2), resolve
    | None, Some (mp',resolve) -> Canonical, (f mp1 mp'), resolve
    | Some (mp1',_), Some (mp2',resolve2) -> Canonical, (f mp1' mp2'), resolve2

let subst_ind sub mind =
  let kn1,kn2 = user_mind mind, canonical_mind mind in
  let mp1,dir,l = repr_kn kn1 in
  let mp2,_,_ = repr_kn kn2 in
  let rebuild_mind mp1 mp2 = make_mind_equiv mp1 mp2 dir l in
  try
    let side,mind',resolve = gen_subst_mp rebuild_mind sub mp1 mp2 in
    match side with
      | User -> mind_of_delta resolve mind'
      | Canonical -> mind_of_delta2 resolve mind'
  with No_subst -> mind

let subst_con sub con =
  let kn1,kn2 = user_con con,canonical_con con in
  let mp1,dir,l = repr_kn kn1 in
  let mp2,_,_ = repr_kn kn2 in
  let rebuild_con mp1 mp2 = make_con_equiv mp1 mp2 dir l in
  let dup con = con, mkConst con in
  try
    let side,con',resolve = gen_subst_mp rebuild_con sub mp1 mp2 in
    match constant_of_delta_with_inline resolve con' with
      | Some t -> con', t
      | None ->
	match side with
	  | User -> dup (constant_of_delta resolve con')
	  | Canonical -> dup (constant_of_delta2 resolve con')
  with No_subst -> dup con

(* Here the semantics is completely unclear.
   What does "Hint Unfold t" means when "t" is a parameter?
   Does the user mean "Unfold X.t" or does she mean "Unfold y"
   where X.t is later on instantiated with y? I choose the first
   interpretation (i.e. an evaluable reference is never expanded). *)
let subst_evaluable_reference subst = function
  | EvalVarRef id -> EvalVarRef id
  | EvalConstRef kn -> EvalConstRef (fst (subst_con subst kn))

let rec map_kn f f' c =
  let func = map_kn f f' in
    match kind_of_term c with
      | Const kn -> f' kn
      | Ind (kn,i) ->
	  let kn' = f kn in
	  if kn'==kn then c else mkInd (kn',i)
      | Construct ((kn,i),j) ->
	  let kn' = f kn in
	  if kn'==kn then c else mkConstruct ((kn',i),j)
      | Case (ci,p,ct,l) ->
	  let ci_ind =
            let (kn,i) = ci.ci_ind in
	    let kn' = f kn in
	    if kn'==kn then ci.ci_ind else kn',i
	  in
	  let p' = func p in
	  let ct' = func ct in
	  let l' = array_smartmap func l in
	    if (ci.ci_ind==ci_ind && p'==p
		&& l'==l && ct'==ct)then c
	    else
	      mkCase ({ci with ci_ind = ci_ind},
		      p',ct', l')
      | Cast (ct,k,t) ->
	  let ct' = func ct in
	  let t'= func t in
	    if (t'==t && ct'==ct) then c
	    else mkCast (ct', k, t')
      | Prod (na,t,ct) ->
	  let ct' = func ct in
	  let t'= func t in
	    if (t'==t && ct'==ct) then c
	    else mkProd (na, t', ct')
      | Lambda (na,t,ct) ->
	  let ct' = func ct in
	  let t'= func t in
	    if (t'==t && ct'==ct) then c
	    else mkLambda (na, t', ct')
      | LetIn (na,b,t,ct) ->
	  let ct' = func ct in
	  let t'= func t in
	  let b'= func b in
	    if (t'==t && ct'==ct && b==b') then c
	    else mkLetIn (na, b', t', ct')
      | App (ct,l) ->
	  let ct' = func ct in
	  let l' = array_smartmap func l in
	    if (ct'== ct && l'==l) then c
	    else mkApp (ct',l')
      | Evar (e,l) ->
	  let l' = array_smartmap func l in
	    if (l'==l) then c
	    else mkEvar (e,l')
      | Fix (ln,(lna,tl,bl)) ->
	  let tl' = array_smartmap func tl in
	  let bl' = array_smartmap func bl in
	    if (bl == bl'&& tl == tl') then c
	    else mkFix (ln,(lna,tl',bl'))
      | CoFix(ln,(lna,tl,bl)) ->
	  let tl' = array_smartmap func tl in
	  let bl' = array_smartmap func bl in
	    if (bl == bl'&& tl == tl') then c
	    else mkCoFix (ln,(lna,tl',bl'))
      | _ -> c

let subst_mps sub =
  map_kn (subst_ind sub) (fun con -> snd (subst_con sub con))

let rec replace_mp_in_mp mpfrom mpto mp =
  match mp with
    | _ when mp = mpfrom -> mpto
    | MPdot (mp1,l) ->
	let mp1' = replace_mp_in_mp mpfrom mpto mp1 in
	  if mp1==mp1' then mp
	  else MPdot (mp1',l)
    | _ -> mp

let replace_mp_in_kn mpfrom mpto kn =
 let mp,dir,l = repr_kn kn in
  let mp'' = replace_mp_in_mp mpfrom mpto mp in
    if mp==mp'' then kn
    else make_kn mp'' dir l

let rec mp_in_mp mp mp1 =
  match mp1 with
    | _ when mp1 = mp -> true
    | MPdot (mp2,l) -> mp_in_mp mp mp2
    | _ -> false

let subset_prefixed_by mp resolver =
  let mp_prefix mkey mequ rslv =
    if mp_in_mp mp mkey then Deltamap.add_mp mkey mequ rslv else rslv
  in
  let kn_prefix kn hint rslv =
    match hint with
      | Inline _ -> rslv
      | Equiv _ ->
	if mp_in_mp mp (modpath kn) then Deltamap.add_kn kn hint rslv else rslv
  in
  Deltamap.fold mp_prefix kn_prefix resolver empty_delta_resolver

let subst_dom_delta_resolver subst resolver =
  let mp_apply_subst mkey mequ rslv =
    Deltamap.add_mp (subst_mp subst mkey) mequ rslv
  in
  let kn_apply_subst kkey hint rslv =
    Deltamap.add_kn (subst_kn subst kkey) hint rslv
  in
  Deltamap.fold mp_apply_subst kn_apply_subst resolver empty_delta_resolver

let subst_mp_delta sub mp mkey =
 match subst_mp0 sub mp with
    None -> empty_delta_resolver,mp
  | Some (mp',resolve) ->
      let mp1 = find_prefix resolve mp' in
      let resolve1 = subset_prefixed_by mp1 resolve in
      (subst_dom_delta_resolver
	 (map_mp mp1 mkey empty_delta_resolver) resolve1),mp1

let gen_subst_delta_resolver dom subst resolver =
  let mp_apply_subst mkey mequ rslv =
    let mkey' = if dom then subst_mp subst mkey else mkey in
    let rslv',mequ' = subst_mp_delta subst mequ mkey in
    Deltamap.join rslv' (Deltamap.add_mp mkey' mequ' rslv)
  in
  let kn_apply_subst kkey hint rslv =
    let kkey' = if dom then subst_kn subst kkey else kkey in
    let hint' = match hint with
      | Equiv kequ ->
	  (try Equiv (subst_kn_delta subst kequ)
	   with Change_equiv_to_inline (lev,c) -> Inline (lev,Some c))
      | Inline (lev,Some t) -> Inline (lev,Some (subst_mps subst t))
      | Inline (_,None) -> hint
    in
    Deltamap.add_kn kkey' hint' rslv
  in
  Deltamap.fold mp_apply_subst kn_apply_subst resolver empty_delta_resolver

let subst_codom_delta_resolver = gen_subst_delta_resolver false
let subst_dom_codom_delta_resolver = gen_subst_delta_resolver true

let update_delta_resolver resolver1 resolver2 =
  let mp_apply_rslv mkey mequ rslv =
    if Deltamap.mem_mp mkey resolver2 then rslv
    else Deltamap.add_mp mkey (find_prefix resolver2 mequ) rslv
  in
  let kn_apply_rslv kkey hint rslv =
    if Deltamap.mem_kn kkey resolver2 then rslv
    else
      let hint' = match hint with
	| Equiv kequ ->
	  (try Equiv (solve_delta_kn resolver2 kequ)
	   with Change_equiv_to_inline (lev,c) -> Inline (lev, Some c))
	| _ -> hint
      in
      Deltamap.add_kn kkey hint' rslv
  in
  Deltamap.fold mp_apply_rslv kn_apply_rslv resolver1 empty_delta_resolver

let add_delta_resolver resolver1 resolver2 =
  if resolver1 == resolver2 then
    resolver2
  else if resolver2 = empty_delta_resolver then
    resolver1
  else
    Deltamap.join (update_delta_resolver resolver1 resolver2) resolver2

let substition_prefixed_by k mp subst =
  let mp_prefixmp kmp (mp_to,reso) sub =
    if mp_in_mp mp kmp && mp <> kmp then
      let new_key = replace_mp_in_mp mp k kmp in
      Umap.add_mp new_key (mp_to,reso) sub
    else sub
  in
  let mbi_prefixmp mbi _ sub = sub
  in
  Umap.fold mp_prefixmp mbi_prefixmp subst empty_subst

let join subst1 subst2 =
  let apply_subst mpk add (mp,resolve) res =
    let mp',resolve' =
      match subst_mp0 subst2 mp with
	| None -> mp, None
	| Some (mp',resolve') ->  mp', Some resolve' in
    let resolve'' =
      match resolve' with
        | Some res ->
	    add_delta_resolver
	      (subst_dom_codom_delta_resolver subst2 resolve) res
	| None ->
	    subst_codom_delta_resolver subst2 resolve
    in
    let prefixed_subst = substition_prefixed_by mpk mp' subst2 in
    Umap.join prefixed_subst (add (mp',resolve'') res)
  in
  let mp_apply_subst mp = apply_subst mp (Umap.add_mp mp) in
  let mbi_apply_subst mbi = apply_subst (MPbound mbi) (Umap.add_mbi mbi) in
  let subst = Umap.fold mp_apply_subst mbi_apply_subst subst1 empty_subst in
  Umap.join subst2 subst

let rec occur_in_path mbi = function
  | MPbound bid' -> mbi = bid'
  | MPdot (mp1,_) -> occur_in_path mbi mp1
  | _ -> false

let occur_mbid mbi sub =
  let check_one mbi' (mp,_) =
    if mbi = mbi' || occur_in_path mbi mp then raise Exit
  in
  try
    Umap.iter_mbi check_one sub;
    false
  with Exit -> true

type 'a lazy_subst =
  | LSval of 'a
  | LSlazy of substitution list * 'a

type 'a substituted = 'a lazy_subst ref

let from_val a = ref (LSval a)

let force fsubst r =
  match !r with
  | LSval a -> a
  | LSlazy(s,a) ->
      let subst = List.fold_left join empty_subst (List.rev s) in
      let a' = fsubst subst a in
      r := LSval a';
      a'

let subst_substituted s r =
  match !r with
    | LSval a -> ref (LSlazy([s],a))
    | LSlazy(s',a) ->
	  ref (LSlazy(s::s',a))

