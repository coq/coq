(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Created by Claudio Sacerdoti from contents of term.ml, names.ml and
   new support for constant inlining in functor application, Nov 2004 *)
(* Optimizations and bug fixes by Élie Soubiran, from Feb 2008 *)

(* This file provides types and functions for managing name
   substitution in module constructions *)

open Pp
open Util
open Names
open Constr

(* For Inline, the int is an inlining level, and the constr (if present)
   is the term into which we should inline. *)

type delta_hint =
  | Inline of int * constr Univ.univ_abstracted option
  | Equiv of KerName.t

(* NB: earlier constructor Prefix_equiv of ModPath.t
   is now stored in a separate table, see Deltamap.t below *)

module Deltamap = struct
  type t = ModPath.t MPmap.t * delta_hint KNmap.t
  let empty = MPmap.empty, KNmap.empty
  let is_empty (mm, km) =
    MPmap.is_empty mm && KNmap.is_empty km
  let add_kn kn hint (mm,km) = (mm,KNmap.add kn hint km)
  let add_mp mp mp' (mm,km) = (MPmap.add mp mp' mm, km)
  let find_mp mp map = MPmap.find mp (fst map)
  let find_kn kn map = KNmap.find kn (snd map)
  let mem_mp mp map = MPmap.mem mp (fst map)
  let fold_kn f map i = KNmap.fold f (snd map) i
  let fold fmp fkn (mm,km) i =
    MPmap.fold fmp mm (KNmap.fold fkn km i)
  let join map1 map2 = fold add_mp add_kn map1 map2
end

(* Invariant: in the [delta_hint] map, an [Equiv] should only
   relate [KerName.t] with the same label (and section dirpath). *)

type delta_resolver = Deltamap.t

let empty_delta_resolver = Deltamap.empty

module Umap :
  sig
    type 'a t
    val empty : 'a t
    val is_empty : 'a t -> bool
    val add_mbi : MBId.t -> 'a -> 'a t -> 'a t
    val add_mp : ModPath.t -> 'a -> 'a t -> 'a t
    val find : ModPath.t -> 'a t -> 'a
    val join : 'a t -> 'a t -> 'a t
    val fold : (ModPath.t -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
  end = struct
  type 'a t = 'a MPmap.t
  let empty = MPmap.empty
  let is_empty m = MPmap.is_empty m
  let add_mbi mbi x m = MPmap.add (MPbound mbi) x m
  let add_mp mp x m = MPmap.add mp x m
  let find = MPmap.find
  let fold = MPmap.fold
  let join map1 map2 = fold add_mp map1 map2
end

type substitution = (ModPath.t * delta_resolver) Umap.t

let empty_subst = Umap.empty

let is_empty_subst = Umap.is_empty

(* <debug> *)

let string_of_hint = function
  | Inline (_,Some _) -> "inline(Some _)"
  | Inline _ -> "inline()"
  | Equiv kn -> KerName.to_string kn

let debug_string_of_delta resolve =
  let kn_to_string kn hint l =
    (KerName.to_string kn ^ "=>" ^ string_of_hint hint) :: l
  in
  let mp_to_string mp mp' l =
    (ModPath.to_string mp ^ "=>" ^ ModPath.to_string mp') :: l
  in
  let l = Deltamap.fold mp_to_string kn_to_string resolve [] in
  String.concat ", " (List.rev l)

let list_contents sub =
  let one_pair (mp,reso) = (ModPath.to_string mp,debug_string_of_delta reso) in
  let mp_one_pair mp0 p l = (ModPath.to_string mp0, one_pair p)::l in
  Umap.fold mp_one_pair sub []

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

(* </debug> *)

(** Extending a [delta_resolver] *)

let add_inline_delta_resolver kn (lev,oc) = Deltamap.add_kn kn (Inline (lev,oc))

let add_kn_delta_resolver kn kn' =
  assert (Label.equal (KerName.label kn) (KerName.label kn'));
  Deltamap.add_kn kn (Equiv kn')

let add_mp_delta_resolver mp1 mp2 = Deltamap.add_mp mp1 mp2

(** Extending a [substitution] without sequential composition *)

let add_mbid mbid mp resolve s = Umap.add_mbi mbid (mp,resolve) s
let add_mp mp1 mp2 resolve s = Umap.add_mp mp1 (mp2,resolve) s

let map_mbid mbid mp resolve = add_mbid mbid mp resolve empty_subst
let map_mp mp1 mp2 resolve = add_mp mp1 mp2 resolve empty_subst

let mp_in_delta mp = Deltamap.mem_mp mp

let kn_in_delta kn resolver =
  try
    match Deltamap.find_kn kn resolver with
      | Equiv _ -> true
      | Inline _ -> false
  with Not_found -> false

let con_in_delta con resolver = kn_in_delta (Constant.user con) resolver
let mind_in_delta mind resolver = kn_in_delta (MutInd.user mind) resolver

let mp_of_delta resolve mp =
 try Deltamap.find_mp mp resolve with Not_found -> mp

let find_prefix resolve mp =
  let rec sub_mp = function
    | MPdot(mp,l) as mp_sup ->
	(try Deltamap.find_mp mp_sup resolve
	 with Not_found -> MPdot(sub_mp mp,l))
    | p -> Deltamap.find_mp p resolve
  in
  try sub_mp mp with Not_found -> mp

(** Applying a resolver to a kernel name *)

exception Change_equiv_to_inline of (int * constr Univ.univ_abstracted)

let solve_delta_kn resolve kn =
  try
    match Deltamap.find_kn kn resolve with
      | Equiv kn1 -> kn1
      | Inline (lev, Some c) ->	raise (Change_equiv_to_inline (lev,c))
      | Inline (_, None) -> raise Not_found
  with Not_found ->
    let mp,l = KerName.repr kn in
    let new_mp = find_prefix resolve mp in
    if mp == new_mp then
      kn
    else
      KerName.make new_mp l

let kn_of_delta resolve kn =
  try solve_delta_kn resolve kn
  with Change_equiv_to_inline _ -> kn

(** Try a 1st resolver, and then a 2nd in case it had no effect *)

let kn_of_deltas resolve1 resolve2 kn =
  let kn' = kn_of_delta resolve1 kn in
  if kn' == kn then kn_of_delta resolve2 kn else kn'

let constant_of_delta_kn resolve kn =
  Constant.make kn (kn_of_delta resolve kn)

let constant_of_deltas_kn resolve1 resolve2 kn =
  Constant.make kn (kn_of_deltas resolve1 resolve2 kn)

let mind_of_delta_kn resolve kn =
  MutInd.make kn (kn_of_delta resolve kn)

let mind_of_deltas_kn resolve1 resolve2 kn =
  MutInd.make kn (kn_of_deltas resolve1 resolve2 kn)

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

let search_delta_inline resolve kn1 kn2 =
  let find kn = match Deltamap.find_kn kn resolve with
    | Inline (_,o) -> o
    | Equiv _ -> raise Not_found
  in
  try find kn1
  with Not_found ->
    if kn1 == kn2 then None
    else
      try find kn2
      with Not_found -> None

let subst_mp0 sub mp = (* 's like subst *)
 let rec aux mp =
  match mp with
    | MPfile _ | MPbound _ -> Umap.find mp sub
    | MPdot (mp1,l) as mp2 ->
	begin
          try Umap.find mp2 sub
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
 let mp,l = KerName.repr kn in
  match subst_mp0 sub mp with
     Some (mp',resolve) ->
      solve_delta_kn resolve (KerName.make mp' l)
   | None -> kn


let subst_kn sub kn =
 let mp,l = KerName.repr kn in
  match subst_mp0 sub mp with
     Some (mp',_) ->
      (KerName.make mp' l)
   | None -> kn

exception No_subst

let subst_dual_mp sub mp1 mp2 =
  let o1 = subst_mp0 sub mp1 in
  let o2 = if mp1 == mp2 then o1 else subst_mp0 sub mp2 in
  match o1, o2 with
    | None, None -> raise No_subst
    | Some (mp1',resolve), None -> mp1', mp2, resolve, true
    | None, Some (mp2',resolve) -> mp1, mp2', resolve, false
    | Some (mp1',_), Some (mp2',resolve) -> mp1', mp2', resolve, false

let progress f x ~orelse =
  let y = f x in
  if y != x then y else orelse

let subst_mind sub mind =
  let mpu,l = MutInd.repr2 mind in
  let mpc = KerName.modpath (MutInd.canonical mind) in
  try
    let mpu,mpc,resolve,user = subst_dual_mp sub mpu mpc in
    let knu = KerName.make mpu l in
    let knc = if mpu == mpc then knu else KerName.make mpc l in
    let knc' =
      progress (kn_of_delta resolve) (if user then knu else knc) ~orelse:knc
    in
    MutInd.make knu knc'
  with No_subst -> mind

let subst_ind sub (ind,i as indi) =
  let ind' = subst_mind sub ind in
    if ind' == ind then indi else ind',i

let subst_pind sub (ind,u) =
  (subst_ind sub ind, u)

let subst_con0 sub cst =
  let mpu,l = Constant.repr2 cst in
  let mpc = KerName.modpath (Constant.canonical cst) in
  let mpu,mpc,resolve,user = subst_dual_mp sub mpu mpc in
  let knu = KerName.make mpu l in
  let knc = if mpu == mpc then knu else KerName.make mpc l in
  match search_delta_inline resolve knu knc with
    | Some t ->
      (* In case of inlining, discard the canonical part (cf #2608) *)
      Constant.make1 knu, Some t
    | None ->
      let knc' =
        progress (kn_of_delta resolve) (if user then knu else knc) ~orelse:knc
      in
      let cst' = Constant.make knu knc' in
      cst', None

let subst_con sub cst =
  try subst_con0 sub cst
  with No_subst -> cst, None

let subst_pcon sub (con,u as pcon) =
  try let con', _can = subst_con0 sub con in
	con',u
  with No_subst -> pcon

let subst_constant sub con =
  try fst (subst_con0 sub con)
  with No_subst -> con

let subst_proj_repr sub p =
  Projection.Repr.map (subst_mind sub) p

let subst_proj sub p =
  Projection.map (subst_mind sub) p

let subst_retro_action subst action =
  let open Retroknowledge in
  match action with
  | Register_ind(prim,ind) ->
    let ind' = subst_ind subst ind in
    if ind == ind' then action else Register_ind(prim, ind')
  | Register_type(prim,c) ->
    let c' = subst_constant subst c in
    if c == c' then action else Register_type(prim, c')
  | Register_inline(c) ->
    let c' = subst_constant subst c in
    if c == c' then action else Register_inline(c')

(* Here the semantics is completely unclear.
   What does "Hint Unfold t" means when "t" is a parameter?
   Does the user mean "Unfold X.t" or does she mean "Unfold y"
   where X.t is later on instantiated with y? I choose the first
   interpretation (i.e. an evaluable reference is never expanded). *)
let subst_evaluable_reference subst = function
  | EvalVarRef id -> EvalVarRef id
  | EvalConstRef kn -> EvalConstRef (subst_constant subst kn)

let rec map_kn f f' c =
  let func = map_kn f f' in
    match kind c with
      | Const kn -> (try f' kn with No_subst -> c)
      | Proj (p,t) -> 
          let p' = Projection.map f p in
	  let t' = func t in
	    if p' == p && t' == t then c
	    else mkProj (p', t')
      | Ind ((kn,i),u) ->
	  let kn' = f kn in
	  if kn'==kn then c else mkIndU ((kn',i),u)
      | Construct (((kn,i),j),u) ->
	  let kn' = f kn in
	  if kn'==kn then c else mkConstructU (((kn',i),j),u)
      | Case (ci,p,ct,l) ->
	  let ci_ind =
            let (kn,i) = ci.ci_ind in
	    let kn' = f kn in
	    if kn'==kn then ci.ci_ind else kn',i
	  in
	  let p' = func p in
	  let ct' = func ct in
          let l' = Array.Smart.map func l in
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
          let l' = Array.Smart.map func l in
	    if (ct'== ct && l'==l) then c
	    else mkApp (ct',l')
      | Evar (e,l) ->
          let l' = Array.Smart.map func l in
	    if (l'==l) then c
	    else mkEvar (e,l')
      | Fix (ln,(lna,tl,bl)) ->
          let tl' = Array.Smart.map func tl in
          let bl' = Array.Smart.map func bl in
	    if (bl == bl'&& tl == tl') then c
	    else mkFix (ln,(lna,tl',bl'))
      | CoFix(ln,(lna,tl,bl)) ->
          let tl' = Array.Smart.map func tl in
          let bl' = Array.Smart.map func bl in
	    if (bl == bl'&& tl == tl') then c
	    else mkCoFix (ln,(lna,tl',bl'))
      | _ -> c

let subst_mps sub c =
  let subst_pcon_term sub (con,u) =
    let con', can = subst_con0 sub con in
    match can with
    | None -> mkConstU (con',u)
    | Some t -> Vars.univ_instantiate_constr u t
  in
  if is_empty_subst sub then c
  else map_kn (subst_mind sub) (subst_pcon_term sub) c

let rec replace_mp_in_mp mpfrom mpto mp =
  match mp with
    | _ when ModPath.equal mp mpfrom -> mpto
    | MPdot (mp1,l) ->
	let mp1' = replace_mp_in_mp mpfrom mpto mp1 in
	  if mp1 == mp1' then mp
	  else MPdot (mp1',l)
    | _ -> mp

let replace_mp_in_kn mpfrom mpto kn =
 let mp,l = KerName.repr kn in
  let mp'' = replace_mp_in_mp mpfrom mpto mp in
    if mp==mp'' then kn
    else KerName.make mp'' l

let rec mp_in_mp mp mp1 =
  match mp1 with
    | _ when ModPath.equal mp1 mp -> true
    | MPdot (mp2,_l) -> mp_in_mp mp mp2
    | _ -> false

let subset_prefixed_by mp resolver =
  let mp_prefix mkey mequ rslv =
    if mp_in_mp mp mkey then Deltamap.add_mp mkey mequ rslv else rslv
  in
  let kn_prefix kn hint rslv =
    match hint with
      | Inline _ -> rslv
      | Equiv _ ->
	if mp_in_mp mp (KerName.modpath kn) then Deltamap.add_kn kn hint rslv else rslv
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
      | Inline (lev,Some t) -> Inline (lev,Some (Univ.map_univ_abstracted (subst_mps subst) t))
      | Inline (_,None) -> hint
    in
    Deltamap.add_kn kkey' hint' rslv
  in
  Deltamap.fold mp_apply_subst kn_apply_subst resolver empty_delta_resolver

let subst_codom_delta_resolver = gen_subst_delta_resolver false
let subst_dom_codom_delta_resolver = gen_subst_delta_resolver true

let update_delta_resolver resolver1 resolver2 =
  let mp_apply_rslv mkey mequ rslv =
    Deltamap.add_mp mkey (find_prefix resolver2 mequ) rslv
  in
  let kn_apply_rslv kkey hint1 rslv =
    let hint = match hint1 with
      | Equiv kequ ->
	(try Equiv (solve_delta_kn resolver2 kequ)
	 with Change_equiv_to_inline (lev,c) -> Inline (lev, Some c))
      | Inline (_,Some _) -> hint1
      | Inline (_,None) ->
        (try Deltamap.find_kn kkey resolver2 with Not_found -> hint1)
    in
    Deltamap.add_kn kkey hint rslv
  in
  Deltamap.fold mp_apply_rslv kn_apply_rslv resolver1 resolver2

let add_delta_resolver resolver1 resolver2 =
  if Deltamap.is_empty resolver2 then
    resolver1
  else
    update_delta_resolver resolver1 resolver2

let substition_prefixed_by k mp subst =
  let mp_prefixmp kmp (mp_to,reso) sub =
    if mp_in_mp mp kmp && not (ModPath.equal mp kmp) then
      let new_key = replace_mp_in_mp mp k kmp in
      Umap.add_mp new_key (mp_to,reso) sub
    else sub
  in
  Umap.fold mp_prefixmp subst empty_subst

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
  let subst = Umap.fold mp_apply_subst subst1 empty_subst in
  Umap.join subst2 subst

type 'a substituted = {
  mutable subst_value : 'a;
  mutable subst_subst : substitution list;
}

let from_val x = { subst_value = x; subst_subst = []; }

let force fsubst r = match r.subst_subst with
| [] -> r.subst_value
| s ->
  let subst = List.fold_left join empty_subst (List.rev s) in
  let x = fsubst subst r.subst_value in
  let () = r.subst_subst <- [] in
  let () = r.subst_value <- x in
  x

let subst_substituted s r = { r with subst_subst = s :: r.subst_subst; }

let force_constr = force subst_mps
let subst_constr = subst_substituted

(* debug *)
let repr_substituted r = match r.subst_subst with
| [] -> None, r.subst_value
| s -> Some s, r.subst_value
