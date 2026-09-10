(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
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

(* The modpath part of a resolver holds two kinds of statements.
   - [p ↦ MPequiv q] states that [q] is the canonical name of [p].
   - [p ↦ MPlift] states that [p] is a bound name that should be left untouched
     by substitution. *)
type mp_hint =
| MPequiv of ModPath.t  (** the canonical form of the key *)
| MPlift                (** the prefix rule stops here *)

(* Delta-resolvers come in three kinds, tracked by the index of [delta_hint].
   [Equiv] gives the canonical name in the given context and makes sense for
   all of them. [Inline] records the level of a [Parameter Inline] and only
   makes sense in a module type. [InlineBody] records the term a constant is to
   be replaced with, which only makes sense in a substitution. *)

type mod_body = [ `ModBody ]
type mod_type = [ `ModType ]
type mod_subst = [ `ModSubst ]

type _ delta_hint =
| Equiv : KerName.t -> 'a delta_hint
| Inline : int -> mod_type delta_hint
| InlineBody : KerName.t option * constr UVars.univ_abstracted -> mod_subst delta_hint

(* NB: earlier constructor Prefix_equiv of ModPath.t
   is now stored in a separate table, see Deltamap.t below *)

module Deltamap = struct
  type 'a t = {
    root : ModPath.t;
    (** Common root of all keys in the deltamap *)
    mmap : mp_hint ModPath.Map.t;
    (** All bindings [mp ↦ _] must satisfy [mp ⊆ root] *)
    kmap : 'a delta_hint KerName.Map.t;
    (** All bindings [kn ↦ _] must satisfy [modpath(kn) ⊆ root] *)
  }

  let forget_inline (type a b) (reso : a t) : b t =
    let fold kn (hint : a delta_hint) accu : b delta_hint KerName.Map.t = match hint with
    | Equiv kn' -> KerName.Map.add kn (Equiv kn') accu
    | Inline _ -> accu
    | InlineBody (None, _) -> accu
    | InlineBody (Some kn', _) -> KerName.Map.add kn (Equiv kn') accu
    in
    { root = reso.root; mmap = reso.mmap;
      kmap = KerName.Map.fold fold reso.kmap KerName.Map.empty }

  let empty root = {
    root;
    mmap = ModPath.Map.empty;
    kmap = KerName.Map.empty;
  }

  let root reso = reso.root

  let add_kn kn hint reso =
    let () = assert (ModPath.subpath reso.root (KerName.modpath kn)) in
    { reso with kmap = KerName.Map.add kn hint reso.kmap }

  let add_mp_hint mp hint reso =
    let () = assert (ModPath.subpath reso.root mp) in
    { reso with mmap = ModPath.Map.add mp hint reso.mmap }

  let add_mp mp mp' reso = add_mp_hint mp (MPequiv mp') reso
  let lift_mp mp reso = add_mp_hint mp MPlift reso

  let find_mp_opt mp reso = ModPath.Map.find_opt mp reso.mmap
  let find_kn kn reso = KerName.Map.find kn reso.kmap
  let mem_kn kn reso = KerName.Map.mem kn reso.kmap
  let fold_kn f reso i = KerName.Map.fold f reso.kmap i
  let fold fmp fkn reso accu =
    ModPath.Map.fold fmp reso.mmap (KerName.Map.fold fkn reso.kmap accu)
  let join map1 map2 = fold add_mp_hint add_kn map1 map2

  (** if mp0 ⊆ root, we can see a resolver on root as a resolver on mp *)
  let upcast mp0 reso =
    let () = assert (ModPath.subpath mp0 reso.root) in
    { reso with root = mp0 }

  (** keep only data that is relevant for names with a modpath ⊇ root *)
  let reroot root reso =
    if ModPath.equal root reso.root then reso
    else
      let () = assert (ModPath.subpath reso.root root) in
      let km = reso.kmap in
      let mm = reso.mmap in
      (* filter the modpaths *)
      let fold_mp mp data (glb, accu) =
        if ModPath.subpath root mp then
          (* root ⊆ mp, keep it *)
          glb, ModPath.Map.add mp data accu
        else if ModPath.subpath mp root then
          (* This is a subpath of the root. It may be relevant due to find_prefix,
            but only when 1. root is not in mm, and 2. this is the most precise
            path in mm above root, as find_prefix will always return this one
            without considering the less precise ones. *)
          let glb = match glb with
          | None -> Some (mp, data)
          | Some (g, _) as old -> if ModPath.subpath g mp then Some (mp, data) else old
          in
          glb, accu
        else
          (* path that is incomparable, skip it *)
          glb, accu
      in
      let glb, mm' = ModPath.Map.fold fold_mp mm (None, ModPath.Map.empty) in
      let mm' = match glb with
      | None -> mm'
      | Some (glb, data) ->
        if ModPath.Map.mem root mm then mm'
        else
          (* Add root to the resolver and map it to what find_prefix would have
            returned on root *)
          match data with
          | MPlift -> ModPath.Map.add root MPlift mm'
          | MPequiv data ->
            let rec diff accu mp =
              if ModPath.equal mp glb then accu
              else match mp with
              | MPdot (mp, l) -> diff (l :: accu) mp
              | MPbound _ | MPfile _ -> assert false
            in
            let diff = diff [] root in
            let data' = List.fold_left (fun accu l -> MPdot (accu, l)) data diff in
            ModPath.Map.add root (MPequiv data') mm'
      in
      (* filter the kernames *)
      let filter_kn kn _ = ModPath.subpath root (KerName.modpath kn) in
      let km' = KerName.Map.filter filter_kn km in
      { kmap = km'; mmap = mm'; root = root }

end

(* Invariant: in the [delta_hint] map, an [Equiv] should only
   relate [KerName.t] with the same label (and section dirpath). *)

type 'a delta_resolver = 'a Deltamap.t

let forget_inline_delta_resolver = Deltamap.forget_inline
let of_body_delta_resolver = Deltamap.forget_inline

let empty_delta_resolver = Deltamap.empty
let has_root_delta_resolver mp reso =
  ModPath.equal mp (Deltamap.root reso)

let upcast_delta_resolver = Deltamap.upcast

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
  type 'a t = 'a ModPath.Map.t
  let empty = ModPath.Map.empty
  let is_empty m = ModPath.Map.is_empty m
  let add_mbi mbi x m = ModPath.Map.add (MPbound mbi) x m
  let add_mp mp x m = ModPath.Map.add mp x m
  let find = ModPath.Map.find
  let fold = ModPath.Map.fold
  let join map1 map2 = fold add_mp map1 map2
end

type substitution = mod_subst delta_resolver Umap.t

let empty_subst = Umap.empty

let is_empty_subst = Umap.is_empty

(* <debug> *)

let string_of_hint (type a) pr (hint : a delta_hint) =
  match hint with
  | InlineBody (kn, c) ->
    str "inline(" ++ pr_opt KerName.print kn ++ str " := " ++ pr c ++ str ")"
  | Inline lvl -> str "inline[" ++ int lvl ++ str "]"
  | Equiv kn -> str "equiv(" ++ KerName.print kn ++ str ")"

let debug_pr_mp_hint = function
| MPequiv mp -> ModPath.print mp
| MPlift -> str "<lift>"

let debug_pr_delta pr resolve =
  let kn_to_string kn hint l =
    hov 2 (KerName.print kn ++ str " =>" ++ spc() ++ string_of_hint pr hint) :: l
  in
  let mp_to_string mp hint l =
    hov 2 (ModPath.print mp ++ str " =>" ++ spc() ++ debug_pr_mp_hint hint) :: l
  in
  let l = Deltamap.fold mp_to_string kn_to_string resolve [] in
  v 0 @@ prlist_with_sep pr_comma (fun p -> p) (List.rev l)

let debug_string_of_delta resolve =
  string_of_ppcmds @@ debug_pr_delta (fun _ -> str "_") resolve

let list_contents subst =
  let one_pair reso = (ModPath.to_string (Deltamap.root reso), debug_string_of_delta reso) in
  let mp_one_pair mp0 p l = (ModPath.to_string mp0, one_pair p)::l in
  Umap.fold mp_one_pair subst []

let debug_string_of_subst subst =
  let l = List.map (fun (s1,(s2,s3)) -> s1^"|->"^s2^"["^s3^"]")
    (list_contents subst)
  in
  "{" ^ String.concat "; " l ^ "}"

let debug_pr_subst subst =
  let l = list_contents subst in
  let f (s1,(s2,s3)) = hov 2 (str s1 ++ spc () ++ str "|-> " ++ str s2 ++
                              spc () ++ str "[" ++ str s3 ++ str "]")
  in
  str "{" ++ hov 2 (prlist_with_sep pr_comma f l) ++ str "}"

(* </debug> *)

(** Extending a [delta_resolver] *)

let add_inline_delta_resolver kn lev reso =
  let () = assert (not (Deltamap.mem_kn kn reso)) in
  Deltamap.add_kn kn (Inline lev) reso

let add_kn_delta_resolver kn kn' =
  assert (Id.equal (KerName.label kn) (KerName.label kn'));
  Deltamap.add_kn kn (Equiv kn')

let add_mp_delta_resolver mp1 mp2 =
  let () = assert (not (ModPath.equal mp1 mp2)) in
  Deltamap.add_mp mp1 mp2

let lift_mp_delta_resolver mp = Deltamap.lift_mp mp

(** Extending a [substitution] without sequential composition *)

let add_mbid mbid mp resolve s =
  let () = assert (ModPath.equal mp (Deltamap.root resolve)) in
  Umap.add_mbi mbid resolve s
let add_mp mp1 mp2 resolve s =
  let () = assert (ModPath.equal mp2 (Deltamap.root resolve)) in
  Umap.add_mp mp1 resolve s

let map_mbid mbid mp resolve =
  add_mbid mbid mp resolve empty_subst
let map_mp mp1 mp2 resolve = add_mp mp1 mp2 resolve empty_subst

let find_prefix_opt resolve mp =
  let rec sub_mp mp = match Deltamap.find_mp_opt mp resolve with
  | Some (MPequiv mp') -> Some mp'
  | Some MPlift -> None
  | None ->
    match mp with
    | MPdot (mp1, l) ->
      begin match sub_mp mp1 with
      | Some mp1' -> Some (MPdot (mp1', l))
      | None -> None
      end
    | MPbound _ | MPfile _ -> None
  in
  sub_mp mp

let mp_of_delta resolve mp = match find_prefix_opt resolve mp with
| Some mp' -> mp'
| None -> mp

let mp_is_alias resolve mp = not (ModPath.equal mp (mp_of_delta resolve mp))

(** Applying a resolver to a kernel name *)

let kn_of_delta_opt (type a) (resolve : a delta_resolver) kn =
  let answer kn' = if KerName.equal kn kn' then None else Some kn' in
  let by_prefix () =
    let mp, l = KerName.repr kn in
    match find_prefix_opt resolve mp with
    | Some mp' -> answer (KerName.make mp' l)
    | None -> None
  in
  match Deltamap.find_kn kn resolve with
  | Equiv kn1 -> answer kn1
  | Inline _ -> by_prefix ()
  | InlineBody (None, _) -> by_prefix ()
  | InlineBody (Some kn1, _) -> answer kn1
  | exception Not_found -> by_prefix ()

let kn_of_delta resolve kn = match kn_of_delta_opt resolve kn with
| Some kn' -> kn'
| None -> kn

let add_inline_body_delta_resolver kn c resolve =
  let kn' = kn_of_delta resolve kn in
  let alias = if KerName.equal kn' kn then None else Some kn' in
  Deltamap.add_kn kn (InlineBody (alias, c)) resolve

let constant_of_delta_kn resolve kn =
  Constant.make kn (kn_of_delta resolve kn)

let mind_of_delta_kn resolve kn =
  MutInd.make kn (kn_of_delta resolve kn)

let fold_inline_body_delta_resolver f resolver accu =
  let fold kn hint accu = match hint with
  | InlineBody (_, c) -> f kn c accu
  | Equiv _ -> accu
  in
  Deltamap.fold_kn fold resolver accu

let inline_of_delta inline resolver =
  match inline with
    | None -> []
    | Some inl_lev ->
      let extract kn hint l =
        match hint with
          | Inline lev -> if lev <= inl_lev then kn :: l else l
          | _ -> l
      in
      Deltamap.fold_kn extract resolver []

let search_delta_inline resolve kn1 kn2 =
  let find kn = match Deltamap.find_kn kn resolve with
    | InlineBody (_, o) -> Some o
    | Equiv _ -> raise Not_found
  in
  try find kn1
  with Not_found ->
    if kn1 == kn2 then None
    else
      try find kn2
      with Not_found -> None

let subst_mp_opt subst mp = (* 's like subst *)
  let repr r = Deltamap.root r, r in
  let rec aux mp = match mp with
    | MPfile _ | MPbound _ -> repr @@ Umap.find mp subst
    | MPdot (mp1,l) as mp2 ->
        begin
          try repr @@ Umap.find mp2 subst
          with Not_found ->
            let mp1',resolve = aux mp1 in
            MPdot (mp1',l),resolve
        end
 in
 try Some (aux mp) with Not_found -> None

let subst_mp subst mp =
 match subst_mp_opt subst mp with
    None -> mp
  | Some (mp',_) -> mp'

(* Substituting the target of an [Equiv]. The image may be a constant that
   [subst] inlines, in which case the binding must become that body. This is how
   the inlining of a functor argument survives the composition of substitutions. *)
let subst_kn_hint_subst subst kn : mod_subst delta_hint =
  let mp, l = KerName.repr kn in
  match subst_mp_opt subst mp with
  | None -> Equiv kn
  | Some (mp', resolve) ->
    let kn' = KerName.make mp' l in
    match Deltamap.find_kn kn' resolve with
    | InlineBody (_, body) ->
      (* Keep the body, but pair it with the canonical name of the key we are
         building, not the one the entry we found happens to carry. *)
      let kn'' = kn_of_delta resolve kn' in
      let alias = if KerName.equal kn'' kn' then None else Some kn'' in
      InlineBody (alias, body)
    | Equiv _ -> Equiv (kn_of_delta resolve kn')
    | exception Not_found -> Equiv (kn_of_delta resolve kn')

(* Same as above but drops inlining payload by only returning the equivalent
   kername. *)
let subst_kn_delta subst kn =
 let mp,l = KerName.repr kn in
  match subst_mp_opt subst mp with
     Some (mp',resolve) -> kn_of_delta resolve (KerName.make mp' l)
   | None -> kn


let subst_kn subst kn =
 let mp,l = KerName.repr kn in
  match subst_mp_opt subst mp with
     Some (mp',_) ->
      (KerName.make mp' l)
   | None -> kn

exception No_subst

let subst_dual_mp subst mp1 mp2 =
  let o1 = subst_mp_opt subst mp1 in
  let o2 = if mp1 == mp2 then o1 else subst_mp_opt subst mp2 in
  match o1, o2 with
    | None, None -> raise No_subst
    | Some (mp1',resolve), None -> mp1', mp2, resolve, true
    | None, Some (mp2',resolve) -> mp1, mp2', resolve, false
    | Some (mp1',_), Some (mp2',resolve) -> mp1', mp2', resolve, false

let subst_mind subst mind =
  let mpu,l = KerName.repr (MutInd.user mind) in
  let mpc = KerName.modpath (MutInd.canonical mind) in
  try
    let mpu,mpc,resolve,user = subst_dual_mp subst mpu mpc in
    let knu = KerName.make mpu l in
    let knc = if mpu == mpc then knu else KerName.make mpc l in
    let knc' = match kn_of_delta_opt resolve (if user then knu else knc) with
    | Some kn -> kn
    | None -> knc
    in
    MutInd.make knu knc'
  with No_subst -> mind

let subst_ind subst (ind,i as indi) =
  let ind' = subst_mind subst ind in
    if ind' == ind then indi else ind',i

let subst_constructor subst (ind,j as ref) =
  let ind' = subst_ind subst ind in
  if ind==ind' then ref
  else (ind',j)

let subst_pind subst (ind,u) =
  (subst_ind subst ind, u)

let subst_con0 subst cst =
  let mpu,l = KerName.repr (Constant.user cst) in
  let mpc = KerName.modpath (Constant.canonical cst) in
  let mpu,mpc,resolve,user = subst_dual_mp subst mpu mpc in
  let knu = KerName.make mpu l in
  let knc = if mpu == mpc then knu else KerName.make mpc l in
  let knc' = match kn_of_delta_opt resolve (if user then knu else knc) with
  | Some kn -> kn
  | None -> knc
  in
  let cst' = Constant.make knu knc' in
  cst', search_delta_inline resolve knu knc

let subst_con subst cst =
  try subst_con0 subst cst
  with No_subst -> cst, None

let subst_pcon subst (con,u as pcon) =
  try let con', _can = subst_con0 subst con in
        con',u
  with No_subst -> pcon

let subst_constant subst con =
  try fst (subst_con0 subst con)
  with No_subst -> con

let subst_proj_repr subst p =
  Projection.Repr.map (subst_mind subst) p

let subst_proj subst p =
  Projection.map (subst_mind subst) p

let subst_retro_action subst action =
  let open Retroknowledge in
  match action with
  | Register_ind(prim,ind) ->
    let ind' = subst_ind subst ind in
    if ind == ind' then action else Register_ind(prim, ind')
  | Register_type(prim,c) ->
    let c' = subst_constant subst c in
    if c == c' then action else Register_type(prim, c')

let rec map_kn f f' c =
  let func = map_kn f f' in
    match kind c with
      | Const kn -> (try f' kn with No_subst -> c)
      | Proj (p,r,t) ->
          let p' = Projection.map f p in
          let t' = func t in
            if p' == p && t' == t then c
            else mkProj (p', r, t')
      | Ind ((kn,i),u) ->
          let kn' = f kn in
          if kn'==kn then c else mkIndU ((kn',i),u)
      | Construct (((kn,i),j),u) ->
          let kn' = f kn in
          if kn'==kn then c else mkConstructU (((kn',i),j),u)
      | Case (ci,u,pms,(p,r),iv,ct,l) ->
          let ci_ind =
            let (kn,i) = ci.ci_ind in
            let kn' = f kn in
            if kn'==kn then ci.ci_ind else kn',i
          in
          let f_ctx (nas, c as d) =
            let c' = func c in
            if c' == c then d else (nas, c')
          in
          let pms' = Array.Smart.map func pms in
          let p' = f_ctx p in
          let iv' = map_invert func iv in
          let ct' = func ct in
          let l' = Array.Smart.map f_ctx l in
            if (ci.ci_ind==ci_ind && pms'==pms && p'==p && iv'==iv
                && l'==l && ct'==ct)then c
            else
              mkCase ({ci with ci_ind = ci_ind}, u,
                      pms',(p',r),iv',ct', l')
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
          let l' = SList.Smart.map func l in
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

let subst_mps subst c =
  let subst_pcon_term subst (con,u) =
    let con', can = subst_con0 subst con in
    match can with
    | None -> mkConstU (con',u)
    | Some t -> Vars.univ_instantiate_constr u t
  in
  if is_empty_subst subst then c
  else map_kn (subst_mind subst) (subst_pcon_term subst) c

let subst_mps_aux subst = function
| Inl (con, u) ->
  begin match subst_con0 subst con with
  | con', None -> Inl (con', u)
  | _, Some t -> Inr (Vars.univ_instantiate_constr u t)
  | exception No_subst -> Inl (con, u)
  end
| Inr t -> Inr (subst_mps subst t)

let subst_mps_list substs c =
  if List.is_empty substs || List.for_all is_empty_subst substs then c
  else
    let cache_const = ref Cmap_env.empty in
    let cache_ind = ref Mindmap_env.empty in
    let subst_const (con, u as pcon) = match Cmap_env.find_opt con !cache_const with
    | Some ans ->
      if ans == con then raise No_subst else mkConstU (ans, u)
    | None ->
      let ans = List.fold_right subst_mps_aux substs (Inl pcon) in
      (* Do not cache arbitrary inline terms *)
      match ans with
      | Inl (con', _ as ans) ->
        let () = cache_const := Cmap_env.add con con' !cache_const in
        if con' == con then raise No_subst else mkConstU ans
      | Inr ans -> ans
    in
    let subst_mind ind = match Mindmap_env.find_opt ind !cache_ind with
    | Some ans -> ans
    | None ->
      let ans = List.fold_right subst_mind substs ind in
      let () = cache_ind := Mindmap_env.add ind ans !cache_ind in
      ans
    in
    map_kn subst_mind subst_const c

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

let mp_in_mp = ModPath.subpath

(* Only the equivalences survive: the result describes names under [mp], for
   whatever kind of resolver the caller is building, so it cannot carry
   inlining information of the resolver it comes from. *)
let subset_prefixed_by (type a b) mp (resolver : a delta_resolver) : b delta_resolver =
  let mp_prefix mkey mequ rslv =
    if mp_in_mp mp mkey then Deltamap.add_mp_hint mkey mequ rslv else rslv
  in
  let kn_prefix kn (hint : a delta_hint) rslv : b delta_resolver = match hint with
  | Inline _ -> rslv
  | InlineBody _ -> rslv
  | Equiv kn' ->
    if mp_in_mp mp (KerName.modpath kn) then
      Deltamap.add_kn kn (Equiv kn') rslv
    else rslv
  in
  Deltamap.fold mp_prefix kn_prefix resolver (empty_delta_resolver mp)

let subst_dom_delta_resolver mp_from mp_to resolver =
  let () = assert (ModPath.equal mp_from resolver.Deltamap.root) in
  let subst = map_mp mp_from mp_to (empty_delta_resolver mp_to) in
  let mp_apply_subst mkey hint rslv =
    Deltamap.add_mp_hint (subst_mp subst mkey) hint rslv
  in
  let kn_apply_subst kkey hint rslv =
    Deltamap.add_kn (subst_kn subst kkey) hint rslv
  in
  let root = subst_mp subst (Deltamap.root resolver) in
  Deltamap.fold mp_apply_subst kn_apply_subst resolver (empty_delta_resolver root)

let subst_mp_delta (type a) subst mp mkey : a delta_resolver * ModPath.t =
  match subst_mp_opt subst mp with
    None -> empty_delta_resolver mp, mp
  | Some (mp',resolve) ->
    (* root(resolve) ⊆ mp' *)
      let mp1 = mp_of_delta resolve mp' in
      let resolve1 = subset_prefixed_by mp1 resolve in
      let reso = subst_dom_delta_resolver mp1 mkey resolve1 in
      let reso =
        if ModPath.equal mp1 mp' then reso
        else
          (* [mp1] is the canonical form of [mp'], so the equivalences [resolve]
             records under [mp'] describe the same names as the ones it records
             under [mp1]. The latter are typically absent so we must not drop
             the former to preserve canonicity of the names. *)
          let subst' = map_mp mp' mkey (empty_delta_resolver mkey) in
          let transfer kn (hint : mod_subst delta_hint) accu : a delta_resolver =
            let kn' = match hint with
            | InlineBody (alias, _) -> alias
            | Equiv kn' -> Some kn'
            in
            match kn' with
            | Some kn' when mp_in_mp mp' (KerName.modpath kn) ->
              Deltamap.add_kn (subst_kn subst' kn) (Equiv kn') accu
            | _ -> accu
          in
          Deltamap.fold_kn transfer resolve reso
      in
      reso, mp1

type 'a inline_handler =
| InlineKeep : mod_subst inline_handler (* keep inlining data *)
| InlineDrop : 'a inline_handler  (* drop inlining data *)

let gen_subst_delta_resolver (type a) (handler : a inline_handler) dom subst (resolver : a delta_resolver) : a delta_resolver =
  let mp_apply_subst mkey hint rslv =
    let mkey' = if dom then subst_mp subst mkey else mkey in
    match hint with
    | MPlift -> Deltamap.add_mp_hint mkey' MPlift rslv
    | MPequiv mequ ->
      let rslv', mequ' = subst_mp_delta subst mequ mkey' in
      Deltamap.join rslv' (Deltamap.add_mp_hint mkey' (MPequiv mequ') rslv)
  in
  let kn_apply_subst kkey (hint : a delta_hint) rslv : a delta_resolver =
    let kkey' = if dom then subst_kn subst kkey else kkey in
    let hint' : a delta_hint = match hint with
    | Equiv kequ ->
      begin match handler with
      | InlineDrop -> Equiv (subst_kn_delta subst kequ)
      | InlineKeep -> subst_kn_hint_subst subst kequ
      end
    | InlineBody (kn', t) ->
      InlineBody (Option.map (fun kn -> subst_kn_delta subst kn) kn',
                  UVars.map_univ_abstracted (subst_mps subst) t)
    | Inline lev -> Inline lev
    in
    Deltamap.add_kn kkey' hint' rslv
  in
  let root = if dom then subst_mp subst (Deltamap.root resolver) else Deltamap.root resolver in
  Deltamap.fold mp_apply_subst kn_apply_subst resolver (empty_delta_resolver root)

let subst_codom_delta_resolver subst reso =
  gen_subst_delta_resolver InlineDrop false subst reso

let subst_dom_codom_delta_resolver subst reso =
  gen_subst_delta_resolver InlineDrop true subst reso

let subst_codom_delta_resolver_subst subst (reso : mod_subst delta_resolver) =
  gen_subst_delta_resolver InlineKeep false subst reso

let subst_dom_codom_delta_resolver_subst subst (reso : mod_subst delta_resolver) =
  gen_subst_delta_resolver InlineKeep true subst reso

let update_delta_resolver (type a) resolver1 resolver2 : a delta_resolver =
  let mp_apply_rslv mkey hint rslv = match hint with
    | MPlift -> Deltamap.add_mp_hint mkey MPlift rslv
    | MPequiv mequ ->
      Deltamap.add_mp_hint mkey (MPequiv (mp_of_delta resolver2 mequ)) rslv
  in
  let kn_apply_rslv : KerName.t -> a delta_hint -> a delta_resolver ->
    a delta_resolver = fun kkey hint1 rslv ->
    let hint : a delta_hint = match hint1 with
      | Equiv kequ -> Equiv (kn_of_delta resolver2 kequ)
      | InlineBody (kn', t) -> InlineBody (Option.map (fun kn -> kn_of_delta resolver2 kn) kn', t)
      | Inline _ ->
        (try Deltamap.find_kn kkey resolver2 with Not_found -> hint1)
    in
    Deltamap.add_kn kkey hint rslv
  in
  Deltamap.fold mp_apply_rslv kn_apply_rslv resolver1 resolver2

let add_delta_resolver (type a) resolver1 resolver2 : a delta_resolver =
  let () =
    if mp_in_mp (Deltamap.root resolver2) (Deltamap.root resolver1) then ()
    else CErrors.anomaly Pp.(strbrk "Incompatible resolver roots: " ++
      ModPath.print (Deltamap.root resolver2) ++ strbrk " is not a subpath of " ++
      ModPath.print (Deltamap.root resolver1))
  in
  update_delta_resolver resolver1 resolver2

let substitution_prefixed_by k mp subst =
  let mp_prefixmp kmp reso subst =
    if mp_in_mp mp kmp && not (ModPath.equal mp kmp) then
      let new_key = replace_mp_in_mp mp k kmp in
      Umap.add_mp new_key reso subst
    else subst
  in
  Umap.fold mp_prefixmp subst empty_subst

let join subst1 subst2 =
  let apply_subst mpk resolve res =
    let mp = Deltamap.root resolve in
    let mp', resolve' = match subst_mp_opt subst2 mp with
    | None ->
      let resolve' = subst_codom_delta_resolver_subst subst2 resolve in
      mp, resolve'
    | Some (mp', resolve') ->
      (* root(resolve') ⊆ mp' = subst2(mp) = root(subst_dom_codom_delta_resolver subst2 resolve) *)
      let resolve' =
        add_delta_resolver
          (subst_dom_codom_delta_resolver_subst subst2 resolve) resolve'
      in
      (* We need to reroot, as in general we only have root(resolve'') ⊆ mp' *)
      let resolve' = Deltamap.reroot mp' resolve' in
      mp', resolve'
    in
    let prefixed_subst = substitution_prefixed_by mpk mp' subst2 in
    Umap.join prefixed_subst (Umap.add_mp mpk resolve' res)
  in
  let subst = Umap.fold apply_subst subst1 empty_subst in
  let fold mp delta accu = match subst_mp_opt subst1 mp with
  | None -> Umap.add_mp mp delta accu
  | Some _ ->
    (* [mp] was already mapped away by [subst1] *)
    accu
  in
  Umap.fold fold subst2 subst
