(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open Util
open Univ

module Quality = Sorts.Quality

module Variance =
struct
  (** A universe position in the instance given to a cumulative
     inductive can be the following. Note there is no Contravariant
     case because [forall x : A, B <= forall x : A', B'] requires [A =
     A'] as opposed to [A' <= A]. *)
  type t = Irrelevant | Covariant | Invariant

  let sup x y =
    match x, y with
    | Irrelevant, s | s, Irrelevant -> s
    | Invariant, _ | _, Invariant -> Invariant
    | Covariant, Covariant -> Covariant

  let equal a b = match a,b with
    | Irrelevant, Irrelevant | Covariant, Covariant | Invariant, Invariant -> true
    | (Irrelevant | Covariant | Invariant), _ -> false

  let check_subtype x y = match x, y with
  | (Irrelevant | Covariant | Invariant), Irrelevant -> true
  | Irrelevant, Covariant -> false
  | (Covariant | Invariant), Covariant -> true
  | (Irrelevant | Covariant), Invariant -> false
  | Invariant, Invariant -> true

  let pr = function
    | Irrelevant -> str "*"
    | Covariant -> str "+"
    | Invariant -> str "="

  let leq_constraint csts variance u u' =
    match variance with
    | Irrelevant -> csts
    | Covariant -> enforce_leq_level u u' csts
    | Invariant -> enforce_eq_level u u' csts

  let eq_constraint csts variance u u' =
    match variance with
    | Irrelevant -> csts
    | Covariant | Invariant -> enforce_eq_level u u' csts

  let leq_constraints variance u u' csts =
    let len = Array.length u in
    assert (len = Array.length u' && len = Array.length variance);
    Array.fold_left3 leq_constraint csts variance u u'

  let eq_constraints variance u u' csts =
    let len = Array.length u in
    assert (len = Array.length u' && len = Array.length variance);
    Array.fold_left3 eq_constraint csts variance u u'
end

module Instance : sig
    type t

    val empty : t
    val is_empty : t -> bool

    val of_array : Quality.t array * Level.t array -> t
    val to_array : t -> Quality.t array * Level.t array

    val abstract_instance : int * int -> t

    val append : t -> t -> t
    val equal : t -> t -> bool
    val length : t -> int * int

    val hcons : t -> t
    val hash : t -> int

    val share : t -> t * int

    val subst_fn : (Sorts.QVar.t -> Quality.t) * (Level.t -> Level.t) -> t -> t

    val pr : (Sorts.QVar.t -> Pp.t) -> (Level.t -> Pp.t) -> ?variance:Variance.t array -> t -> Pp.t
    val levels : t -> Quality.Set.t * Level.Set.t

    type mask = Quality.pattern array * int option array

    val pattern_match : mask -> t -> ('term, Quality.t, Level.t) Partial_subst.t -> ('term, Quality.t, Level.t) Partial_subst.t option
end =
struct
  type t = Quality.t array * Level.t array

  let empty : t = [||], [||]

  module HInstancestruct =
  struct
    type nonrec t = t
    type u = (Quality.t -> Quality.t) * (Level.t -> Level.t)

    let hashcons (hqual, huniv) (aq, au as a) =
      let qlen = Array.length aq in
      let ulen = Array.length au in
        if Int.equal qlen 0 && Int.equal ulen 0 then empty
        else begin
          for i = 0 to qlen - 1 do
            let x = Array.unsafe_get aq i in
            let x' = hqual x in
              if x == x' then ()
              else Array.unsafe_set aq i x'
          done;
          for i = 0 to ulen - 1 do
            let x = Array.unsafe_get au i in
            let x' = huniv x in
              if x == x' then ()
              else Array.unsafe_set au i x'
          done;
          a
        end

    let eq t1 t2 =
      CArray.equal (==) (fst t1) (fst t2)
      && CArray.equal (==) (snd t1) (snd t2)

    let hash (aq,au) =
      let accu = ref 0 in
        for i = 0 to Array.length aq - 1 do
          let l = Array.unsafe_get aq i in
          let h = Quality.hash l in
            accu := Hashset.Combine.combine !accu h;
        done;
        for i = 0 to Array.length au - 1 do
          let l = Array.unsafe_get au i in
          let h = Level.hash l in
            accu := Hashset.Combine.combine !accu h;
        done;
        (* [h] must be positive. *)
        let h = !accu land 0x3FFFFFFF in
          h
  end

  module HInstance = Hashcons.Make(HInstancestruct)

  let hcons = Hashcons.simple_hcons HInstance.generate HInstance.hcons (Quality.hcons,Level.hcons)

  let hash = HInstancestruct.hash

  let share a = (hcons a, hash a)

  let empty = hcons empty

  let is_empty (x,y) = CArray.is_empty x && CArray.is_empty y


  let append (xq,xu as x) (yq,yu as y) =
    if is_empty x then y
    else if is_empty y then x
    else Array.append xq yq, Array.append xu yu

  let of_array a : t = a

  let to_array (a:t) = a

  let abstract_instance (qlen,ulen) =
    let qs = Array.init qlen Quality.var in
    let us = Array.init ulen Level.var in
    of_array (qs,us)

  let length (aq,au) = Array.length aq, Array.length au

  let subst_fn (fq, fn) (q,u as orig) : t =
    let q' = CArray.Smart.map (Quality.subst fq) q in
    let u' = CArray.Smart.map fn u in
    if q' == q && u' == u then orig else q', u'

  let levels (xq,xu) =
    let q = Array.fold_left (fun acc x -> Quality.Set.add x acc) Quality.Set.empty xq in
    let u = Array.fold_left (fun acc x -> Level.Set.add x acc) Level.Set.empty xu in
    q, u

  let pr prq prl ?variance (q,u) =
    let ppu i u =
      let v = Option.map (fun v -> v.(i)) variance in
      pr_opt_no_spc Variance.pr v ++ prl u
    in
    (if Array.is_empty q then mt() else prvect_with_sep spc (Quality.pr prq) q ++ strbrk " | ")
    ++ prvecti_with_sep spc ppu u

  let equal (xq,xu) (yq,yu) =
    CArray.equal Quality.equal xq yq
    && CArray.equal Level.equal xu yu

  type mask = Quality.pattern array * int option array

  let pattern_match (qmask, umask) (qs, us) tqus =
    let tqus = Array.fold_left2 (fun tqus mask u -> Partial_subst.maybe_add_univ mask u tqus) tqus umask us in
    match Array.fold_left2 (fun tqus mask q -> Quality.pattern_match mask q tqus |> function Some tqs -> tqs | None -> raise_notrace Exit) tqus qmask qs with
    | tqs -> Some tqs
    | exception Exit -> None
end

let eq_sizes (a,b) (a',b') = Int.equal a a' && Int.equal b b'

type 'a quconstraint_function = 'a -> 'a -> Sorts.QUConstraints.t -> Sorts.QUConstraints.t

let enforce_eq_instances x y (qcs, ucs as orig) =
  let xq, xu = Instance.to_array x and yq, yu = Instance.to_array y in
  if Array.length xq != Array.length yq || Array.length xu != Array.length yu then
    CErrors.anomaly (Pp.(++) (Pp.str "Invalid argument: enforce_eq_instances called with")
                       (Pp.str " instances of different lengths."));
  let qcs' = CArray.fold_right2 Sorts.enforce_eq_quality xq yq qcs in
  let ucs' = CArray.fold_right2 enforce_eq_level xu yu ucs in
  if qcs' == qcs && ucs' == ucs then orig else qcs', ucs'

let enforce_eq_variance_instances variances x y (qcs,ucs as orig) =
  let xq, xu = Instance.to_array x and yq, yu = Instance.to_array y in
  let qcs' = CArray.fold_right2 Sorts.enforce_eq_quality xq yq qcs in
  let ucs' = Variance.eq_constraints variances xu yu ucs in
  if qcs' == qcs && ucs' == ucs then orig else qcs', ucs'

let enforce_leq_variance_instances variances x y (qcs,ucs as orig) =
  let xq, xu = Instance.to_array x and yq, yu = Instance.to_array y in
  (* no variance for quality variables -> enforce_eq *)
  let qcs' = CArray.fold_right2 Sorts.enforce_eq_quality xq yq qcs in
  let ucs' = Variance.leq_constraints variances xu yu ucs in
  if qcs' == qcs && ucs' == ucs then orig else qcs', ucs'

let subst_instance_level s l =
  match Level.var_index l with
  | Some n -> (snd (Instance.to_array s)).(n)
  | None -> l

let subst_instance_qvar s v =
  match Sorts.QVar.var_index v with
  | Some n -> (fst (Instance.to_array s)).(n)
  | None -> Quality.QVar v

let subst_instance_quality s l =
  match l with
  | Quality.QVar v -> begin match Sorts.QVar.var_index v with
      | Some n -> (fst (Instance.to_array s)).(n)
      | None -> l
    end
  | Quality.QConstant _ -> l

let subst_instance_instance s i =
  let qs, us = Instance.to_array i in
  let qs' = Array.Smart.map (fun l -> subst_instance_quality s l) qs in
  let us' = Array.Smart.map (fun l -> subst_instance_level s l) us in
  if qs' == qs && us' == us then i else Instance.of_array (qs', us')

let subst_instance_universe s univ =
  let f (v,n as vn) =
    let v' = subst_instance_level s v in
    if v == v' then vn
    else v', n
  in
  let u = Universe.repr univ in
  let u' = List.Smart.map f u in
  if u == u' then univ
  else Universe.unrepr u'

let subst_instance_sort u s =
  Sorts.subst_fn ((subst_instance_qvar u), (subst_instance_universe u)) s

let subst_instance_relevance u r =
  Sorts.relevance_subst_fn (subst_instance_qvar u) r

let subst_instance_constraint s (u,d,v as c) =
  let u' = subst_instance_level s u in
  let v' = subst_instance_level s v in
    if u' == u && v' == v then c
    else (u',d,v')

let subst_instance_constraints s csts =
  Constraints.fold
    (fun c csts -> Constraints.add (subst_instance_constraint s c) csts)
    csts Constraints.empty

type 'a puniverses = 'a * Instance.t
let out_punivs (x, _y) = x
let in_punivs x = (x, Instance.empty)
let eq_puniverses f (x, u) (y, u') =
  f x y && Instance.equal u u'

type bound_names = Names.Name.t array * Names.Name.t array

(** A context of universe levels with universe constraints,
    representing local universe variables and constraints *)

module UContext =
struct
  type t = bound_names * Instance.t constrained

  let make names (univs, _ as x) : t =
    let qs, us = Instance.to_array univs in
    assert (Array.length (fst names) = Array.length qs && Array.length(snd names) = Array.length us);
    (names, x)

  (** Universe contexts (variables as a list) *)
  let empty = (([||], [||]), (Instance.empty, Constraints.empty))
  let is_empty (_, (univs, csts)) = Instance.is_empty univs && Constraints.is_empty csts

  let pr prq prl ?variance (_, (univs, csts) as uctx) =
    if is_empty uctx then mt() else
      h (Instance.pr prq prl ?variance univs ++ str " |= ") ++ h (v 0 (Constraints.pr prl csts))

  let hcons ((qnames, unames), (univs, csts)) =
    ((Array.map Names.Name.hcons qnames, Array.map Names.Name.hcons unames), (Instance.hcons univs, hcons_constraints csts))

  let names ((names, _) : t) = names
  let instance (_, (univs, _csts)) = univs
  let constraints (_, (_univs, csts)) = csts

  let union ((qna, una), (univs, csts)) ((qna', una'), (univs', csts')) =
    (Array.append qna qna', Array.append una una'), (Instance.append univs univs', Constraints.union csts csts')

  let size (_,(x,_)) = Instance.length x

  let refine_names (qnames',unames') ((qnames, unames), x) =
    let merge_names = Array.map2 Names.(fun old refined -> match refined with Anonymous -> old | Name _ -> refined) in
    ((merge_names qnames qnames', merge_names unames unames'), x)

  let sort_levels a =
    Array.sort Level.compare a; a

  let sort_qualities a =
    Array.sort Quality.compare a; a

  let of_context_set f qctx (levels, csts) =
    let qctx = sort_qualities
        (Array.map_of_list (fun q -> Quality.QVar q)
           (Sorts.QVar.Set.elements qctx))
    in
    let levels = sort_levels (Array.of_list (Level.Set.elements levels)) in
    let inst = Instance.of_array (qctx, levels) in
    (f inst, (inst, csts))

  let to_context_set (_, (inst, csts)) =
    let qs, us = Instance.to_array inst in
    let us = Array.fold_left (fun acc x -> Level.Set.add x acc) Level.Set.empty us in
    let qs = Array.fold_left (fun acc -> function
        | Sorts.Quality.QVar x -> Sorts.QVar.Set.add x acc
        | Sorts.Quality.QConstant _ -> assert false)
        Sorts.QVar.Set.empty
        qs
    in
    qs, (us, csts)

end

type universe_context = UContext.t
type 'a in_universe_context = 'a * universe_context

let hcons_universe_context = UContext.hcons

module AbstractContext =
struct
  type t = bound_names constrained

  let make names csts : t = names, csts

  let instantiate inst ((qnames,unames), cst) =
    let q, u = Instance.to_array inst in
    assert (Array.length q == Array.length qnames && Array.length u = Array.length unames);
    subst_instance_constraints inst cst

  let names (nas, _) = nas

  let hcons ((qnames,unames), cst) =
    let qnames = Array.map Names.Name.hcons qnames in
    let unames = Array.map Names.Name.hcons unames in
    ((qnames, unames), hcons_constraints cst)

  let empty = (([||],[||]), Constraints.empty)

  let is_constant ((qnas,unas),_) =
    Array.is_empty qnas && Array.is_empty unas

  let is_empty (_, cst as ctx) =
    is_constant ctx && Constraints.is_empty cst

  let union ((qnas,unas), cst) ((qnas',unas'), cst') =
    ((Array.append qnas qnas', Array.append unas unas'), Constraints.union cst cst')

  let size ((qnas,unas), _) = Array.length qnas, Array.length unas

  let repr (names, cst as self) : UContext.t =
    let inst = Instance.abstract_instance (size self) in
    (names, (inst, cst))

  let pr prq pru ?variance ctx = UContext.pr prq pru ?variance (repr ctx)

end

type 'a univ_abstracted = {
  univ_abstracted_value : 'a;
  univ_abstracted_binder : AbstractContext.t;
}

let map_univ_abstracted f {univ_abstracted_value;univ_abstracted_binder} =
  let univ_abstracted_value = f univ_abstracted_value in
  {univ_abstracted_value;univ_abstracted_binder}

let hcons_abstract_universe_context = AbstractContext.hcons

let pr_quality_level_subst prl l =
  let open Pp in
  h (prlist_with_sep fnl (fun (u,v) -> prl u ++ str " := " ++ Sorts.Quality.pr prl v)
       (Sorts.QVar.Map.bindings l))

type sort_level_subst = Quality.t Sorts.QVar.Map.t * universe_level_subst

let is_empty_sort_subst (qsubst,usubst) = Sorts.QVar.Map.is_empty qsubst && is_empty_level_subst usubst

let empty_sort_subst = Sorts.QVar.Map.empty, empty_level_subst

let subst_sort_level_instance (qsubst,usubst) i =
  let i' = Instance.subst_fn (Quality.subst_fn qsubst, subst_univs_level_level usubst) i in
  if i == i' then i
  else i'

let subst_instance_sort_level_subst s (i : sort_level_subst) =
  let qs, us = i in
  let qs' = Sorts.QVar.Map.map (fun l -> subst_instance_quality s l) qs in
  let us' = Level.Map.map (fun l -> subst_instance_level s l) us in
  if qs' == qs && us' == us then i else (qs', us')

let subst_univs_level_abstract_universe_context subst (inst, csts) =
  inst, subst_univs_level_constraints subst csts

let subst_sort_level_qvar (qsubst,_) qv =
  match Sorts.QVar.Map.find_opt qv qsubst with
  | None -> Quality.QVar qv
  | Some q -> q

let subst_sort_level_quality subst = function
  | Sorts.Quality.QConstant _ as q -> q
  | Sorts.Quality.QVar q ->
    subst_sort_level_qvar subst q

let subst_sort_level_sort (_,usubst as subst) s =
  let fq qv = subst_sort_level_qvar subst qv in
  let fu u = subst_univs_level_universe usubst u in
  Sorts.subst_fn (fq,fu) s

let subst_sort_level_relevance subst r =
  Sorts.relevance_subst_fn (subst_sort_level_qvar subst) r

let make_instance_subst i =
  let qarr, uarr = Instance.to_array i in
  let qsubst =
    Array.fold_left_i (fun i acc l ->
      let l = match l with Quality.QVar l -> l | _ -> assert false in
      Sorts.QVar.Map.add l (Quality.var i) acc)
      Sorts.QVar.Map.empty qarr
  in
  let usubst =
    Array.fold_left_i (fun i acc l ->
      Level.Map.add l (Level.var i) acc)
      Level.Map.empty uarr
  in
  qsubst, usubst

let make_abstract_instance ctx =
  UContext.instance (AbstractContext.repr ctx)

let abstract_universes uctx =
  let nas = UContext.names uctx in
  let instance = UContext.instance uctx in
  let subst = make_instance_subst instance in
  let cstrs = subst_univs_level_constraints (snd subst)
      (UContext.constraints uctx)
  in
  let ctx = (nas, cstrs) in
  instance, ctx

let pr_universe_context = UContext.pr

let pr_abstract_universe_context = AbstractContext.pr
