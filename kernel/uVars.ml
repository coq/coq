(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
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
    type t = Level.t array

    val empty : t
    val is_empty : t -> bool

    val of_array : Level.t array -> t
    val to_array : t -> Level.t array

    val append : t -> t -> t
    val equal : t -> t -> bool
    val length : t -> int

    val hcons : t -> t
    val hash : t -> int

    val share : t -> t * int

    val subst_fn : (Level.t -> Level.t) -> t -> t

    val pr : (Level.t -> Pp.t) -> ?variance:Variance.t array -> t -> Pp.t
    val levels : t -> Level.Set.t
end =
struct
  type t = Level.t array

  let empty : t = [||]

  module HInstancestruct =
  struct
    type nonrec t = t
    type u = Level.t -> Level.t

    let hashcons huniv a =
      let len = Array.length a in
        if Int.equal len 0 then empty
        else begin
          for i = 0 to len - 1 do
            let x = Array.unsafe_get a i in
            let x' = huniv x in
              if x == x' then ()
              else Array.unsafe_set a i x'
          done;
          a
        end

    let eq t1 t2 =
      t1 == t2 ||
        (Int.equal (Array.length t1) (Array.length t2) &&
           let rec aux i =
             (Int.equal i (Array.length t1)) || (t1.(i) == t2.(i) && aux (i + 1))
           in aux 0)

    let hash a =
      let accu = ref 0 in
        for i = 0 to Array.length a - 1 do
          let l = Array.unsafe_get a i in
          let h = Level.hash l in
            accu := Hashset.Combine.combine !accu h;
        done;
        (* [h] must be positive. *)
        let h = !accu land 0x3FFFFFFF in
          h
  end

  module HInstance = Hashcons.Make(HInstancestruct)

  let hcons = Hashcons.simple_hcons HInstance.generate HInstance.hcons Level.hcons

  let hash = HInstancestruct.hash

  let share a = (hcons a, hash a)

  let empty = hcons [||]

  let is_empty x = Int.equal (Array.length x) 0

  let append x y =
    if Array.length x = 0 then y
    else if Array.length y = 0 then x
    else Array.append x y

  let of_array a =
    a

  let to_array a = a

  let length a = Array.length a

  let subst_fn fn t =
    let t' = CArray.Smart.map fn t in
      if t' == t then t else of_array t'

  let levels x = Array.fold_left (fun acc x -> Level.Set.add x acc) Level.Set.empty x

  let pr prl ?variance =
    let ppu i u =
      let v = Option.map (fun v -> v.(i)) variance in
      pr_opt_no_spc Variance.pr v ++ prl u
    in
    prvecti_with_sep spc ppu

  let equal t u =
    t == u ||
      (Array.is_empty t && Array.is_empty u) ||
      (CArray.for_all2 Level.equal t u
         (* Necessary as universe instances might come from different modules and
            unmarshalling doesn't preserve sharing *))

end

let enforce_eq_instances x y =
  let ax = Instance.to_array x and ay = Instance.to_array y in
    if Array.length ax != Array.length ay then
      CErrors.anomaly (Pp.(++) (Pp.str "Invalid argument: enforce_eq_instances called with")
                 (Pp.str " instances of different lengths."));
    CArray.fold_right2 enforce_eq_level ax ay

let enforce_eq_variance_instances = Variance.eq_constraints
let enforce_leq_variance_instances = Variance.leq_constraints

let subst_instance_level s l =
  match Level.var_index l with
  | Some n -> s.(n)
  | None -> l

let subst_instance_instance s i =
  Array.Smart.map (fun l -> subst_instance_level s l) i

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

(** A context of universe levels with universe constraints,
    representing local universe variables and constraints *)

module UContext =
struct
  type t = Names.Name.t array * Instance.t constrained

  let make names (univs, _ as x) =
    assert (Array.length names = Array.length univs);
    (names, x)

  (** Universe contexts (variables as a list) *)
  let empty = ([||], (Instance.empty, Constraints.empty))
  let is_empty (_, (univs, cst)) = Instance.is_empty univs && Constraints.is_empty cst

  let pr prl ?variance (_, (univs, cst) as ctx) =
    if is_empty ctx then mt() else
      h (Instance.pr prl ?variance univs ++ str " |= ") ++ h (v 0 (Constraints.pr prl cst))

  let hcons (names, (univs, cst)) =
    (Array.map Names.Name.hcons names, (Instance.hcons univs, hcons_constraints cst))

  let names (names, _) = names
  let instance (_, (univs, _cst)) = univs
  let constraints (_, (_univs, cst)) = cst

  let union (na, (univs, cst)) (na', (univs', cst')) =
    Array.append na na', (Instance.append univs univs', Constraints.union cst cst')

  let size (_,(x,_)) = Instance.length x

  let refine_names names' (names, x) =
    let merge_names = Array.map2 Names.(fun old refined -> match refined with Anonymous -> old | Name _ -> refined) in
    (merge_names names names', x)

  let sort_levels a =
    Array.sort Level.compare a; a

  let of_context_set f (ctx, cst) =
    let inst = Instance.of_array (sort_levels (Array.of_list (Level.Set.elements ctx))) in
    (f inst, (inst, cst))

  let to_context_set (_, (ctx, cst)) =
    (Instance.levels ctx, cst)

end

type universe_context = UContext.t
type 'a in_universe_context = 'a * universe_context

let hcons_universe_context = UContext.hcons

module AbstractContext =
struct
  type t = Names.Name.t array constrained

  let make names csts : t = names, csts

  let repr (inst, cst) =
    (inst, (Array.init (Array.length inst) (fun i -> Level.var i), cst))

  let pr f ?variance ctx = UContext.pr f ?variance (repr ctx)

  let instantiate inst (u, cst) =
    assert (Array.length u = Array.length inst);
    subst_instance_constraints inst cst

  let names (nas, _) = nas

  let hcons (univs, cst) =
    (Array.map Names.Name.hcons univs, hcons_constraints cst)

  let empty = ([||], Constraints.empty)

  let is_empty (nas, cst) = Array.is_empty nas && Constraints.is_empty cst

  let union (nas, cst) (nas', cst') = (Array.append nas nas', Constraints.union cst cst')

  let size (nas, _) = Array.length nas

end

type 'a univ_abstracted = {
  univ_abstracted_value : 'a;
  univ_abstracted_binder : AbstractContext.t;
}

let map_univ_abstracted f {univ_abstracted_value;univ_abstracted_binder} =
  let univ_abstracted_value = f univ_abstracted_value in
  {univ_abstracted_value;univ_abstracted_binder}

let hcons_abstract_universe_context = AbstractContext.hcons

let subst_univs_level_instance subst i =
  let i' = Instance.subst_fn (subst_univs_level_level subst) i in
    if i == i' then i
    else i'

let subst_univs_level_abstract_universe_context subst (inst, csts) =
  inst, subst_univs_level_constraints subst csts

let make_instance_subst i =
  let arr = Instance.to_array i in
    Array.fold_left_i (fun i acc l ->
      Level.Map.add l (Level.var i) acc)
      Level.Map.empty arr

let make_abstract_instance (ctx, _) =
  Array.init (Array.length ctx) (fun i -> Level.var i)

let abstract_universes uctx =
  let nas = UContext.names uctx in
  let instance = UContext.instance uctx in
  let () = assert (Int.equal (Array.length nas) (Instance.length instance)) in
  let subst = make_instance_subst instance in
  let cstrs = subst_univs_level_constraints subst
      (UContext.constraints uctx)
  in
  let ctx = (nas, cstrs) in
  instance, ctx

let pr_universe_context = UContext.pr

let pr_abstract_universe_context = AbstractContext.pr
