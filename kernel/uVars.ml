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
open PConstraints

module Quality = Sorts.Quality

module Variance =
struct
  (** A universe position in the instance given to a cumulative
     inductive can be the following. *)
  type t = Irrelevant | Covariant | Contravariant | Invariant

  let sup x y =
    match x, y with
    | Irrelevant, s | s, Irrelevant -> s
    | Invariant, _ | _, Invariant -> Invariant
    | Covariant, Covariant -> Covariant
    | Contravariant, Contravariant -> Contravariant
    | Covariant, Contravariant | Contravariant, Covariant -> Invariant

  let sup_variances = function
    | [] -> None
    | v :: vs -> Some (List.fold_left sup v vs)

  let equal a b = match a,b with
    | Irrelevant, Irrelevant | Covariant, Covariant | Contravariant, Contravariant | Invariant, Invariant -> true
    | (Irrelevant | Covariant | Contravariant | Invariant), _ -> false

  let le x y = match x, y with
  | Irrelevant, (Irrelevant | Covariant | Contravariant | Invariant) -> true
  | (Covariant | Contravariant | Invariant), Irrelevant -> false
  | Covariant, (Covariant | Invariant) -> true
  | Contravariant, (Contravariant | Invariant) -> true
  | Covariant, Contravariant -> false
  | Contravariant, Covariant -> false
  | Invariant, (Covariant | Contravariant) -> false
  | Invariant, Invariant -> true

  let pr = function
    | Irrelevant -> str "*"
    | Covariant -> str "+"
    | Contravariant -> str "-"
    | Invariant -> str "="

  let leq_constraint csts variance u u' =
    match variance with
    | Irrelevant -> csts
    | Covariant -> enforce_leq u u' csts
    | Contravariant -> enforce_leq u' u csts
    | Invariant -> enforce_eq u u' csts

  let eq_constraint csts variance u u' =
    match variance with
    | Irrelevant -> csts
    | Covariant | Contravariant | Invariant -> enforce_eq u u' csts

  let opp = function
    | Irrelevant | Invariant as x -> x
    | Covariant -> Contravariant
    | Contravariant -> Covariant

  let is_irrelevant = function
    | Irrelevant -> true
    | _ -> false
end

type application = FullyApplied | NumArgs of int
let is_applied o n = match o with FullyApplied -> true | NumArgs m -> Int.equal m n

let is_applied_enough o n = match o with FullyApplied -> true | NumArgs m -> n < m

module Position =
struct
  type t =
  | InBinder of int
  | InTopFixBinder of int
  | InTerm | InType

  let equal x y =
    match x, y with
    | InBinder i, InBinder i' -> Int.equal i i'
    | InTerm, InTerm | InType, InType -> true
    | _, _ -> false

  let le x y =
    match x, y with
    | InBinder i, InBinder i' -> i <= i'
    | InBinder _, (InTopFixBinder _ | InTerm | InType) -> true
    | InTopFixBinder _, InBinder _ -> false
    | InTopFixBinder i, InTopFixBinder i' -> i <= i'
    | InTopFixBinder _, (InTerm | InType) -> true
    | (InTerm | InType), (InBinder _ | InTopFixBinder _) -> false
    | InTerm, InTerm -> true
    | InType, InType -> true
    | InType, InTerm -> true
    | InTerm, InType -> false

  let pr pos =
    match pos with
    | InTerm ->  str"(in term)"
    | InType ->  str"(in type)"
    | InBinder i -> str"(" ++ pr_nth (i + 1) ++ str" binder)"
    | InTopFixBinder i -> str"(" ++ pr_nth (i + 1) ++ str" fix binder)"

  let lift k pos =
    match pos with
    | InTerm | InType -> pos
    | InBinder i -> InBinder (k + i)
    | InTopFixBinder i -> InTopFixBinder (k + i)
end

module VariancePos =
struct
  type t = Variance.t * Position.t

  let make v pos = (v, pos)

  let equal (v, pos) (v', pos') =
    Variance.equal v v' && Position.equal pos pos'

  let le (v, pos) (v', pos') =
    (Variance.equal v v' && Position.le pos pos') ||
    (Variance.le v v')

  let lift k (v, pos) =
    (v, Position.lift k pos)

  let variance nargs (v, pos) =
    let open Position in
    match pos with
    | InTerm -> v
    | InType ->
      let open Variance in
      (match v with
      | Irrelevant | Covariant ->
        Irrelevant (* A universe which only appears covariantly in the type *)
      | Contravariant | Invariant -> v)
    | InBinder binder | InTopFixBinder binder ->
      if is_applied_enough nargs binder then
        let open Variance in
        Irrelevant
        (* (match v with
        | Contravariant -> Irrelevant
        | Invariant | Covariant -> v
        | Irrelevant -> v) *)
      else v

  let pr (v, pos) = Variance.pr v ++ Position.pr pos

end

(** {6 Variance occurrences} *)

type impred_qvars_status =
  | Predicative
  | Impredicative of Sorts.QVar.Set.t
type impred_qvars = impred_qvars_status option

let update_impred_qvars (f : Sorts.QVar.t -> Quality.t option) vars =
  match vars with
  | None -> None
  | Some Predicative -> Some Predicative
  | Some (Impredicative vars) ->
    let pred = Sorts.QVar.Set.fold (fun qv impred ->
      match impred with
      | Predicative -> impred
      | Impredicative impred as acc ->
        match f qv with
        | None -> (* A unification variable, might become impredicative *)
          Impredicative (Sorts.QVar.Set.add qv impred)
        | Some q ->
          let open Quality in
          match q with
          | QVar v -> Impredicative (Sorts.QVar.Set.add v impred)
          | QGlobal _ -> acc (* MS: Check with SkySkimmer *)
          | QConstant (QProp | QSProp) -> acc
          | QConstant QType -> Predicative)
      vars (Impredicative Sorts.QVar.Set.empty)
    in Some pred

let pr_impred_qvars (qvars : impred_qvars) =
  let open Pp in
  let pr_pred = function
  | Predicative -> str "predicative"
  | Impredicative qvars ->
    let elems = Sorts.QVar.Set.elements qvars in
    if List.is_empty elems then str"impredicative"
    else str"(im)predicative depending on " ++ prlist_with_sep spc Sorts.QVar.raw_pr elems
  in Pp.(pr_opt pr_pred qvars)

let impred_qvars_of_quality q =
  let open Quality in
  match q with
  | QVar qv -> Impredicative (Sorts.QVar.Set.singleton qv)
  | QConstant (QProp | QSProp) -> Impredicative Sorts.QVar.Set.empty
  | QGlobal _ -> Predicative
  | QConstant QType -> Predicative

let equal_qvars (x : impred_qvars) (y : impred_qvars) =
  let eq_pred x y = match x, y with
  | Predicative, Predicative -> true
  | Impredicative qvars, Impredicative qvars' -> Sorts.QVar.Set.equal qvars qvars'
  | _, _ -> false
  in Option.equal eq_pred x y

let union_impred_qvars impred_qvars impred_qvars' =
  let union_pred x y =
    match x, y with
    | Predicative, _ | _, Predicative -> Predicative
    | Impredicative s, Impredicative s' -> Impredicative (Sorts.QVar.Set.union s s')
  in
  match impred_qvars, impred_qvars' with
  | Some s, Some s' -> Some (union_pred s s')
  | None, x -> x
  | x, None -> x

module VariancePair =
struct
  type t =
  { cumul_variance : Variance.t;
    typing_variance : Variance.t }

  let cumul_variance x = x.cumul_variance
  let typing_variance x = x.typing_variance
  let irrelevant_pair =
    { cumul_variance = Variance.Irrelevant; typing_variance = Variance.Irrelevant }

  let equal v v' =
    v.cumul_variance == v'.cumul_variance &&
    v.typing_variance == v'.typing_variance

  let le x y =
    Variance.le x.cumul_variance y.cumul_variance &&
    Variance.le x.typing_variance y.typing_variance

  let sup x y =
    { cumul_variance = Variance.sup x.cumul_variance y.cumul_variance;
      typing_variance = Variance.sup x.typing_variance y.typing_variance }

  let pr { cumul_variance; typing_variance } =
    if cumul_variance == typing_variance then Variance.pr cumul_variance
    else Variance.pr cumul_variance ++ str" (" ++ Variance.pr typing_variance ++ str" for typing)"


  let sup_cumul_variances x y =
    Variance.sup x.cumul_variance y.cumul_variance

  let sup_typing_variances x y =
    Variance.sup x.typing_variance y.typing_variance

end
module VarianceOccurrence =
struct
  open VariancePair

  type t =
    { in_binders : VariancePair.t option * int list; (* Max variance, binders where the level occurs *)
      in_topfix_binders : VariancePair.t option * int list; (* Occurrences in toplevel fix binders *)
      in_term : VariancePair.t option;
      in_type : VariancePair.t option;
      under_impred_qvars : impred_qvars }
  let default_occ =
    { in_binders = None, []; in_topfix_binders = None, []; in_term = None; in_type = None;
      under_impred_qvars = None }

  let lift n occ =
    let v, pos = occ.in_binders in
    { occ with in_binders = v, List.map (fun i -> (i + n)) pos }

  let pr_variance_occurrence fa fterm ftype { in_binders; in_topfix_binders; in_term; in_type; under_impred_qvars = _ } =
    let open Pp in
    let pr_binders = fa false in_binders in
    let pr_binders = List.append pr_binders (fa true in_topfix_binders) in
    let pr_in_term = fterm in_term in
    let pr_in_type = ftype in_type in
    let variances = List.append pr_binders pr_in_term in
    if List.is_empty variances then
      str"*" ++ if List.is_empty pr_in_type then mt () else str"(" ++
        prlist_with_sep pr_comma identity pr_in_type ++ str")"
    else
      let variances = List.append variances pr_in_type in
      str"(" ++ prlist_with_sep pr_comma identity variances ++ str")"

  let pr occ =
    let pr_binders in_fix (bindersv, binders) =
      match bindersv with
      | None -> []
      | Some b -> [VariancePair.pr b ++ str " in " ++ prlist_with_sep pr_comma (fun i -> pr_nth (succ i)) binders ++
        (if in_fix then str" fix " else mt()) ++
        str (String.plural (List.length binders) " binder")]
    in
    let pr_in_type = function
      | None -> []
      | Some ty -> [VariancePair.pr ty ++ str" in type"]
    in
    let pr_in_term = function
    | None -> []
    | Some term -> [VariancePair.pr term ++ str" in term"]
    in
    pr_variance_occurrence pr_binders pr_in_term pr_in_type occ

  let opt_pair_equal = Option.equal VariancePair.equal

  let eq_binders (bindersv, in_binders) (bindersv', in_binders') =
    opt_pair_equal bindersv bindersv' &&
    List.equal Int.equal in_binders in_binders'

  let equal ({ in_binders; in_topfix_binders; in_term; in_type; under_impred_qvars } as x)
    ({ in_binders = in_binders'; in_topfix_binders = in_topfix_binders'; in_term = in_term'; in_type = in_type';
       under_impred_qvars = under_impred_qvars' } as y) =
    x == y ||
    (eq_binders in_binders in_binders' &&
    eq_binders in_topfix_binders in_topfix_binders' &&
    opt_pair_equal in_term in_term' &&
    opt_pair_equal in_type in_type' &&
    equal_qvars under_impred_qvars under_impred_qvars')

  let opt_pair_equal_cumul = Option.equal (fun x y -> Variance.equal x.cumul_variance y.cumul_variance)

  let eq_binders_cumul (bindersv, in_binders) (bindersv', in_binders') =
    opt_pair_equal_cumul bindersv bindersv' &&
    List.equal Int.equal in_binders in_binders'

  let equal_cumul ({ in_binders; in_topfix_binders; in_term; in_type; under_impred_qvars } as x)
    ({ in_binders = in_binders'; in_topfix_binders = in_topfix_binders'; in_term = in_term'; in_type = in_type';
       under_impred_qvars = under_impred_qvars' } as y) =
    x == y ||
    (eq_binders_cumul in_binders in_binders' &&
    eq_binders_cumul in_topfix_binders in_topfix_binders' &&
    opt_pair_equal_cumul in_term in_term' &&
    opt_pair_equal_cumul in_type in_type' &&
    equal_qvars under_impred_qvars under_impred_qvars')

  let option_le le x y =
    match x, y with
    | None, Some _ -> true
    | Some x, Some y -> le x y
    | Some v, None -> Variance.is_irrelevant v.cumul_variance (* FIXME, really needed? *)
    | None, None -> true

  let opt_pair_le x y = option_le VariancePair.le x y

  let le_binders (in_binders, pos) (in_binders', pos') =
    opt_pair_le in_binders in_binders' && List.subset pos pos'

  let le ({ in_binders; in_topfix_binders; in_term; in_type; under_impred_qvars = _ } as x)
    ({ in_binders = in_binders'; in_topfix_binders = in_topfix_binders'; in_term = in_term'; in_type = in_type';
       under_impred_qvars = _under_impred_qvars' } as y) =
    x == y ||
    (le_binders in_binders in_binders' &&
     le_binders in_topfix_binders in_topfix_binders' &&
     opt_pair_le in_term in_term' &&
     opt_pair_le in_type in_type')
    (* Option.equal Sorts.QVar.Set.equal under_impred_qvars under_impred_qvars') Does not matter for subtyping *)

  let opt_union_proj p f x y =
    match x, y with
    | Some x, Some y -> Some (f x y)
    | Some x, None -> Some (p x)
    | None, Some y -> Some (p y)
    | None, None -> None

  let _term_variance { in_binders = (bindersv, _); in_topfix_binders = (fix_bindersv, _); in_term; in_type = _; under_impred_qvars = _ } =
    Option.default Variance.Irrelevant
      (Option.union Variance.sup (Option.map (fun x -> x.cumul_variance) fix_bindersv) (opt_union_proj cumul_variance VariancePair.sup_cumul_variances bindersv in_term))

  let typing_variances { in_binders = (bindersv, _); in_topfix_binders = (fix_bindersv, _); in_term; in_type = _; under_impred_qvars = _ } =
    Option.default Variance.Irrelevant
      (Option.union Variance.sup (Option.map (fun x -> x.typing_variance) fix_bindersv)
      (opt_union_proj typing_variance VariancePair.sup_typing_variances bindersv in_term))


  let variance_app nargs vocc =
    let binderv =
      match vocc.in_binders with
      | None, _ -> irrelevant_pair
      | Some v, li ->
        match nargs with
        | FullyApplied -> irrelevant_pair
        | NumArgs nargs -> if List.exists (fun k -> k >= nargs) li then v else irrelevant_pair
    in
    match vocc.in_term with
    | None -> binderv
    | Some vterm -> VariancePair.sup binderv vterm

  let variances_of_opt_pair = Option.default irrelevant_pair

  type input_universe = bool

  let typing_and_cumul_variance_app ?(with_type=true) nargs vocc =
    let open Variance in
    let is_applied_enough, variance_in_binders =
      match vocc.in_binders with
      | None, _ -> false, irrelevant_pair
      | Some v, li ->
        match nargs with
        | FullyApplied -> true, irrelevant_pair
        | NumArgs nargs ->
          if List.exists (fun k -> k >= nargs) li then false, v
          else true, irrelevant_pair
    in
    let binders_term_variance = VariancePair.sup variance_in_binders (variances_of_opt_pair vocc.in_term) in
    let typing_variance =
      if binders_term_variance.cumul_variance == Irrelevant then irrelevant_pair
      else if with_type then VariancePair.sup binders_term_variance (variances_of_opt_pair vocc.in_type)
      else binders_term_variance
    in
    let binders_variance = if is_applied_enough then irrelevant_pair else variances_of_opt_pair (fst vocc.in_binders) in
    let topfix_variance = variances_of_opt_pair (fst vocc.in_topfix_binders) in
    let binders_cumul_variance = VariancePair.sup binders_variance topfix_variance in
    let cumul_variance = VariancePair.sup binders_cumul_variance (variances_of_opt_pair vocc.in_term) in
    is_applied_enough, { cumul_variance = cumul_variance.cumul_variance; typing_variance = typing_variance.typing_variance }

  let typing_and_cumul_variance ~nargs vocc = typing_and_cumul_variance_app (NumArgs nargs) vocc

  let eq_constraint nargs csts vocc =
    let variance = variance_app nargs vocc in
    Variance.eq_constraint csts variance.cumul_variance

  let leq_constraint nargs csts vocc =
    let variance = variance_app nargs vocc in
    Variance.leq_constraint csts variance.cumul_variance

  let under_impred_qvars vocc = vocc.under_impred_qvars

end

module Variances =
struct
  type t = VarianceOccurrence.t array

  let lift n vs : t =
    if Int.equal n 0 then vs
    else Array.map (VarianceOccurrence.lift n) vs

  let make vocc : t = vocc

  let repr (vs : t) : VarianceOccurrence.t array = vs

  let split n (vs : t) : t * t =
    assert (n <= Array.length vs);
    Array.chop n vs

  let append vs vs' : t =
    Array.append vs vs'

  let pr (vs : t) : Pp.t = prvect_with_sep spc VarianceOccurrence.pr vs

  let equal (x : t) (y : t) : bool =
    Array.equal VarianceOccurrence.equal x y

  let equal_cumul x y = Array.equal VarianceOccurrence.equal_cumul x y

  let eq_sizes x y =
    Int.equal (Array.length x) (Array.length y)

  let le x y =
    Array.equal VarianceOccurrence.le x y

  let leq_constraints ~nargs variances u u' csts =
    let len = Array.length u in
    assert (len = Array.length u' && len = Array.length variances);
    Array.fold_left3 (VarianceOccurrence.leq_constraint nargs) csts variances u u'

  let eq_constraints ~nargs variances u u' csts =
    let len = Array.length u in
    assert (len = Array.length u' && len = Array.length variances);
    Array.fold_left3 (VarianceOccurrence.eq_constraint nargs) csts variances u u'

  let cumulative variances =
    let not_cumul_invariant v =
      match v.VarianceOccurrence.in_term with
      | None -> true
      | Some { VariancePair.cumul_variance = v; _ }  -> v != Variance.Invariant
    in
    Array.exists not_cumul_invariant variances

end

type variances = Variances.t

module LevelInstance : sig
    type t

    val empty : t
    val is_empty : t -> bool

    val of_array : Quality.t array * Level.t array -> t
    val to_array : t -> Quality.t array * Level.t array

    val abstract_instance : int * int -> t

    val append : t -> t -> t
    val equal : t -> t -> bool
    val length : t -> int * int

    val hcons : t -> int * t
    val hash : t -> int

    val subst_fn : (Sorts.QVar.t -> Quality.t) * (Level.t -> Level.t) -> t -> t

    val pr : Sorts.printer -> ?variances:Variances.t -> t -> Pp.t
    val levels : t -> Quality.Set.t * Level.Set.t

    val lookup_quality : t -> int -> Quality.t
    val lookup_level : t -> int -> Level.t
end =
struct
  type t = Quality.t array * Level.t array

  let empty : t = [||], [||]

  module HInstancestruct =
  struct
    type nonrec t = t

    let hashcons (aq, au as a) =
      let qlen = Array.length aq in
      let ulen = Array.length au in
      if Int.equal qlen 0 && Int.equal ulen 0 then 0, empty
      else
        let hq, aq' = Hashcons.hashcons_array Quality.hcons aq in
        let hu, au' = Hashcons.hashcons_array Level.hcons au in
        let a = if aq' == aq && au' == au then a else (aq',au') in
        Hashset.Combine.combine hq hu, a

    let eq t1 t2 =
      CArray.equal (==) (fst t1) (fst t2)
      && CArray.equal (==) (snd t1) (snd t2)

  end

  module HInstance = Hashcons.Make(HInstancestruct)

  let hcons = Hashcons.simple_hcons HInstance.generate HInstance.hcons ()

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
    (* [h] must be positive (XXX why?). *)
    let h = !accu land 0x3FFFFFFF in
    h

  let empty = snd @@ hcons empty

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

  let pr (printer:Sorts.printer) ?variances (q,u) =
    let ppu i u =
      let v = Option.map (fun v ->
        let v = Variances.repr v in
        if i < Array.length v then v.(i) else VarianceOccurrence.default_occ (* TODO fix: bad caller somewhere *)) variances in
      printer.pru u ++ pr_opt_no_spc VarianceOccurrence.pr v
    in
    (if Array.is_empty q then mt() else prvect_with_sep spc (Quality.pr printer.prq) q ++ strbrk " ; ")
    ++ prvecti_with_sep spc ppu u

  let equal (xq,xu) (yq,yu) =
    CArray.equal Quality.equal xq yq
    && CArray.equal Level.equal xu yu

  let lookup_quality (xq, _) n = xq.(n)
  let lookup_level (_, xu) n = xu.(n)

end

module Instance : sig
  type t

  val empty : t
  val is_empty : t -> bool

  val of_array : Quality.t array * Universe.t array -> t
  val to_array : t -> Quality.t array * Universe.t array
  val of_level_instance : LevelInstance.t -> t
  val abstract_instance : int * int -> t
  (** Instance of the given size made of QVar/Level.var *)

  val append : t -> t -> t
  val equal : t -> t -> bool
  val length : t -> int * int


  val hcons : t -> int * t
  val hash : t -> int

  val subst_fn : (Sorts.QVar.t -> Quality.t) * (Level.t -> Universe.t) -> t -> t

  val pr : Sorts.printer -> ?variances:Variances.t -> t -> Pp.t
  val levels : t -> Quality.Set.t * Level.Set.t

  type ('q, 'u) mask = 'q Quality.pattern array * 'u array

  val pattern_match : (int option, int option) mask -> t -> ('term, Quality.t, Universe.t) Partial_subst.t ->
                      ('term, Quality.t, Universe.t) Partial_subst.t option

end =
struct
type t = Quality.t array * Universe.t array

let empty : t = [||], [||]

module HInstancestruct =
struct
  type nonrec t = t

  let hashcons (aq, au as a) =
    let qlen = Array.length aq in
    let ulen = Array.length au in
      if Int.equal qlen 0 && Int.equal ulen 0 then 0, empty
      else
        let hq, aq' = Hashcons.hashcons_array Quality.hcons aq in
        let hu, au' = Hashcons.hashcons_array Universe.hcons au in
        let a = if aq' == aq && au' == au then a else (aq',au') in
        Hashset.Combine.combine hq hu, a

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
        let h = Universe.hash l in
          accu := Hashset.Combine.combine !accu h;
      done;
      (* [h] must be positive. *)
      let h = !accu land 0x3FFFFFFF in
        h
end


module HInstance = Hashcons.Make(HInstancestruct)

let hcons = Hashcons.simple_hcons HInstance.generate HInstance.hcons ()

let hash : t -> int = HInstancestruct.hash

let is_empty (x,y) = CArray.is_empty x && CArray.is_empty y

let append (xq,xu as x) (yq,yu as y) =
  if is_empty x then y
  else if is_empty y then x
  else Array.append xq yq, Array.append xu yu

let of_array a : t = a

let to_array (a:t) = a

let of_level_instance i =
  let (qu, us) = LevelInstance.to_array i in
  (qu, Array.map Universe.make us)

let abstract_instance n = of_level_instance (LevelInstance.abstract_instance n)
let length (aq,au) = Array.length aq, Array.length au

let subst_fn (fq, fn) (q,u as orig) : t =
  let q' = CArray.Smart.map (Quality.subst fq) q in
  let u' = CArray.Smart.map (Universe.subst_fn fn) u in
  if q' == q && u' == u then orig else q', u'

let levels (xq,xu) =
  let q = Array.fold_left (fun acc x -> Quality.Set.add x acc) Quality.Set.empty xq in
  let u = Array.fold_left (fun acc x -> Level.Set.union (Universe.levels x) acc) Level.Set.empty xu in
  q, u

let pr printer ?variances (q,u) =
  let ppu i u =
    let v = Option.map (fun v -> v.(i)) variances in
    pr_opt_no_spc VarianceOccurrence.pr v ++ Universe.pr printer.Sorts.pru u
  in
  (if Array.is_empty q then mt() else prvect_with_sep spc (Quality.pr printer.prq) q ++ strbrk " ; ")
  ++ prvecti_with_sep spc ppu u

let equal (xq,xu) (yq,yu) =
  CArray.equal Quality.equal xq yq
  && CArray.equal Universe.equal xu yu

type ('q, 'u) mask = 'q Quality.pattern array * 'u array

let pattern_match (qmask, umask) (qs, us) tqus =
  let tqus = Array.fold_left2 (fun tqus mask u -> Partial_subst.maybe_add_univ mask u tqus) tqus umask us in
  match Array.fold_left2 (fun tqus mask q -> Quality.pattern_match mask q tqus |> function Some tqs -> tqs | None -> raise_notrace Exit) tqus qmask qs with
  | tqs -> Some tqs
  | exception Exit -> None

end

let eq_sizes (a,b) (a',b') = Int.equal a a' && Int.equal b b'

module QPair = OrderedType.Pair(Quality)(Quality)

module QPairSet = Set.Make(QPair)

type 'a pconstraints_function = 'a -> 'a -> QPairSet.t * UnivConstraints.t -> QPairSet.t * UnivConstraints.t

let enforce_eq_cumul_quality a b csts =
  if Quality.equal a b then csts
  else QPairSet.add (a, b) csts

let enforce_eq_instances x y (qcs, ucs as orig) =
  let xq, xu = Instance.to_array x and yq, yu = Instance.to_array y in
  if Array.length xq != Array.length yq || Array.length xu != Array.length yu then
    CErrors.anomaly (Pp.(++) (Pp.str "Invalid argument: enforce_eq_instances called with")
                       (Pp.str " instances of different lengths."));
  let qcs' = CArray.fold_right2 enforce_eq_cumul_quality xq yq qcs in
  let ucs' = CArray.fold_right2 enforce_eq xu yu ucs in
  if qcs' == qcs && ucs' == ucs then orig else qcs', ucs'

let enforce_eq_variance_instances ~nargs variances x y (qcs,ucs as orig) =
  let xq, xu = Instance.to_array x and yq, yu = Instance.to_array y in
  let qcs' = CArray.fold_right2 enforce_eq_cumul_quality xq yq qcs in
  let ucs' = Variances.eq_constraints ~nargs variances xu yu ucs in
  if qcs' == qcs && ucs' == ucs then orig else qcs', ucs'

let enforce_leq_variance_instances ~nargs variances x y (qcs,ucs as orig) =
  let xq, xu = Instance.to_array x and yq, yu = Instance.to_array y in
  (* no variance for quality variables -> enforce_eq *)
  let qcs' = CArray.fold_right2 enforce_eq_cumul_quality xq yq qcs in
  let ucs' = Variances.leq_constraints ~nargs variances xu yu ucs in
  if qcs' == qcs && ucs' == ucs then orig else qcs', ucs'

let subst_instance_level s l =
  match Level.var_index l with
  | Some n -> (snd (Instance.to_array s)).(n)
  | None -> Universe.make l

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
  | Quality.QConstant _ | Quality.QGlobal _ -> l

let subst_instance_universe subst u =
  let ur = Universe.repr u in
  let modified = ref false in
  let rec aux u' = function
    | [] -> u'
    | (l, k) :: u ->
      let univ = subst_instance_level subst l in
      modified := true;
      aux (List.append (Universe.repr (Universe.addn univ k)) u') u
  in
  let u' = aux [] ur in
  if not !modified then u
  else Universe.unrepr u'

let subst_instance_sort u s =
  Sorts.subst_fn ((subst_instance_qvar u), (subst_instance_level u)) s

let subst_instance_relevance u r =
  Sorts.relevance_subst_fn (subst_instance_qvar u) r

let subst_instance_instance s i =
  let qs, us = Instance.to_array i in
  let qs' = Array.Smart.map (fun l -> subst_instance_quality s l) qs in
  let us' = Array.Smart.map (fun l -> subst_instance_universe s l) us in
  if qs' == qs && us' == us then i else Instance.of_array (qs', us')

let subst_instance_constraint subst_instance s (u,d,v as c) =
  let u' = subst_instance s u in
  let v' = subst_instance s v in
    if u' == u && v' == v then c
    else (u',d,v')

let subst_level_instance_level s l =
  match Level.var_index l with
  | Some n -> LevelInstance.lookup_level s n
  | None -> l

let subst_level_instance_level_universe s l =
  match Level.var_index l with
  | Some n -> Universe.make @@ LevelInstance.lookup_level s n
  | None -> Universe.make l

let subst_level_instance_qvar s v =
  match Sorts.QVar.var_index v with
  | Some n -> LevelInstance.lookup_quality s n
  | None -> Quality.QVar v

let subst_level_instance_quality s l =
  match l with
  | Quality.QVar v ->
    begin match Sorts.QVar.var_index v with
      | Some n -> LevelInstance.lookup_quality s n
      | None -> l
    end
  | _ -> l

let subst_level_instance_universe s univ =
  let f (v,n as vn) =
    let v' = subst_level_instance_level s v in
    if v == v' then vn
    else v', n
  in
  let u = Universe.repr univ in
  let u' = List.Smart.map f u in
  if u == u' then univ
  else Universe.unrepr u'

let subst_level_instance_instance s i =
  let qs, us = Instance.to_array i in
  let qs' = Array.Smart.map (fun l -> subst_level_instance_quality s l) qs in
  let us' = Array.Smart.map (fun l -> subst_level_instance_universe s l) us in
  if qs' == qs && us' == us then i else Instance.of_array (qs', us')

let subst_level_instance_sort u s =
  Sorts.subst_fn ((subst_level_instance_qvar u), (subst_level_instance_level_universe u)) s

let subst_level_instance_relevance u r =
  Sorts.relevance_subst_fn (subst_level_instance_qvar u) r

(* let subst_level_instance_constraint s (u,d,v as c) = *)
(*   let u' = subst_level_instance_universe s u in *)
(*   let v' = subst_level_instance_universe s v in *)
(*     if u' == u && v' == v then c *)
(*     else (u', d, v') *)

let subst_instance_elim_constraint =
  subst_instance_constraint subst_instance_quality

let subst_instance_univ_constraint =
  subst_instance_constraint subst_instance_universe

let subst_instance_constraints s csts =
  PConstraints.fold
    ((fun q csts -> Sorts.ElimConstraints.add (subst_instance_elim_constraint s q) csts),
     (fun u csts -> UnivConstraints.add (subst_instance_univ_constraint s u) csts))
    csts PConstraints.empty

type 'a puniverses = 'a * Instance.t
let out_punivs (x, _y) = x
let in_punivs x = (x, Instance.empty)
let eq_puniverses f (x, u) (y, u') =
  f x y && Instance.equal u u'

type bound_names = {
  quals: Names.Name.t array;
  univs: Names.Name.t array;
}
let empty_bound_names = {quals = [||]; univs =  [||]}
let append_bound_names {quals = qnames; univs = unames} {quals = qnames'; univs = unames'} =
  {quals = Array.append qnames qnames'; univs = Array.append unames unames'}
(** A context of universe levels with universe constraints,
    representing local universe variables and constraints *)

module UContext =
struct
  type t = bound_names * LevelInstance.t constrained

  let make names (univs, _ as x) : t =
    let qs, us = LevelInstance.to_array univs in
    assert (Array.length names.quals = Array.length qs && Array.length names.univs = Array.length us);
    (names, x)

  (** Universe contexts (variables as a list) *)
  let empty = (empty_bound_names, (LevelInstance.empty, PConstraints.empty))
  let is_empty (_, (univs, csts)) = LevelInstance.is_empty univs && PConstraints.is_empty csts

  let pr printer ?variances (_, (univs, csts) as uctx) =
    if is_empty uctx then mt() else
      h (LevelInstance.pr printer ?variances univs ++ str " | ") ++ h (v 0 (PConstraints.pr printer csts))

  let hcons ({quals = qnames; univs = unames}, (univs, csts)) =
    let hqnames, qnames = Hashcons.hashcons_array Names.Name.hcons qnames in
    let hunames, unames = Hashcons.hashcons_array Names.Name.hcons unames in
    let hunivs, univs = LevelInstance.hcons univs in
    let hcsts, csts = PConstraints.hcons csts in
    Hashset.Combine.combine4 hqnames hunames hunivs hcsts, ({quals = qnames; univs = unames}, (univs, csts))

  let names ((names, _) : t) = names
  let instance (_, (univs, _csts)) = univs
  let constraints (_, (_univs, csts)) = csts
  let univ_constraints (_, (_, (_,univs))) = univs
  let elim_constraints (_, (_, (elims,_))) = elims

  let union (names, (univs, csts)) (names', (univs', csts')) =
    append_bound_names names names', (LevelInstance.append univs univs', PConstraints.union csts csts')

  let size (_,(x,_)) = LevelInstance.length x

  let refine_names names' (names, x) =
    let merge_names = Array.map2 Names.(fun old refined -> match refined with Anonymous -> old | Name _ -> refined) in
    ({quals = merge_names names.quals names'.quals; univs = merge_names names.univs names'.univs}, x)

  let sort_levels a =
    Array.sort Level.compare a; a

  let sort_qualities a =
    Array.sort Quality.compare a; a

  let of_context_set f ((qctx, qcst), (levels, lcst)) =
    let csts = (qcst, lcst) in
    let qctx = sort_qualities
        (Array.map_of_list (fun q -> Quality.QVar q)
           (Sorts.QVar.Set.elements qctx))
    in
    let levels = sort_levels (Array.of_list (Level.Set.elements levels)) in
    let inst = LevelInstance.of_array (qctx, levels) in
    (f inst, (inst, csts))

  let to_context_set (_, (inst, (qcsts, lcsts))) =
    let qs, us = LevelInstance.to_array inst in
    let us = Array.fold_left (fun acc x -> Level.Set.add x acc) Level.Set.empty us in
    let qs = Array.fold_left (fun acc -> function
        | Sorts.Quality.QVar x -> Sorts.QVar.Set.add x acc
        | Sorts.Quality.(QConstant _ | QGlobal _)  -> assert false)
        Sorts.QVar.Set.empty
        qs
    in
    (qs, qcsts), (us, lcsts)

end

type universe_context = UContext.t
type 'a in_universe_context = 'a * universe_context

let hcons_universe_context = UContext.hcons

module AbstractContext =
struct
  type t = bound_names constrained

  let make names csts : t = names, csts

  let instantiate inst (names, cst) =
    let q, u = Instance.to_array inst in
    assert (Array.length q == Array.length names.quals && Array.length u = Array.length names.univs);
    subst_instance_constraints inst cst

  let names (nas, _) = nas

  let constraints (_, csts) = csts

  let hcons ({quals = qnames; univs = unames}, cst) =
    let hqnames, qnames = Hashcons.hashcons_array Names.Name.hcons qnames in
    let hunames, unames = Hashcons.hashcons_array Names.Name.hcons unames in
    let hcst, cst = PConstraints.hcons cst in
    Hashset.Combine.combine3 hqnames hunames hcst, ({quals = qnames; univs = unames}, cst)

  let empty = (empty_bound_names, PConstraints.empty)

  let is_constant (names,_) =
    Array.is_empty names.quals && Array.is_empty names.univs

  let is_empty (_, cst as ctx) =
    is_constant ctx && PConstraints.is_empty cst

  let union (names, cst) (names', cst') =
    (append_bound_names names names', PConstraints.union cst cst')

  let size (names, _) = Array.length names.quals, Array.length names.univs

  let repr (names, cst as self) : UContext.t =
    let inst = LevelInstance.abstract_instance (size self) in
    (names, (inst, cst))

  let refine_names names' (names, x) =
    let merge_names = Array.map2 Names.(fun old refined -> match refined with Anonymous -> old | Name _ -> refined) in
    ({quals = merge_names names.quals names'.quals; univs = merge_names names.univs names'.univs}, x)

  let pr printer ?variances ctx = UContext.pr printer ?variances (repr ctx)

end

type 'a univ_abstracted = {
  univ_abstracted_value : 'a;
  univ_abstracted_binder : AbstractContext.t;
}

let hcons_abstract_universe_context = AbstractContext.hcons

let map_univ_abstracted f {univ_abstracted_value;univ_abstracted_binder} =
  let univ_abstracted_value = f univ_abstracted_value in
  {univ_abstracted_value;univ_abstracted_binder}


(**********************************************************************)
(** Universe polymorphism                                             *)
(**********************************************************************)

(** A universe level substitution, note that no algebraic universes are
    involved *)

type universe_level_subst = Universe.t Level.Map.t

(** Substitutions. *)

(** A universe level to universe substitution *)

let empty_level_subst = Level.Map.empty
let is_empty_level_subst = Level.Map.is_empty

(** Substitution functions *)

(** With level to universe substitutions. *)
let subst_univs_level_level subst l =
  try Level.Map.find l subst
  with Not_found -> Universe.make l

let subst_univs_level_universe (subst : Universe.t Level.Map.t) u =
  let modified = ref false in
 let rec aux u' = function
    | [] -> u'
    | (l, k as e) :: tl ->
      match Level.Map.find l subst with
      | exception Not_found -> aux (e :: u') tl
      | univ ->
        modified := true;
        aux (List.append (Universe.repr (Universe.addn univ k)) u') tl
  in
  let u' = aux [] (Universe.repr u) in
  if not !modified then u
  else Universe.sort u'

let subst_univs_level_constraint subst (u,d,v) =
  let u' = subst_univs_level_universe subst u
  and v' = subst_univs_level_universe subst v in
    if Universe.equal u' v' then None
    else Some (u',d,v')

let subst_sort_level_qvar subst qv =
  match Sorts.QVar.Map.find_opt qv subst with
  | None -> Quality.QVar qv
  | Some q -> q

let subst_sort_level_quality subst = function
  | Quality.(QConstant _ | QGlobal _) as q -> q
  | Quality.QVar q ->
    subst_sort_level_qvar subst q

let subst_univs_elim_constraint subst (q1,k,q2) =
  let q1 = subst_sort_level_quality subst q1 in
  let q2 = subst_sort_level_quality subst q2 in
  (q1,k,q2)

let subst_univs_constraints usubst uctx =
  let fold c accu = Option.fold_right UnivConstraints.add (subst_univs_level_constraint usubst c) accu in
  Univ.UnivConstraints.fold fold uctx Univ.UnivConstraints.empty

let subst_elim_constraints qsubst qctx =
  let fold c accu = Sorts.ElimConstraints.add (subst_univs_elim_constraint qsubst c) accu in
  Sorts.ElimConstraints.fold fold qctx Sorts.ElimConstraints.empty

let subst_poly_constraints (qsubst, usubst) (qctx, uctx) =
  (subst_elim_constraints qsubst qctx, subst_univs_constraints usubst uctx)

(** Pretty-printing *)

let pr_universe_level_subst prl =
  Level.Map.pr prl (fun u -> str" := " ++ Universe.pr prl u ++ spc ())

let pr_quality_level_subst (printer:Quality.printer) l =
  let open Pp in
  h (prlist_with_sep fnl (fun (u,v) -> printer.prvar u ++ str " := " ++ Sorts.Quality.pr printer v)
       (Sorts.QVar.Map.bindings l))

type sort_level_subst = Quality.t Sorts.QVar.Map.t * universe_level_subst

let is_empty_sort_subst (qsubst,usubst) = Sorts.QVar.Map.is_empty qsubst && is_empty_level_subst usubst

let empty_sort_subst = Sorts.QVar.Map.empty, empty_level_subst

let subst_sort_level_instance (qsubst,usubst) i =
  let i' = Instance.subst_fn (Quality.subst_fn qsubst, Universe.make_subst_fn usubst) i in
  if i == i' then i
  else i'

let subst_instance_sort_level_subst s (i : sort_level_subst) =
  let qs, us = i in
  let qs' = Sorts.QVar.Map.map (fun l -> subst_instance_quality s l) qs in
  let us' = Level.Map.map (fun l -> subst_instance_universe s l) us in
  if qs' == qs && us' == us then i else (qs', us')

let subst_univs_level_abstract_universe_context subst (inst, csts) =
  inst, subst_poly_constraints subst csts

let subst_sort_level_qvar (qsubst,_) qv =
  match Sorts.QVar.Map.find_opt qv qsubst with
  | None -> Quality.QVar qv
  | Some q -> q

let subst_sort_level_quality subst = function
  | Sorts.Quality.(QConstant _ | QGlobal _) as q -> q
  | Sorts.Quality.QVar q ->
    subst_sort_level_qvar subst q

let subst_sort_level_sort (_,usubst as subst) s =
  let fq qv = subst_sort_level_qvar subst qv in
  let fu u = subst_univs_level_level usubst u in
  Sorts.subst_fn (fq,fu) s

let subst_sort_level_relevance subst r =
  Sorts.relevance_subst_fn (subst_sort_level_qvar subst) r

let subst_sort_level_variance_occurrence usubst b =
  let open VarianceOccurrence in
  let upd qv = Some (subst_sort_level_qvar usubst qv) in
  let under_impred_qvars = update_impred_qvars upd b.under_impred_qvars in
  { b with under_impred_qvars }

let subst_sort_level_variances usubst vs =
  Array.map (subst_sort_level_variance_occurrence usubst) vs

let make_instance_subst i =
  let qarr, uarr = LevelInstance.to_array i in
  let qsubst =
    Array.fold_left_i (fun i acc l ->
      let l = match l with Quality.QVar l -> l | _ -> assert false in
      Sorts.QVar.Map.add l (Quality.var i) acc)
      Sorts.QVar.Map.empty qarr
  in
  let usubst =
    Array.fold_left_i (fun i acc l ->
      Level.Map.add l (Universe.make (Level.var i)) acc)
      Level.Map.empty uarr
  in
  qsubst, usubst

let make_abstract_level_instance ctx =
  UContext.instance (AbstractContext.repr ctx)
let make_abstract_instance ctx =
  Instance.of_level_instance (make_abstract_level_instance ctx)

let abstract_universes uctx =
  let nas = UContext.names uctx in
  let instance = UContext.instance uctx in
  let subst = make_instance_subst instance in
  let cstrs = subst_poly_constraints subst (UContext.constraints uctx)
  in
  let ctx = (nas, cstrs) in
  instance, ctx

let pr_universe_context = UContext.pr
let pr_abstract_universe_context = AbstractContext.pr
