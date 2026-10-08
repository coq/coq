(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Declarations
open Constr
open Univ
open UVars
open Variance
open Util

let debug = CDebug.create ~name:"inferCumul" ()
let debug_infer_def = CDebug.create ~name:"inferCumul_infer_def" ()
let debug_infer_term = CDebug.create ~name:"inferCumul_infer_term" ()
let debug_infer_term_variances = CDebug.create ~name:"inferCumul_infer_term_variances" ()

type cumul_pb =
  | Conv | Cumul | InvCumul

let pr_cumul_pb = Pp.(function
  | Conv -> str"="
  | Cumul -> str"≤"
  | InvCumul -> str"≥")

(** Not the same as Type_errors.BadVariance because we don't have the env where we raise. *)
exception BadVariance of Level.t * VariancePos.t * VariancePos.t
(* some ocaml bug is triggered if we make this an inline record *)

exception NotInferring

type mode = Check | Infer
let pr_mode m =
  let open Pp in
  match m with
  | Check -> str"check"
  | Infer -> str"infer"

type infer_binders = (mode * (VariancePair.t option * int list))

type impred_qvars = UVars.impred_qvars
(** Set of potentially impredicative QVars under which the universe lives.
  If there is an occurrence under a non-impredicative QVar somewhere, this is empty. *)

type infer_variance_occurrence =
  { infer_binders : infer_binders;
    infer_topfix_binders : infer_binders; (* Variances in the term's toplevel fixpoint binders treated as lambdas (contravariance allowed)  *)
    infer_term : mode * UVars.VariancePair.t option;
    infer_type : mode * UVars.VariancePair.t option;
    infer_under_impred_qvars : impred_qvars }

type variances = infer_variance_occurrence Univ.Level.Map.t
let default_occ =
  { infer_binders = (Infer, (None, []));
    infer_topfix_binders = (Infer, (None, []));
    infer_term = (Infer, None);
    infer_type = (Infer, None);
    infer_under_impred_qvars = None }

let make_checked_occ ~infer_in_type
  UVars.VarianceOccurrence.{ in_binders; in_topfix_binders; in_term; in_type; under_impred_qvars } =
  { infer_binders = ((if infer_in_type then Infer else Check), in_binders);
    infer_topfix_binders = Check, in_topfix_binders;
    infer_term = Check, in_term;
    infer_type = (if infer_in_type then Infer else Check), in_type;
    infer_under_impred_qvars = under_impred_qvars }

let forget_infer_variance_occurrence
  { infer_binders; infer_topfix_binders; infer_term; infer_type;
    infer_under_impred_qvars = impred_qvars } =
  UVars.VarianceOccurrence.{ in_binders = snd infer_binders;
    in_topfix_binders = snd infer_topfix_binders;
    in_term = (snd infer_term);
    in_type = snd infer_type;
    under_impred_qvars = impred_qvars }

let of_variance_occurrences ~infer_in_type (vs : (Level.t * UVars.VarianceOccurrence.t option) array) : variances =
  Array.fold_left (fun vs (l, vocc) ->
    Level.Map.add l (Option.cata (make_checked_occ ~infer_in_type) default_occ vocc) vs) Level.Map.empty vs

let pr_variance_occurrence (occ : infer_variance_occurrence) =
  let open Pp in
  let pr_binders is_fix (m, (v, bs)) =
    if List.is_empty bs then [] else
    [pr_mode m ++ str":" ++ pr_opt VariancePair.pr v ++ spc () ++ str "in" ++ spc () ++
      prlist_with_sep pr_comma (fun i -> pr_nth (succ i)) bs ++ (if is_fix then str" fix " else mt()) ++ str (String.plural (List.length bs) " binder")] in
  let pr_term (m, v) = match v with
    | None -> []
    | Some v -> [pr_mode m ++ str": " ++ VariancePair.pr v ++ str" in term"]
  in
  let pr_type (m, v) =
    match v with
    | None -> []
    | Some v -> [pr_mode m ++ str": " ++ VariancePair.pr v ++ str" in type"]
  in
  let pr_impred =
    match occ.infer_under_impred_qvars with
    | Some _ as x -> [UVars.pr_impred_qvars x]
    | None -> []
  in
  let variances = pr_binders false occ.infer_binders @ pr_binders true occ.infer_topfix_binders
    @ pr_term occ.infer_term @ pr_type occ.infer_type @ pr_impred in
    if List.is_empty variances then mt ()
    else hov 0 (str": " ++ prlist_with_sep pr_comma identity variances)

let make_checked_occ (variance, position) =
  let open Position in
  let open VariancePair in
  let variance = { cumul_variance = variance; typing_variance = Irrelevant } in
  match position with
  | InBinder i ->
    { default_occ with infer_binders = (Check, (Some variance, [i])) }
  | InTopFixBinder i ->
    { default_occ with infer_topfix_binders = (Check, (Some variance, [i])) }
  | InType ->
    { default_occ with infer_type = Check, Some variance }
  | InTerm ->
    { default_occ with infer_term = Check, Some variance }

(** Level variances *)

(* The position records the last position in the term where the variable was used relevantly. *)

let empty_variances = Univ.Level.Map.empty
let is_empty_variances = Univ.Level.Map.is_empty

let pr_variances prl variances =
  Univ.Level.Map.pr prl pr_variance_occurrence variances

let mode_sup x y =
  match x, y with
  | Check, _ -> Check
  | _, Check -> Check
  | Infer, Infer -> Infer

let rec union_binders l1 l2 =
  match l1, l2 with
  | [], l2 -> l2
  | l1, [] -> l1
  | i1 :: t1, i2 :: t2 ->
    let c = Int.compare i1 i2 in
    if Int.equal c 0
    then i1 :: union_binders t1 t2
    else if c <= 0
    then i1 :: union_binders t1 l2
    else i2 :: union_binders l1 t2


let sup_binders (mode, (bindersv, binders)) (mode', (bindersv', binders')) =
  (mode_sup mode mode', (Option.union VariancePair.sup bindersv bindersv', union_binders binders binders'))

let sup_occs { infer_binders; infer_topfix_binders; infer_term; infer_type;
   infer_under_impred_qvars }
  { infer_binders = infer_binders'; infer_topfix_binders = infer_topfix_binders'; infer_term = infer_term';
    infer_type = infer_type';
    infer_under_impred_qvars = infer_under_impred_qvars' } =
  let infer_binders = sup_binders infer_binders infer_binders' in
  let infer_topfix_binders = sup_binders infer_topfix_binders infer_topfix_binders' in
  let mode_var_sup (mode, v) (mode', v') = (mode_sup mode mode', Option.union VariancePair.sup v v') in
  let infer_term = mode_var_sup infer_term infer_term' in
  let infer_type = mode_var_sup infer_type infer_type' in
  let infer_under_impred_qvars = union_impred_qvars infer_under_impred_qvars infer_under_impred_qvars' in
  { infer_binders; infer_topfix_binders; infer_term; infer_type;
    infer_under_impred_qvars }

let union_variances : variances -> variances -> variances =
  let union _ x y = Some (sup_occs x y) in
  Univ.Level.Map.union union

let sup_vopt x y =
  match x, y with
  | None, None -> x
  | Some _, None -> x
  | None, Some _ -> y
  | Some v, Some v' -> Some (UVars.Variance.sup v v')

let max_binder = function
  | [] -> None
  | v :: vs -> Some (List.fold_left max v vs)
let binder_pos (infer_binders, pos) =
  match infer_binders with
  | None -> None
  | Some v ->
    match max_binder pos with
    | None -> None
    | Some i -> Some (i, v)

let occurrence_to_variance_pos
  ({ infer_binders = (modeb, infer_binders);
     infer_topfix_binders = (modef, infer_fix_binders);
     infer_term = (modet, infer_term);
     infer_type = (modety, infer_type);
     infer_under_impred_qvars = _ } : infer_variance_occurrence) =
  let open VariancePair in
  let open Position in
  let infer_binders =
    let (v, b) = infer_binders in
    let (v', b') = infer_fix_binders in
    sup_vopt (Option.map cumul_variance v) (Option.map (fun _ -> Invariant) v'), b @ b'
  in
  let binders = binder_pos infer_binders in
  match binders, infer_term, infer_type with
  | in_binder, Some v, _ when (v.cumul_variance <> Variance.Irrelevant) ->
     (mode_sup (mode_sup modeb modef) modet, (Option.get (sup_vopt (Option.map snd in_binder) (Some v.cumul_variance)), InTerm))
  | Some (i, v), _, _ when v <> Irrelevant -> (modeb, (v, InBinder i))
  | _, _, infer_type -> (modety, (Option.cata cumul_variance Irrelevant infer_type, InType))

let term_type_variances
  ({ infer_binders = (_, (infer_binders, _)); infer_topfix_binders = (_, (infer_fix_binders, _)); infer_term = (_, infer_term); infer_type = (_, infer_type);
     infer_under_impred_qvars = _ } : infer_variance_occurrence) =
  let open VariancePair in
  sup_vopt (Option.map (fun _ -> Invariant) infer_fix_binders) (Option.map cumul_variance infer_term),
  sup_vopt (Option.map typing_variance infer_binders) (Option.map typing_variance infer_type),
  sup_vopt (Option.map typing_variance infer_binders) (Option.map typing_variance infer_term)

type pre_variances = (Univ.Level.t * VarianceOccurrence.t option) array
type infer_variance_occurrences = infer_variance_occurrence array

module Inf : sig
  type status

  val pr : (Level.t -> Pp.t) -> status -> Pp.t

  val infer_level_eq : typing_variance:Variance.t -> impred_qvars -> Level.t -> status -> status
  val infer_level_leq : typing_variance:Variance.t -> impred_qvars -> Level.t -> status -> status
  val infer_level_geq : typing_variance:Variance.t -> impred_qvars -> Level.t -> status -> status
  val infer_level_typing_variance : typing_variance:Variance.t -> impred_qvars -> Level.t -> status -> status

  val get_infer_mode : status -> bool
  val set_infer_mode : bool -> status -> status

  val set_position : Position.t -> status -> status
  val get_position : status -> Position.t

  val start : ?volatile:TransparentState.t -> infer_in_type:bool -> pre_variances -> Position.t -> status
  val start_variances : ?volatile:TransparentState.t -> variances -> Position.t -> status

  val start_inference : ?volatile:TransparentState.t -> Level.Set.t -> Position.t -> status

  val volatile : status -> TransparentState.t

  val inferred : status -> variances
  val finish : Environ.env -> status -> UVars.variances

end = struct

  (**
     Each local universe is either in the [univs] map or is Invariant.

     If [univs] is empty all universes are Invariant and there is nothing more to do,
     so we stop by raising [TrivialVariance]. The [soft] check comes before that.
  *)
  type status = {
    orig_array : pre_variances;
    univs : variances;
    infer_mode : bool;
    position : Position.t;
    volatile : TransparentState.t
  }

  let univs (s : status) = s.univs

  let get_infer_mode v = v.infer_mode
  let set_infer_mode b v = if v.infer_mode == b then v else {v with infer_mode=b}

  let get_position v = v.position
  let set_position p v = if v.position == p then v else {v with position=p}

  let pr prl (status : status) = pr_variances prl status.univs

  let get_variance_at_position variances u =
    let open VariancePair in
    let get_variances v = Option.default irrelevant_pair v in
    match Level.Map.find_opt u (univs variances) with
    | None -> None
    | Some occ ->
      let open Position in
      match variances.position with
      | InBinder _ ->
        let (mode, (v, _)) = occ.infer_binders in
        Some (mode, get_variances v)
      | InTopFixBinder _ ->
        let (mode, (v, _)) = occ.infer_topfix_binders in
        Some (mode, get_variances v)
      | InTerm -> let (mode, v) = occ.infer_term in
        Some (mode, get_variances v)
      | InType -> let (mode, v) = occ.infer_type in
        Some (mode, get_variances v)

  let update_binder_variance (_, binders) i variance =
    let rec aux binders =
      match binders with
      | [] -> [i]
      | i' :: binders' ->
        match Int.compare i i' with
        | 0 -> i :: binders'
        | x when x < 0 -> i :: binders
        | _ -> i' :: aux binders'
    in (Some variance, aux binders)

  let update_variance variances q u variance =
    let upd = function
      | None -> assert false
      | Some occs ->
        let open Position in
        let infer_under_impred_qvars = union_impred_qvars occs.infer_under_impred_qvars q in
        let occs' = match variances.position with
        | InBinder i ->
          let (mode, binders) = occs.infer_binders in
          { occs with infer_binders = (mode, update_binder_variance binders i variance);
            infer_under_impred_qvars }
        | InTopFixBinder i ->
          let (mode, binders) = occs.infer_topfix_binders in
          { occs with infer_topfix_binders = (mode, update_binder_variance binders i variance);
            infer_under_impred_qvars }
        | InTerm ->
          let (mode, _) = occs.infer_term in
          { occs with infer_term = (mode, Some variance);
            infer_under_impred_qvars }
        | InType ->
          let (mode, _) = occs.infer_type in
          { occs with infer_type = (mode, Some variance);
            infer_under_impred_qvars }
        in Some occs'
    in {variances with univs = Level.Map.update u upd variances.univs}

  let infer_level_cmp ~typing_variance:tq q variance u variances =
    let open VariancePair in
    match get_variance_at_position variances u with
    | None -> variances
    | Some (Check, expected) ->
      if Variance.le variance expected.cumul_variance then variances
      else raise (BadVariance (u, (expected.cumul_variance, variances.position), (variance, variances.position)))
    | Some (Infer, inferred) ->
      if not variances.infer_mode then raise NotInferring;
      let v =
        { cumul_variance = Variance.sup inferred.cumul_variance variance;
          typing_variance = Variance.sup inferred.typing_variance tq }
      in
      update_variance variances q u v

  let infer_level_eq ~typing_variance q u variances = infer_level_cmp ~typing_variance q Invariant u variances
  let infer_level_leq ~typing_variance q u variances = infer_level_cmp ~typing_variance q Covariant u variances
  let infer_level_geq ~typing_variance q u variances = infer_level_cmp ~typing_variance q Contravariant u variances

  let infer_level_typing_variance ~typing_variance:tq q u (variances : status) =
    let open VariancePair in
    let upd = function
      | None -> None
      | Some occ ->
        let (mode, vs) = occ.infer_term in
        let upd_typing v = { v with typing_variance = Variance.sup tq v.typing_variance } in
        Some { occ with infer_term = (mode, Some (upd_typing (Option.default irrelevant_pair vs)));
        infer_under_impred_qvars = union_impred_qvars occ.infer_under_impred_qvars q }
    in
    { variances with univs = Level.Map.update u upd variances.univs }

  let pr_pre_variances =
    let open Pp in
    let open Univ in
    let pr (l, v) = Level.raw_pr l ++ str " : " ++ pr_opt VarianceOccurrence.pr v in
    prvect_with_sep spc pr

  let start ?(volatile=TransparentState.empty) ~infer_in_type univs position =
    debug Pp.(fun () -> str"Starting from variances: " ++ pr_pre_variances univs);
    { univs = of_variance_occurrences ~infer_in_type univs; orig_array = univs; infer_mode = true; position;
      volatile }

  let start_variances ?(volatile=TransparentState.empty) univs position =
    { univs; orig_array = [| |]; infer_mode = true; position; volatile}

  let start_inference ?(volatile=TransparentState.empty) levels position =
    let univs = Level.Set.fold (fun level -> Level.Map.add level default_occ) levels Level.Map.empty in
    { univs; orig_array = [||]; infer_mode=true; position; volatile}

  let variance_occurrence_to_variance_pos VarianceOccurrence.{ in_binders; in_topfix_binders; in_term; in_type; under_impred_qvars = _ } =
    let open Position in
    let open VariancePair in
    let binders = binder_pos in_binders in
    let in_term =
      let (v, _b) = in_topfix_binders in
      sup_vopt (Option.map (fun _ -> Invariant) v) (Option.map cumul_variance in_term)
    in
    match binders, in_term, in_type with
    | in_binder, Some v, _ when (v <> Variance.Irrelevant) -> (Option.get (sup_vopt (Option.map (fun inb -> cumul_variance (snd inb)) in_binder) (Some v)), InTerm)
    | Some (i, v), _, _ when v.cumul_variance <> Irrelevant -> (v.cumul_variance, InBinder i)
    | _, _, in_type -> (Option.cata cumul_variance Irrelevant in_type, InType)

  let variance_of_occ u expected occ =
    let imode, inferred = occurrence_to_variance_pos occ in
    match expected with
    | None -> inferred
    | Some expected ->
      let expectedvpos = variance_occurrence_to_variance_pos expected in
      if imode == Infer || VariancePos.le inferred expectedvpos then expectedvpos
      else raise (BadVariance (u, expectedvpos, inferred))

  let to_variance_opt u expected o =
    Option.cata (fun occ -> variance_of_occ u expected occ) (Irrelevant,Position.InTerm) o

  let volatile variances = variances.volatile

  let inferred (variances : status) = variances.univs

  let finish env (variances : status) =
    try
      let arr =
        Array.map
          (fun (u,expected) ->
            let occ = Level.Map.find_opt u variances.univs in
            Option.default VarianceOccurrence.default_occ (Option.map forget_infer_variance_occurrence occ),
            to_variance_opt u expected occ)
          variances.orig_array
      in
      let vs, _apps = Array.split arr in
      Variances.make vs
  with BadVariance (lev, expected, actual) ->
    Type_errors.error_bad_variance env ~lev ~expected ~actual

end
open Inf

type is_type = IsType | IsTerm

let instance_univs u = snd (Instance.to_array u)

let infer_generic_instance_eq gr variances u =
  debug_infer_term_variances Pp.(fun () -> str"infer_generic_instance_eq: " ++ str " for " ++
                                             pr_opt Names.GlobRef.print gr ++
                                             Instance.pr Sorts.raw_printer u
  );
  Array.fold_left (fun variances u ->
    Level.Set.fold (fun l -> infer_level_eq ~typing_variance:Invariant None l) (Universe.levels u) variances)
    variances (instance_univs u)

let extend_con_instance cb u =
  Instance.append (Instance.of_level_instance cb.const_univ_hyps) u

let extend_ind_instance mib u =
  Instance.append (Instance.of_level_instance mib.mind_univ_hyps) u

let extended_mind_variance mind =
  match Declareops.(universes_variances (inductive_universes mind)), mind.mind_sec_variance with
  | None, None -> None
  | Some _ as variance, None -> variance
  | None, Some _ -> assert false
  | Some variance, Some sec_variance -> Some (UVars.Variances.append sec_variance variance)

let extend_application nargs hyps =
  match nargs with
  | FullyApplied -> FullyApplied
  | NumArgs n -> NumArgs (Context.Named.nhyps hyps + n)

let extended_const_variance cb nargs =
  match Declareops.universes_variances cb.const_universes, cb.const_sec_variance with
  | None, None -> None
  | Some variance, None -> Some (variance, nargs)
  | None, Some _ -> assert false
  | Some variance, Some sec_variance ->
    Some (UVars.Variances.append sec_variance variance,
      extend_application nargs cb.const_hyps)

let compute_impred_qvars qs vocc =
  let vars = UVars.VarianceOccurrence.under_impred_qvars vocc in
  update_impred_qvars (fun qv -> Option.map (fun idx -> qs.(idx)) (Sorts.QVar.var_index qv)) vars

(** Compute variances from f@{u1 ... un} knowing f@{l1(vn) ... ln(vn)} variance information *)
let infer_cumulative_instance gr cv_pb (is_type, typing_v) nargs gvariances variances u =
  let qs, us = Instance.to_array u in
  debug_infer_term_variances Pp.(fun () -> str"infer_cumulative_instance: " ++ Variances.pr gvariances ++ str " for " ++
    Names.GlobRef.print gr ++ (match nargs with FullyApplied -> str"fully applied" | NumArgs n -> str" applied to " ++ int n ++ str" arguments:") ++
    Instance.pr Sorts.raw_printer u ++
    str" in typing variance position " ++ Variance.pr typing_v ++
    str " is_type = " ++ if is_type == IsType then str "IsType" else str "IsTerm");
  Array.fold_left2 (fun variances vocc u ->
    let input_univ, VariancePair.{ cumul_variance; typing_variance } = VarianceOccurrence.typing_and_cumul_variance_app ~with_type:false nargs vocc in
    debug_infer_term_variances Pp.(fun () -> str"infer_cumulative_instance, for: " ++ Universe.raw_pr u ++
      str" typing variance " ++ Variance.pr typing_variance ++
      str" cumul variance " ++ Variance.pr cumul_variance);
    let q = compute_impred_qvars qs vocc in
    let typing_variance =
      if input_univ then (* The level is an input of the application
          and can hence be determined by the arguments types *)
        Irrelevant
      else if cv_pb == Cumul then
        (* The level is an output of the application *)
        cumul_variance
      else (* cv_pb == Conv *)
        if cumul_variance == Irrelevant then Irrelevant
        else Invariant
(*
      else
        match typing_v with
      | Invariant -> if typing_variance == Irrelevant then Irrelevant else Invariant
      | Irrelevant -> assert false
      | Covariant -> typing_variance
      | Contravariant -> Variance.opp typing_variance  *)
    in
    match cv_pb, cumul_variance with
    | _, Irrelevant ->
      if typing_variance != Irrelevant then Level.Set.fold (infer_level_typing_variance ~typing_variance q) (Universe.levels u) variances else variances
    | _, Invariant
    | Conv, (Covariant | Contravariant) ->
      (* Co/contravariant in invariant position, becomes invariant *)
      Level.Set.fold (infer_level_eq ~typing_variance q) (Universe.levels u) variances
    | Cumul, Covariant ->
      (* Covariant in covariant position -> covariant *)
      Level.Set.fold (infer_level_leq ~typing_variance q) (Universe.levels u) variances
    | Cumul, Contravariant ->
      (* Contravariant in covariant position -> contravariant *)
      Level.Set.fold (infer_level_geq ~typing_variance q) (Universe.levels u) variances
    | InvCumul, Contravariant ->
      (* Contravariant in contravariant position -> covariant *)
      Level.Set.fold (infer_level_leq ~typing_variance q) (Universe.levels u) variances
    | InvCumul, Covariant ->
      (* Covariant in contravariant position -> contravariant *)
      Level.Set.fold (infer_level_geq ~typing_variance q) (Universe.levels u) variances)
    variances
    (Variances.repr gvariances)
    us

let inductive_variances env ind u =
  if not (Environ.mem_mind (fst ind) env) then
    None
  else
    let mind = Environ.lookup_mind (fst ind) env in
    let u = extend_ind_instance mind u in
    match extended_mind_variance mind with
    | None -> None
    | Some mind_variance -> Some (mind_variance, u)

let infer_inductive_instance cv_pb variance env variances ind nargs u =
  match inductive_variances env ind u with
  | None -> infer_generic_instance_eq (Some (Names.GlobRef.IndRef ind)) variances u
  | Some (mind_variance, u) -> infer_cumulative_instance (Names.GlobRef.IndRef ind) cv_pb variance (UVars.NumArgs nargs) mind_variance variances u

let constructor_variances _mind _ind _ctor variance =
  (* let npars = mind.Declarations.mind_nparams in *)
  (* let nargs = mind.Declarations.mind_packets.(ind).Declarations.mind_consnrealargs.(ctor - 1) in *)
  let open VarianceOccurrence in
  let map vocc = { vocc with in_type = vocc.in_term; in_term = None } in
  Variances.make (Array.map map (Variances.repr variance))

let infer_constructor_instance_eq env variance variances ((mi,ind),ctor as c) nargs u =
  let gr = Names.GlobRef.ConstructRef c in
  if not (Environ.mem_mind mi env) then
    infer_generic_instance_eq (Some gr) variances u
  else
  let mind = Environ.lookup_mind mi env in
  let u = extend_ind_instance mind u in
  match extended_mind_variance mind with
  | None -> infer_generic_instance_eq (Some gr) variances u
  | Some mind_variance ->
    let cstr_variance = constructor_variances mind ind ctor mind_variance in
    infer_cumulative_instance gr Cumul variance (UVars.NumArgs nargs) cstr_variance variances u

    (*if not (Int.equal (UCompare.constructor_cumulativity_arguments (mind, ind, ctor)) nargs)
    then infer_generic_instance_eq variances u
    else variances (* constructors are convertible at common supertype *) *)

let infer_sort cv_pb (_is_type, typing_variance) variances s =
  let impred_qvars = Some (impred_qvars_of_quality (Sorts.quality s)) in
  let levels = Sorts.levels s in
  match cv_pb with
  | Conv ->
    Level.Set.fold (infer_level_eq ~typing_variance impred_qvars) levels variances
  | Cumul ->
    Level.Set.fold (infer_level_leq ~typing_variance impred_qvars) levels variances
  | InvCumul ->
    Level.Set.fold (infer_level_geq ~typing_variance impred_qvars) levels variances

let infer_constant cv_pb variance env nargs variances has_def (con,u) =
  let cb = Environ.lookup_constant con env in
  let u = extend_con_instance cb u in
  let gr = Names.GlobRef.ConstRef con in
  match extended_const_variance cb nargs with
  | None ->
    let variances = if has_def then set_infer_mode false variances else variances in
    infer_generic_instance_eq (Some gr) variances u
  | Some (cst_variance, nargs) -> infer_cumulative_instance gr cv_pb variance nargs cst_variance variances u

let whd_stack (infos, tab) hd stk = CClosure.whd_stack infos tab hd stk

(* let flip_pb = function
  | Conv -> Conv
  | Cumul -> InvCumul
  | InvCumul -> Cumul *)

exception Expand

let rec infer_fterm cv_pb (variance : is_type * Variance.t) infos variances hd stk =
  Control.check_for_interrupt ();
  let hd,stk = whd_stack infos hd stk in
  let open CClosure in
  let push_relevance (infos, tab) n = (push_relevance infos n, tab) in
  let push_relevances (infos, tab) n = (push_relevances infos n, tab) in
  (* debug_infer_term Pp.(fun () -> str"infer_term of: " ++ debug_print (CClosure.term_of_fconstr (zip hd stk))); *)
  (* debug_infer_term Pp.(fun () -> str"infer_term of head: " ++ debug_print (CClosure.term_of_fconstr hd)); *)
  match fterm_of hd with
  | FAtom a ->
    begin match kind a with
      | Sort s -> infer_sort cv_pb variance variances s
      | Meta _ -> infer_stack variance infos variances stk
      | _ -> assert false
    end
  | FEvar (_, _, usubs, _) ->
    let variances = infer_generic_instance_eq None variances (snd usubs) in
    infer_stack variance infos variances stk
  | FRel _ -> infer_stack variance infos variances stk
  | FInt _ -> infer_stack variance infos variances stk
  | FFloat _ -> infer_stack variance infos variances stk
  | FString _ -> infer_stack variance infos variances stk
  | FFlex Names.(RelKey _ | VarKey _ as fl) ->
    (* We could try to lazily unfold but then we have to analyse the
       universes in the bodies, not worth coding at least for now. *)
    begin match unfold_ref_with_args (fst infos) (snd infos) fl stk with
    | Some (hd,stk) -> infer_fterm cv_pb variance infos variances hd stk
    | None -> infer_stack variance infos variances stk
    end
  | FFlex (Names.ConstKey con as fl) ->
    begin
      if not (Environ.mem_constant (fst con) (info_env (fst infos))) then
        let variances = infer_generic_instance_eq (Some (ConstRef (fst con))) variances (snd con) in
        let variances = infer_stack variance infos variances stk in
        variances
      else
      let def = unfold_ref_with_args (fst infos) (snd infos) fl stk in
      try
        if TransparentState.is_transparent_constant (Inf.volatile variances) (fst con) then raise Expand else
        let infer_mode = get_infer_mode variances in
        let nargs = stack_args_size stk in
        let variances = infer_constant cv_pb variance (info_env (fst infos)) (UVars.NumArgs nargs) variances (Option.has_some def) con in
        let variances = set_infer_mode infer_mode variances in
        infer_stack variance infos variances stk
      with BadVariance _ | Expand | NotInferring as e ->
      match def with
      | None -> raise e
      | Some (hd,stk) ->
        debug_infer_term Pp.(fun () -> str"expanding constant: " ++ Names.GlobRef.print (Names.GlobRef.ConstRef (fst con)));
        infer_fterm cv_pb variance infos variances hd stk
    end
  | FProj (_,_,c) ->
    let variances = infer_fterm Conv variance infos variances c [] in
    infer_stack variance infos variances stk
  | FLambda _ ->
    let (na,ty,bd) = destFLambda mk_clos hd in
    let variances = infer_fterm Conv (IsType, Invariant) infos variances ty [] in
    infer_fterm cv_pb variance (push_relevance infos na) variances bd []
  | FProd (na,dom,codom,e) ->
    let na = usubst_binder e na in
    let variances = infer_fterm Conv (IsType, Invariant) infos variances dom [] in
    infer_fterm cv_pb variance (push_relevance infos na) variances (mk_clos (CClosure.usubs_lift e) codom) []
  | FInd (ind, u) ->
    let variances =
      let nargs = stack_args_size stk in
      infer_inductive_instance cv_pb variance (info_env (fst infos)) variances ind nargs u
    in
    infer_stack variance infos variances stk
  | FConstruct ((ctor,u),args) ->
    assert (List.is_empty stk);
    let variances =
      let nargs = Array.length args in
      infer_constructor_instance_eq (info_env (fst infos)) variance variances ctor nargs u
    in
    infer_stack (fst variance, Invariant) infos variances (append_stack args stk)
  | FFix ((_,(na,tys,cl)),e) | FCoFix ((_,(na,tys,cl)),e) ->
    let n = Array.length cl in
    let variances = infer_vect Conv variance infos variances (Array.map (mk_clos e) tys) in
    let le = CClosure.usubs_liftn n e in
    let variances =
      let na = Array.map (usubst_binder e) na in
      let infos = push_relevances infos na in
      infer_vect Conv variance infos variances (Array.map (mk_clos le) cl)
    in
    infer_stack variance infos variances stk
  | FArray (u,elemsdef,ty) ->
    let variances =
      infer_cumulative_instance (Names.GlobRef.VarRef (Names.Id.of_string "array")) cv_pb (IsType, snd variance) FullyApplied CPrimitives.array_variances variances u
    in
    let variances = infer_fterm cv_pb (IsType, Covariant) infos variances ty [] in
    let elems, def = Parray.to_array elemsdef in
    let variances = infer_fterm Conv (IsTerm, Invariant) infos variances def [] in
    let variances = infer_vect Conv (IsTerm, Invariant) infos variances elems in
    infer_stack variance infos variances stk


  | FCaseInvert (ci, u, pms, p, iv, _, br, e) ->
    (* don't check discriminee: inductive is guaranteed proof irrelevant *)    
    let mib = Environ.lookup_mind (fst ci.ci_ind) (info_env (fst infos)) in
    let (_, (p, _), _, _, br) =
      Inductive.expand_case_specif mib (ci, u, pms, p, NoInvert, mkProp, br)
    in
    let infer c variances = infer_fterm Conv (IsTerm, Invariant) infos  variances (mk_clos e c) [] in
    let variances = Array.fold_left (fun variances i ->
        infer_fterm Conv (IsTerm, Invariant) infos variances i [])
        variances (get_invert iv)
    in
    let variances = infer p variances in
    let variances = Array.fold_right infer br variances in
    infer_stack variance infos variances stk

  (* | FCaseInvert (ci, u, _, p, _, _, br, e) -> *)
     (* infer_case cv_pb variance infos variances ci u p br e *)

  | FLetIn (_na, b, _ty, body, usubs) ->
     if Vars.noccurn 1 body then
       infer_fterm cv_pb variance infos variances (mk_clos usubs (Vars.subst1 (Constr.mkSort Sorts.prop) body)) stk
     else begin
         debug_infer_term Pp.(fun () -> str"infer_term at LetIn: " ++ Inf.pr Level.raw_pr variances ++ Constr.debug_print (CClosure.term_of_fconstr b));
         let variances = infer_fterm Conv variance infos variances b [] in
         infer_fterm cv_pb variance infos variances (mk_clos usubs (Vars.subst1 (Constr.mkSort Sorts.prop) body)) stk
       end

  (* Removed by whnf *)
  | FLOCKED -> assert false
  | FCaseT _ -> assert false
  (* | FLetIn _ -> assert false *\) *)
  | FApp _ -> assert false
  | FLIFT _ -> assert false
  | FCLOS _ -> assert false
  | FIrrelevant -> assert false (* TODO: use create_conv_infos below and use it? *)

and infer_case cv_pb variance infos variances ci u p br e =
  let ind = ci.ci_ind in
  let variances =
    let u = CClosure.usubst_instance e u in
    match inductive_variances (CClosure.info_env (fst infos)) ind u with
    | None -> infer_generic_instance_eq (Some (IndRef ind)) variances u
    | Some (mind_variances, u) ->
      infer_cumulative_instance (Names.GlobRef.IndRef ind) cv_pb (IsType, snd variance) FullyApplied mind_variances variances u
  in
  let open CClosure in
  let push_relevances (infos, tab) n = (push_relevances infos n, tab) in
  let orig_pos = get_position variances in
  debug Pp.(fun () -> str"computing variance of case with conv_pb = " ++ pr_cumul_pb cv_pb ++ str " and position " ++ Position.pr orig_pos);
  let variances =
    let (ctx, arity), _r = p in
    let ctx = Array.map (usubst_binder e) ctx in
    let infos = push_relevances infos ctx in
    let e = CClosure.usubs_liftn (Array.length ctx) e in
    infer_fterm cv_pb (IsType, Covariant) infos variances (mk_clos e arity) [] in
  let variances = set_position orig_pos variances in
  let infer_br br variances =
    let (ctx, body) = br in
    let ctx = Array.map (usubst_binder e) ctx in
    let infos = push_relevances infos ctx in
    let e = CClosure.usubs_liftn (Array.length ctx) e in
    infer_fterm cv_pb variance infos variances (mk_clos e body) []
  in
  Array.fold_right infer_br br variances

and infer_stack variance infos variances (stk:CClosure.stack) =
  match stk with
  | [] -> variances
  | z :: stk ->
    let open CClosure in
    let variance = fst variance, Invariant in
    let variances = match z with
      | Zapp v -> infer_vect Conv variance infos variances v
      | Zproj _ -> variances
      | Zfix (fx,par) ->
        let variances = infer_fterm Conv variance infos variances fx [] in
        infer_stack variance infos variances par
      | ZcaseT (ci,u,_,p,br,e) ->
        infer_case Conv variance infos variances ci u p br e
      | Zshift _ -> variances
      | Zupdate _ -> variances
      | Zprimitive (_,_,rargs,kargs) ->
        let variances = List.fold_left (fun variances c -> infer_fterm Conv variance infos variances c []) variances rargs in
        let variances = List.fold_left (fun variances (_,c) -> infer_fterm Conv variance infos variances c []) variances kargs in
        variances
    in
    infer_stack variance infos variances stk

and infer_vect cv_pb variance infos variances v =
  Array.fold_left (fun variances c -> infer_fterm cv_pb variance infos variances c []) variances v

let infer_infos ~fl env ~evars =
  let open CClosure in
  let reds = RedFlags.red_add_transparent fl TransparentState.full in
  (create_clos_infos reds ~evars env, create_tab ())

let variance_of_cv_pb = function
  | Conv -> Invariant
  | Cumul -> Covariant
  | InvCumul -> Contravariant

let infer_term (cumul_cv_pb, typing_cv_pb) env ~evars variances c =
  let variance = variance_of_cv_pb typing_cv_pb in
  let is_type = if Inf.get_position variances == Position.InTerm then IsTerm else IsType in
  let () = debug_infer_term Pp.(fun () -> pr_mode (if Inf.get_infer_mode variances then Infer else Check) ++ spc () ++
    str"at position " ++ Position.pr (Inf.get_position variances) ++
    str", cumul cv_pb = " ++ pr_cumul_pb cumul_cv_pb ++
    str", typing variance = " ++ Variance.pr variance ++ spc () ++
                                            str" term: " ++ Constr.debug_print c ++ fnl ()) in
  (* let fl = if Inf.get_infer_mode variances then (\* Infer *\) RedFlags.betaiota else RedFlags.betaiotazeta in *)
  let fl =
    if (Environ.typing_flags env).Declarations.cumulativity_zeta then RedFlags.betaiotazeta else RedFlags.betaiota
  in
  let infos = infer_infos ~fl env ~evars in
  let status = infer_fterm cumul_cv_pb (is_type, variance) infos variances (CClosure.inject c) [] in
  debug_infer_term Pp.(fun () -> Inf.pr Level.raw_pr variances ++ fnl () ++ str" -> " ++ fnl () ++ Inf.pr Level.raw_pr status);
  status

(* Assumes the context [ctx] is already in [env] *)
let infer_named_context env ~evars variances ctx =
  let infer_typ typ (i, variances) =
    let variances = Inf.set_position (Position.InBinder i) variances in
    match typ with
    | Context.Named.Declaration.LocalAssum (_, typ') ->
      (succ i,
       infer_term (Conv, Conv) env ~evars variances typ')
    | Context.Named.Declaration.LocalDef (_, _, _) ->
      (i, variances)
      (* Skip let-bound variables *)
  in
  let sec_binders, variances = Context.Named.fold_outside infer_typ ctx ~init:(0, variances) in
  sec_binders, variances

let infer_context env ~evars ?(skip_lets=true) ?(shift = 0) ?(binder_pos = fun i -> Position.InBinder i) variances ctx =
  let infer_typ typ (env, i, variances) =
    let variances = Inf.set_position (binder_pos i) variances in
    match typ with
    | Context.Rel.Declaration.LocalAssum (_, typ') ->
      (Environ.push_rel typ env, succ i,
       infer_term (Conv, Conv) env ~evars variances typ')
    | Context.Rel.Declaration.LocalDef (_, bdy, _) -> 
      if skip_lets then
        (* Skip let-bound variables *)
        (Environ.push_rel typ env, i, variances)
      else
        (* no need to infer on the type of the letin AFAICT *)
        let variances = infer_term (Conv, Conv) env ~evars variances bdy in
        (Environ.push_rel typ env, i, variances)

  in
  let env, _, variances = Context.Rel.fold_outside infer_typ ctx ~init:(env, shift, variances) in
  env, variances

let whd_decompose_lambda env ?(evars = CClosure.default_evar_handler env) c =
  let open Context.Rel.Declaration in
  let rec decrec env m c =
    let infos = infer_infos ~fl:(RedFlags.betaiotazeta) env ~evars in
    let t = CClosure.whd_val (fst infos) (snd infos) (CClosure.inject c) in
    match kind t with
      | Lambda (n,a,c0) ->
          let d = LocalAssum (n,a) in
          decrec (Environ.push_rel d env) (Context.Rel.add d m) c0
      | _ -> m,t
  in
  decrec env Context.Rel.empty c

let whd_decompose_prod env ?(evars = CClosure.default_evar_handler env) c =
  let open Context.Rel.Declaration in
  let rec decrec env m c =
    let infos = infer_infos ~fl:(RedFlags.betaiotazeta) env ~evars in
    let t = CClosure.whd_val (fst infos) (snd infos) (CClosure.inject c) in
    match kind t with
    | Prod (n,a,c0) ->
      let d = LocalAssum (n,a) in
      decrec (Environ.push_rel d env) (Context.Rel.add d m) c0
    | _ -> m,t
  in
  decrec env Context.Rel.empty c

let whd_decompose_fix env ?(evars = CClosure.default_evar_handler env) c =
  let infos = infer_infos ~fl:(RedFlags.betaiotazeta) env ~evars in
  let t = CClosure.whd_val (fst infos) (snd infos) (CClosure.inject c) in
  match kind t with
  | Fix (recinfo, defs) -> Some (recinfo, defs)
  | _ -> None

let infer_body cumul_pb env ~evars ~shift variances body =
  let ctx, body = whd_decompose_lambda ~evars env body in
  let env, variances = infer_context env ~evars ~shift variances ctx in
  let shift = Context.Rel.nhyps ctx + shift in
  match whd_decompose_fix env ~evars body with
  | Some (_, (_, tys, bodies as defs)) ->
    debug Pp.(fun () -> str"Fix decomposition in infer_body");
    let fixenv = Environ.push_rec_types defs env in
    let one_fix variances ty body =
      let fixctx, fixty = whd_decompose_prod ~evars env ty in
      let onefixenv, variances = infer_context env ~evars ~shift ~binder_pos:(fun i -> Position.InTopFixBinder i) variances fixctx in
      let variances = Inf.set_position Position.InType variances in
      let variances = infer_term (Conv, Cumul) onefixenv ~evars variances fixty in
      let fixlamctx, body = whd_decompose_lambda ~evars env body in
      let bodyenv, variances = infer_context fixenv ~evars ~shift ~binder_pos:(fun i -> Position.InTopFixBinder i) variances fixlamctx in
      let variances = Inf.set_position Position.InTerm variances in
      infer_term (Conv, Cumul) bodyenv ~evars variances body
    in
    let variances = Array.fold_left2 one_fix variances tys bodies in
    debug Pp.(fun () -> str"infer_body finished with " ++ Inf.pr Level.raw_pr variances);
    variances
  | None ->
    let variances = Inf.set_position Position.InTerm variances in
    infer_term cumul_pb env ~evars variances body

let infer_type env ~evars ?(shift = 0) variances arcn =
  let ctx, codom = whd_decompose_prod ~evars env arcn in
  let env, variances = infer_context env ~evars ~shift variances ctx in
  let variances = Inf.set_position Position.InType variances in
  infer_term (Cumul, Cumul) env ~evars variances codom

let infer_section_context env ~evars ~infer_in_type in_ctx variances =
  match in_ctx with
  | None -> 0, Inf.start ~infer_in_type variances Position.InType
  | Some ctx ->
    let shift = Context.Named.nhyps ctx in
    let variances = Inf.start ~infer_in_type (Array.map (fun (l, occ) -> (l, Option.map (VarianceOccurrence.lift shift) occ)) variances) Position.InType in
    infer_named_context env ~evars variances ctx

let infer_definition_core env ?(evars = CClosure.default_evar_handler env) ~infer_in_type ?in_ctx ~typ ?body variances =
  let shift, variances =
    infer_section_context env ~evars ~infer_in_type in_ctx variances
  in
  debug_infer_def Pp.(fun () -> str"infer_definition: " ++ Inf.pr Level.raw_pr variances ++
    str" in type: " ++ Constr.debug_print typ ++ spc () ++
    str " and body; " ++ pr_opt Constr.debug_print body);
  let variances = infer_type env ~evars ~shift variances typ in
  debug_infer_def Pp.(fun () -> str"infer_definition after type: " ++ Inf.pr Level.raw_pr variances);
  let variances = Option.cata (infer_body (Cumul, Cumul) env ~evars ~shift variances) variances body in
  debug Pp.(fun () -> str"infer_definition finished with: " ++ Inf.pr Level.raw_pr variances);
  shift, Inf.finish env variances

let push_section_universes variances sec_univs =
  match sec_univs with
  | None -> variances
  | Some sec_univs ->
    (* no variance for qualities *)
    let _, sec_univs = UVars.LevelInstance.to_array sec_univs in
    let sec_univs = Array.map (fun u -> u, None) sec_univs in
    Array.append sec_univs variances

let pop_section_universes variances sec_univs shift =
  match sec_univs with
  | None -> variances, None
  | Some sec_univs ->
    (* no variance for qualities *)
    let _nsecq, nsecu = UVars.LevelInstance.length sec_univs in
    let arr', arr = UVars.Variances.split nsecu variances in
    UVars.Variances.lift (-shift) arr, Some arr'

let infer_definition env ?(evars = CClosure.default_evar_handler env) ?(infer_in_type=false) ~in_ctx ~sec_univs ~typ ?body variances =
  try
    let variances = push_section_universes variances sec_univs in
    let shift, variances = infer_definition_core env ~evars ~infer_in_type ?in_ctx ~typ ?body variances in
    pop_section_universes variances sec_univs shift
  with BadVariance (lev, expected, actual) ->
    Type_errors.error_bad_variance env ~lev ~expected ~actual

let infer_arity_constructor is_arity env ~evars ?(shift = 0) variances arcn =
  let infer_typ typ (env, i, variances) =
    let variances = if is_arity then Inf.set_position (Position.InBinder i) variances else variances in
    match typ with
    | Context.Rel.Declaration.LocalAssum (_, typ') ->
      (Environ.push_rel typ env, succ i,
       infer_term (if is_arity then (Conv, Conv) else (Cumul,Conv)) env ~evars variances typ')
    | Context.Rel.Declaration.LocalDef _ -> assert false
  in
  let typs, codom = Reduction.whd_decompose_prod ~evars env arcn in
  let env, _, variances = Context.Rel.fold_outside infer_typ typs ~init:(env, shift, variances) in
  (* If we have Inductive foo@{i j} : ... -> Type@{i} := C : ... -> foo Type@{j}
     i is irrelevant, j is invariant. *)
  if not is_arity then
    let variances = Inf.set_position Position.InTerm variances in
    infer_term (Conv, Conv) env ~evars variances codom
  else
    let variances = Inf.set_position Position.InType variances in
    infer_term (Cumul, Cumul) env ~evars variances codom


let infer_inductive_core ~env ~env_ar_par ~evars ?in_ctx ~params ~arities ~ctors variances =
  let shift, variances =
    infer_section_context env ~evars ~infer_in_type:false in_ctx variances
  in
  let env_params, variances = infer_context env ~evars ~shift variances params in
  let variances = Inf.set_position Position.InType variances in
  let variances = List.fold_left (fun variances arity ->
      infer_arity_constructor true env_params ~evars variances arity)
      variances arities
  in
  let variances = Inf.set_position Position.InTerm variances in
  let variances = List.fold_left
      (List.fold_left (infer_arity_constructor false env_ar_par ~shift ~evars))
      variances ctors
  in
  shift, Inf.finish env_params variances

let infer_inductive ~env ~env_ar_par ?(evars = CClosure.default_evar_handler env) ~in_ctx ~sec_univs ~params ~arities ~ctors variances =
  try
    let variances = push_section_universes variances sec_univs in
    let shift, variances = infer_inductive_core ~env ~env_ar_par ~evars ~in_ctx ~params ~arities ~ctors variances in
    pop_section_universes variances sec_univs shift
  with
  | BadVariance (lev, expected, actual) ->
    Type_errors.error_bad_variance env ~lev ~expected ~actual
