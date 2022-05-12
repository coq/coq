type constraint_type = Lt | Le | Eq

module type Point = sig
  type t

  module Set : CSig.SetS with type elt = t
  module Map : CMap.ExtS with type key = t and module Set := Set

  val equal : t -> t -> bool
  val compare : t -> t -> int

  val pr : t -> Pp.t
end

(* This allows to load multiple plugins sharing the same option at the same time
  while have option settings apply to both *)
let timing_opt () = true
  (* let open Goptions in
  let key = ["Universes"; "Timing"] in
  let tables = get_tables () in
  try
    let _ = OptionMap.find key tables in
    fun () ->
      let tables = get_tables () in
      let opt = OptionMap.find key tables in
      match opt.opt_value with
      | BoolValue b -> b
      | _ -> assert false
  with Not_found ->
    declare_bool_option_and_ref ~depr:false ~key ~value:false *)

let time prefix f x =
  if timing_opt () then
    let start = Unix.gettimeofday () in
    let res = f x in
    let stop = Unix.gettimeofday () in
    let () = Printf.printf "%s\n" (Pp.string_of_ppcmds Pp.(prefix ++ str " executed in: " ++ Pp.real (stop -. start) ++ str "s")) in
    res
  else f x

module Make (Point : Point) = struct

type univ_constraint = Point.t * constraint_type * Point.t

type clauses = (int * (Point.t * int) list) list Point.Map.t

let add_clause l kprem cls =
  Point.Map.update l (fun kprems ->
    match kprems with
    | None -> Some [kprem]
    | Some l -> Some (kprem :: l)) cls

(* let update_model *)
(* Point.Maps are purely functional hashmaps *)
type model = int Point.Map.t

let level_value m l =
  try Point.Map.find l m
  with Not_found -> 0

let min_premise (m : model) prem =
  match prem with
  | (l, k) :: tl ->
    List.fold_left (fun minl (l, k) -> min minl (level_value m l - k)) (level_value m l - k) tl
  | [] -> assert false

let update_value (w,m) concl conclv (k, prem) : (int * (Point.Set.t * model)) option =
  let k0 = min_premise m prem in
  if k0 < 0 then None
  else
    let newk = k + k0 in
     if newk <= conclv then None
     else Some (newk, (Point.Set.add concl w, Point.Map.add concl newk m))

let rec check_model_aux cls wm =
  Point.Map.fold (fun concl cls (_, (_, m) as acc) ->
      snd (List.fold_left (fun (conclv, (_, wm) as acc) kprem ->
          match update_value wm concl conclv kprem with
          | None -> acc
          | Some (newv, wm') -> (newv, (true, wm')))
        (level_value m concl, acc) cls))
    cls (false, wm)

let check_model cls w m =
  let (modified, wm') = check_model_aux cls (w, m) in
  if modified then Some wm' else None

let check_model cls w m =
  time (Pp.str "check_model") (check_model cls w) m

let premises_in w prem =
  List.for_all (fun (l, _) -> Point.Set.mem l w) prem

let partition_clauses (cls : clauses) w =
  Point.Map.fold (fun concl cls (inl, inr) ->
    let (clsW, clsnW) =
      List.fold_left (fun (inW, ninW) kprem ->
        if premises_in w (snd kprem) then (kprem :: inW, ninW)
        else (inW, kprem :: ninW)) ([], []) cls
    in
    (Point.Map.add concl clsW inl, Point.Map.add concl clsnW inr))
    cls (Point.Map.empty, Point.Map.empty)

let partition_clauses_concl (cls : clauses) (w : Point.Set.t) =
  Point.Map.fold (fun concl cls (inl, inr) ->
    if Point.Set.mem concl w then (Point.Map.add concl cls inl, inr)
    else (inl, Point.Map.add concl cls inr))
    cls (Point.Map.empty, Point.Map.empty)

type result = Loop | Model of Point.Set.t * model

let check v cls m =
  let cV = Point.Set.cardinal v in
  let rec inner_loop w cls m =
    let (premconclW, conclW) = partition_clauses cls w in
    let cardW = Point.Set.cardinal w in
    let rec inner_loop_partition m =
      match loop w cardW Point.Set.empty premconclW m with
      | Loop -> Loop
      | Model (wr, mr) ->
        (match check_model conclW wr mr with
        | Some (_wconcl, mconcl) -> inner_loop_partition mconcl
        | None -> Model (wr, mr))
      in inner_loop_partition m
  and loop v cV u cls m =
    match check_model cls u m with
    | None -> Model (u, m)
    | Some (w, m') ->
      if Int.equal (Point.Set.cardinal w) cV
      then Loop
      else
        let conclW, conclnW = partition_clauses_concl cls w in
        (match inner_loop w conclW m' with
        | Loop -> Loop
        | Model (wc, mwc) ->
          (match check_model conclnW wc mwc with
          | None -> Model (wc, mwc)
          | Some (wcls, mcls)  ->
             loop v cV wcls cls mcls))
  in loop v cV Point.Set.empty cls m

let valuation_of_model m =
  let max = Point.Map.fold (fun _ k acc -> max k acc) m 0 in
  Point.Map.map (fun v -> max - v) m

let pr_levelmap (m : model) : Pp.t =
  let open Pp in
  h (prlist_with_sep fnl (fun (u, v) ->
    Point.pr u ++ str" -> " ++ int v) (Point.Map.bindings m))
  (* Point.Map.pr Pp.int m  *)

let update_model_value m l k' =
  Point.Map.update l (fun k ->
    match k with
    | None -> Some k'
    | Some k -> Some (max k k'))
    m

let update_model cls m =
  Point.Map.fold (fun _concl prems m ->
    List.fold_left (fun m (_k, prem) ->
      List.fold_left (fun m (l, k) -> update_model_value m l k) m prem)
      m prems)
    cls m

type t = {
  model : model;
  univs : Point.Set.t;
  clauses : clauses;
}
let infer_clauses_extension (m : t) (clauses : clauses) =
  let univs = m.univs in
  let model' = update_model clauses m.model in
  match check univs clauses model' with
  | Loop -> None
  | Model (_w', model) -> Some { model; clauses; univs }

let check_clause m conclv (k, prem) =
  let k0 = min_premise m prem in
  if k0 < 0 then false (* We do not allow vacuously true constraints *)
  else
    let newk = k + k0 in
     if newk <= conclv then true
     else false

let check_clauses m cls =
  Point.Map.for_all (fun concl cls ->
    let conclv = level_value m concl in
    List.for_all (fun cl -> check_clause m conclv cl) cls)
    cls

let clauses_of_le_constraint (u v : (Point.t * int) list) cls =
  (* max u_i <= v <-> ∧_i u_i <= v *)
  List.fold_left (fun cls (u, k) -> add_clause u (k, v) cls) cls u

let clauses_of_constraint u k v cls =
  match k with
  | Le -> clauses_of_le_constraint u v cls
  | Lt -> clauses_of_le_constraint (Universe.super u) v cls
  | Eq -> clauses_of_le_constraint u v (clauses_of_le_constraint v u cls)

let empty_clauses = Point.Map.empty

let check_leq (m : t) u v =
  let cls = clauses_of_le_constraint u v empty_clauses in
  check_clauses m.model cls

let check_eq (m : t) u v =
  let cls = clauses_of_constraint u Eq v empty_clauses in
  check_clauses m.model cls

let check_eq_level m u v =
  let cls = add_clause u (0, [(v, 0)]) (add_clause v (0, [(u, 0)]) empty_clauses) in
  check_clauses m.model cls

let check_lt_level (m : t) u v =
  let cls = clauses_of_univ_constraint (u, Lt, v) empty_clauses in
  check_clauses m.model cls

let check_le_level (m : t) u v =
  let cls = clauses_of_univ_constraint (u, Le, v) empty_clauses in
  check_clauses m.model cls
let initial_universes =
  { model = Point.Map.add Level.set 0 Point.Map.empty;
    clauses = empty_clauses;
    univs = Point.Set.singleton Level.set }

let enforce_leq u v m =
  let cls = clauses_of_univ_constraint (u, Le, v) m.clauses in
  infer_clauses_extension m cls

let enforce_lt u v m =
  let cls = clauses_of_univ_constraint (u, Lt, v) m.clauses in
  infer_clauses_extension m cls

let enforce_eq u v m =
  let cls = clauses_of_univ_constraint (u, Eq, v) m.clauses in
  infer_clauses_extension m cls

let add u { model; univs; clauses } =
  { univs = Point.Set.add u univs;
    model = Point.Map.add u 0 model;
    clauses }

let check_declared { univs; _ } l = Point.Set.mem l univs

(* This only works for level (+1) <= level constraints *)
let constraints_of_clauses (clauses : clauses) =
  Point.Map.fold (fun concl prems cstrs ->
    List.fold_left (fun cstrs (k, prem) ->
      match prem with
      | [(v, 0)] ->
        if k = 0 then Constraints.add (concl, Le, v) cstrs
        else if k = 1 then Constraints.add (concl, Lt, v) cstrs
        else assert false
      | _ -> assert false) cstrs prems)
    clauses Constraints.empty

let constraints_of { clauses; _ } fold acc =
  let cstrs = constraints_of_clauses clauses in
  Constraints.fold fold cstrs acc, []

let constraints_for ~kept:Point.Set.t { clauses; _ } fold acc =
  let cstrs = constraints_of_clauses clauses in
  let cstrs = Constraints.filter (fun (l, d, r) -> Point.Set.mem )

let infer_cstrs_extension m (cstrs : Constraints.t) =
  let cls = clauses_of_constraints cstrs in
  infer_clauses_extension m cls


let clauses_of_univ_constraint (cstr : univ_constraint) (cls : clauses) : clauses =
  let (l, k, r) = cstr in (* l <=k r *)
  match k with
  | Lt -> add_clause l (1, [(r, 0)]) cls (* l < r <-> l + 1 <= r *)
  | Le -> add_clause l (0, [(r, 0)]) cls
  | Eq -> add_clause l (0, [(r, 0)]) (add_clause r (0, [(l, 0)]) cls)

let clauses_of_constraints cstr =
  Univ.Constraints.fold clauses_of_univ_constraint cstr Point.Map.empty

let check_constraints ((univs, cstrs) : Univ.ContextSet.t) : unit =
  let clauses = time (Pp.str "Building clauses out of constraints") clauses_of_constraints cstrs in
  let m = update_model clauses Point.Map.empty in
  match time (Pp.str "Checking for a model") (check univs clauses) m with
  | Loop -> Feedback.msg_info Pp.(str "found a loop")
  | Model (_w, _m) -> Feedback.msg_info Pp.(str "found a model")

    (* match check_model clauses Point.Set.empty m with
    | None -> Feedback.msg_info Pp.(str"Model is " ++ pr_levelmap m)
    | Some _ -> Feedback.msg_info Pp.(str"Not actually a model!") *)
