type constraint_type = Lt | Le | Eq

let _debug_loop_checking_flag, debug = CDebug.create_full ~name:"loop-checking" ()
let debug_loop_checking_timing_flag, debug_timing = CDebug.create_full ~name:"loop-checking-timing" ()

module type Point = sig
  type t

  module Set : CSig.SetS with type elt = t
  module Map : CMap.ExtS with type key = t and module Set := Set

  val equal : t -> t -> bool
  val compare : t -> t -> int

  val pr : t -> Pp.t
end

let time prefix f x =
  if CDebug.(get_flag debug_loop_checking_timing_flag) then
    let start = Unix.gettimeofday () in
    let res = f x in
    let stop = Unix.gettimeofday () in
    let () = debug_timing Pp.(fun () -> prefix ++ str " executed in: " ++ Pp.real (stop -. start) ++ str "s") in
    res
  else f x

module Make (Point : Point) = struct

  module Index :
  sig
    type t
    val equal : t -> t -> bool
    module Set : CSig.SetS with type elt = t
    module Map : CMap.ExtS with type key = t and module Set := Set
    type table
    val empty : table
    val fresh : Point.t -> table -> t * table
    val mem : Point.t -> table -> bool
    val find : Point.t -> table -> t
    val repr : t -> table -> Point.t
  end =
  struct
    type t = int
    let equal = Int.equal
    module Set = Int.Set
    module Map = Int.Map

    type table = {
      tab_len : int;
      tab_fwd : Point.t Int.Map.t;
      tab_bwd : int Point.Map.t
    }

    let empty = {
      tab_len = 0;
      tab_fwd = Int.Map.empty;
      tab_bwd = Point.Map.empty;
    }
    let mem x t = Point.Map.mem x t.tab_bwd
    let find x t = Point.Map.find x t.tab_bwd
    let repr n t = Int.Map.find n t.tab_fwd

    let fresh x t =
      let () = assert (not @@ mem x t) in
      let n = t.tab_len in
      n, {
        tab_len = n + 1;
        tab_fwd = Int.Map.add n x t.tab_fwd;
        tab_bwd = Point.Map.add x n t.tab_bwd;
      }
  end

module PMap = Index.Map
module PSet = Index.Set

type univ_constraint = Point.t * constraint_type * Point.t

type clauses = (int * (Index.t * int) list) list Point.Map.t

(* Comparison on this type is pointer equality *)
type canonical_node =
  { canon: Index.t;

  }

(* A Point.t is either an alias for another one, or a canonical one,
    for which we know the points that are above *)

type entry =
  | Canonical of canonical_node
  | Equiv of Index.t

let add_clause l kprem cls =
  PMap.update l (fun kprems ->
    match kprems with
    | None -> Some [kprem]
    | Some l -> Some (kprem :: l)) cls

(* let update_model *)
(* Point.Maps are purely functional hashmaps *)
type model = int PMap.t

let model_value m l =
  try PMap.find l m
  with Not_found -> 0

let min_premise (m : model) prem =
  match prem with
  | (l, k) :: tl ->
    List.fold_left (fun minl (l, k) -> min minl (model_value m l - k)) (model_value m l - k) tl
  | [] -> assert false

let update_value (w,m) concl conclv (k, prem) : (int * (Point.Set.t * model)) option =
  let k0 = min_premise m prem in
  if k0 < 0 then None
  else
    let newk = k + k0 in
     if newk <= conclv then None
     else Some (newk, (Point.Set.add concl w, Point.Map.add concl newk m))

let check_model_aux cls wm =
  Point.Map.fold (fun concl cls (_, (_, m) as acc) ->
      snd (List.fold_left (fun (conclv, (_, wm) as acc) kprem ->
          match update_value wm concl conclv kprem with
          | None -> acc
          | Some (newv, wm') -> (newv, (true, wm')))
        (model_value m concl, acc) cls))
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
          | Some (wcls, mcls)  -> loop v cV wcls cls mcls))
  in loop v cV Point.Set.empty cls m

let check v cls m =
  debug Pp.(fun () -> str"Calling loop-checking");
  try let res = check v cls m in
    debug Pp.(fun () -> str"Loop-checking terminated");
    res
  with Stack_overflow ->
    CErrors.anomaly (Pp.str "check raised a stack overflow")

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

let max_level m =
  Point.Map.fold (fun _ v m -> max v m) m 0

let clauses_cardinal m =
  Point.Map.fold (fun _ prems card ->
    List.length prems + card)
    m 0


type t = {
  model : model;
  points : PSet.t;
  clauses : clauses;
}

let statistics { points; model; clauses } =
  let open Pp in
  int (PSet.cardinal points) ++ str"universes, maximal level in the model is " ++ int (max_level model) ++
  str", " ++ int (clauses_cardinal clauses) ++ str" clauses."

let pr_with f (l, n) =
  if Int.equal n 0 then f l
  else Pp.(f l ++ Pp.str"+" ++ int n)

let pr_pointint = pr_with Point.pr

let pr_clauses cls =
  let open Pp in
  Point.Map.fold (fun concl prems acc ->
    (prlist_with_sep spc (fun (k, prem) ->
      h (prlist_with_sep (fun () -> str ",") pr_pointint prem ++ str " → " ++ pr_pointint (concl, k) ++ spc ()))
       prems) ++ fnl () ++ acc) cls (Pp.mt())

let infer_clauses_extension (m : t) (clauses : clauses) =
  let points = m.points in
  let model' = update_model clauses m.model in
  debug Pp.(fun () -> str"Calling loop-checking" ++ statistics { m with model = model' });
  match check points clauses model' with
  | Loop -> None
  | Model (_w', model) -> Some { model; clauses; points }

let check_clause m conclv (k, prem) =
  let k0 = min_premise m prem in
  if k0 < 0 then false (* We do not allow vacuously true constraints *)
  else
    let newk = k + k0 in
     if newk <= conclv then true
     else false

let check_clauses m cls =
  Point.Map.for_all (fun concl cls ->
    let conclv = model_value m concl in
    List.for_all (fun cl -> check_clause m conclv cl) cls)
    cls

(* max u_i <= v <-> ∧_i u_i <= v *)
let clauses_of_le_constraint u v cls =
  List.fold_left (fun cls (u, k) -> add_clause u (k, v) cls) cls u

let empty_clauses = Point.Map.empty
let empty = { model = Point.Map.empty; points = Point.Set.empty; clauses = empty_clauses }

let _check_leq (m : t) u v =
  let cls = clauses_of_le_constraint u v empty_clauses in
  check_clauses m.model cls

let clauses_of_point_constraint (cstr : univ_constraint) (cls : clauses) : clauses =
  let (l, k, r) = cstr in (* l <=k r *)
  match k with
  | Lt -> add_clause l (1, [(r, 0)]) cls (* l < r <-> l + 1 <= r *)
  | Le -> add_clause l (0, [(r, 0)]) cls
  | Eq -> add_clause l (0, [(r, 0)]) (add_clause r (0, [(l, 0)]) cls)

type 'a check_function = t -> 'a -> 'a -> bool

let check_lt (m : t) u v =
  let cls = clauses_of_point_constraint (u, Lt, v) empty_clauses in
  check_clauses m.model cls

let check_leq (m : t) u v =
  let cls = clauses_of_point_constraint (u, Le, v) empty_clauses in
  check_clauses m.model cls

let check_eq m u v =
  let cls = add_clause u (0, [(v, 0)]) (add_clause v (0, [(u, 0)]) empty_clauses) in
  check_clauses m.model cls

let infer_extension u k v m =
  let cls = clauses_of_point_constraint (u, k, v) m.clauses in
  match infer_clauses_extension m cls with
  | None ->
    let newcls = clauses_of_point_constraint (u, k, v) empty_clauses in
    debug Pp.(fun () -> str"Enforcing clauses " ++ pr_clauses newcls ++ str" resulted in a loop");
    None
  | x -> x

let enforce_leq u v m = infer_extension u Le v m
let enforce_lt u v m = infer_extension u Lt v m
let enforce_eq u v m = infer_extension u Eq v m

type lub = (Point.t * int) list

let clauses_of_constraint (u : lub) k (v : lub) cls =
  match k with
  | Le -> clauses_of_le_constraint u v cls
  | Lt -> clauses_of_le_constraint (List.map (fun (l, k) -> (l, k + 1)) u) v cls
  | Eq -> clauses_of_le_constraint u v (clauses_of_le_constraint v u cls)

let enforce_constraint u k v (m : t) =
  let cls = clauses_of_constraint u k v empty_clauses in
  infer_clauses_extension m cls

exception AlreadyDeclared

let check_invariants ~(required_canonical:Point.t -> bool) _ =
  let _r = required_canonical in
  ()

let add ?(rank:int option) u { model; points; clauses } =
  let _r = rank in
  if Point.Set.mem u points then raise AlreadyDeclared
  else
    { points = Point.Set.add u points;
      model = Point.Map.add u 0 model;
      clauses }

exception Undeclared of Point.t

let check_declared { points; _ } ls =
  Point.Set.iter (fun l ->
    if Point.Set.mem l points then ()
    else raise (Undeclared l))
    ls

let get_explanation (cstr : Point.t * constraint_type * Point.t) _ : (constraint_type * Point.t) list =
  let _cstr = cstr in
  (* TODO *)
  []


let constraint_type_ord c1 c2 = match c1, c2 with
  | Lt, Lt -> 0
  | Lt, _ -> -1
  | Le, Lt -> 1
  | Le, Le -> 0
  | Le, Eq -> -1
  | Eq, Eq -> 0
  | Eq, _ -> 1

module UConstraintOrd =
struct
  type t = univ_constraint
  let compare (u,c,v) (u',c',v') =
    let i = constraint_type_ord c c' in
    if not (Int.equal i 0) then i
    else
      let i' = Point.compare u u' in
      if not (Int.equal i' 0) then i'
      else Point.compare v v'
end

module Constraints =
struct
  module S = Set.Make(UConstraintOrd)
  include S
end

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

type 'a constraint_fold = Point.t * constraint_type * Point.t -> 'a -> 'a

let constraints_of { clauses; _ } fold acc =
  let cstrs = constraints_of_clauses clauses in
  Constraints.fold fold cstrs acc, []

let constraints_for ~(kept:Point.Set.t) { clauses; _ } fold acc =
  let cstrs = constraints_of_clauses clauses in
  let cstrs = Constraints.filter (fun (l, _, r) -> Point.Set.mem l kept || Point.Set.mem r kept) cstrs in
  Constraints.fold fold cstrs acc

let domain { points; _ } = points

let choose p _ p' =
  if p p' then Some p'
  else None
    (* Point.Set.fold (fun p' acc ->
      match acc with
      | Some _ -> acc
      | None -> if p p' then Some p' else acc)
      points None *)

type node =
  | Alias of Point.t
  | Node of bool Point.Map.t (** Nodes v s.t. u < v (true) or u <= v (false) *)

type repr = node Point.Map.t
let repr { clauses; _ } =
  Point.Map.fold (fun concl prems acc ->
    let map =
      List.fold_left (fun map (k, prem) ->
        match prem with
        | [(v, 0)] ->
          if k = 0 then Point.Map.add v false map
          else if k = 1 then Point.Map.add v true map
          else assert false
        | _ -> assert false) Point.Map.empty prems
    in
    let repr = Node map in
    Point.Map.add concl repr acc)
    clauses Point.Map.empty


let pr_model { model; _ } =
  Pp.(str "model: " ++ pr_levelmap model)

let valuation { model; _ } = valuation_of_model model

end


(*
let clauses_of_constraints cstr =
  Univ.Constraints.fold clauses_of_point_constraint cstr Point.Map.empty


let initial_universes =
  { model = Point.Map.add Level.set 0 Point.Map.empty;
    clauses = empty_clauses;
    points = Point.Set.singleton Level.set }

let infer_cstrs_extension m (cstrs : Constraints.t) =
  let cls = clauses_of_constraints cstrs in
  infer_clauses_extension m cls

let check_constraints ((points, cstrs) : Univ.ContextSet.t) : unit =
  let clauses = time (Pp.str "Building clauses out of constraints") clauses_of_constraints cstrs in
  let m = update_model clauses Point.Map.empty in
  match time (Pp.str "Checking for a model") (check points clauses) m with
  | Loop -> Feedback.msg_info Pp.(str "found a loop")
  | Model (_w, _m) -> Feedback.msg_info Pp.(str "found a model")

    (* match check_model clauses Point.Set.empty m with
    | None -> Feedback.msg_info Pp.(str"Model is " ++ pr_levelmap m)
    | Some _ -> Feedback.msg_info Pp.(str"Not actually a model!") *)
*)
