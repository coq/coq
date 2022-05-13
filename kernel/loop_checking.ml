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
    val dom : table -> Point.Set.t
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

    let dom t = Point.Map.domain t.tab_bwd
  end

module PMap = Index.Map
module PSet = Index.Set

type univ_constraint = Point.t * constraint_type * Point.t

type clause_info = (int * (Index.t * int) list)
type clauses_info = clause_info list

(* Comparison on this type is pointer equality *)
type canonical_node =
  { canon: Index.t;
    value : int }

(* A Point.t is either an alias for another one, or a canonical one,
    for which we know the points that are above *)

type entry =
  | Canonical of canonical_node
  | Equiv of Index.t

type clauses = clauses_info PMap.t

type model = {
  entries : entry PMap.t;
  table : Index.table }

let empty_model = {
  entries = PMap.empty;
  table = Index.empty
}

(* Invariant: clauses map only canonical points in the model to their clauses *)
type t = {
  model : model;
  clauses : clauses;
}

let enter_equiv m u v =
  { entries = PMap.modify u (fun _ a ->
          match a with
          | Canonical _ -> Equiv v
          | _ -> assert false) m.entries;
    table = m.table }

let change_node m n =
  { m with entries =
    PMap.modify n.canon
      (fun _ a ->
        match a with
        | Canonical _ -> Canonical n
        | _ -> assert false)
      m.entries }

(* canonical representative : we follow the Equiv links *)
let rec repr m u =
  match PMap.find u m.entries with
  | Equiv v -> repr m v
  | Canonical arc -> arc

let repr_node m u =
  try repr m (Index.find u m.table)
  with Not_found ->
    CErrors.anomaly ~label:"Univ.repr"
      Pp.(str"Universe " ++ Point.pr u ++ str" undefined.")

let clauses_of idx clauses =
  try PMap.find idx clauses
  with Not_found -> []

let check_invariants ~(required_canonical:Point.t -> bool) { model; clauses } =
  let required_canonical u = required_canonical (Index.repr u model.table) in
  let n_canon = ref 0 in
  PMap.iter (fun idx e ->
    match e with
    | Canonical can ->
      assert (Index.equal idx can.canon);
      assert (Index.mem (Index.repr idx model.table) model.table);
      assert (can.value >= 0);
      let cls = clauses_of idx clauses in
      List.iter
        (fun (k, prems) ->
          assert (k >= 0);
          let check_prem (l, k) =
            assert (k >= 0);
            assert (PMap.mem l model.entries)
          in
          List.iter check_prem prems) cls;
      incr n_canon
    | Equiv idx' ->
      assert (PMap.mem idx' model.entries);
      assert (Index.mem (Index.repr idx' model.table) model.table);
      (* The clauses should not mention aliases *)
      assert (not (PMap.mem idx clauses));
      assert (not (required_canonical idx)))
    model.entries
  (* We don't necessarily have clauses for all levels assert (!n_canon <= PMap.cardinal clauses) *)

(* PMaps are purely functional hashmaps *)

let model_value m l =
  try (repr m l).value
  with Not_found -> 0

let min_premise (m : model) prem =
  match prem with
  | (l, k) :: tl ->
    List.fold_left (fun minl (l, k) -> min minl (model_value m l - k)) (model_value m l - k) tl
  | [] -> assert false

let update_value (w,m) c (k, prem) : (canonical_node * (PSet.t * model)) option =
  let k0 = min_premise m prem in
  if k0 < 0 then None
  else
    let newk = k + k0 in
     if newk <= c.value then None
     else
      let newc = { c with value = newk } in
      Some (newc, (PSet.add c.canon w, change_node m newc))

let check_model_aux (cls : clauses) wm =
  PMap.fold (fun idx cls (_, (_, m) as acc) ->
    let can = repr m idx in
    let _newm, wm' =
      List.fold_left (fun (can, (_, wm) as acc) kprem ->
        match update_value wm can kprem with
        | None -> acc
        | Some (can', wm') -> (can', (true, wm')))
      (can, acc) cls
    in wm')
  cls (false, wm)

let check_model cls w m =
  let (modified, wm') = check_model_aux cls (w, m) in
  if modified then Some wm' else None

let check_model cls w m =
  time (Pp.str "check_model") (check_model cls w) m

let premises_in w prem =
  List.for_all (fun (l, _) -> PSet.mem l w) prem

let partition_clauses (cls : clauses) w : clauses * clauses =
  PMap.fold (fun concl cls (inl, inr) ->
    let (clsW, clsnW) =
      List.fold_left (fun (inW, ninW) kprem ->
        if premises_in w (snd kprem) then (kprem :: inW, ninW)
        else (inW, kprem :: ninW)) ([], []) cls
    in
  (PMap.add concl clsW inl, PMap.add concl clsnW inr))
  cls (PMap.empty, PMap.empty)

let partition_clauses_concl (cls : clauses) (w : PSet.t) : clauses * clauses =
  PMap.fold (fun concl cls (inl, inr) ->
    if PSet.mem concl w then (PMap.add concl cls inl, inr)
    else (inl, PMap.add concl cls inr))
    cls (PMap.empty, PMap.empty)

type result = Loop | Model of PSet.t * model

let canonical_cardinal m =
  PMap.fold (fun _ e acc ->
    match e with
    | Equiv _ -> acc
    | Canonical _ -> succ acc)
    m.entries 0

let check cls m =
  let cV = canonical_cardinal m in
  let rec inner_loop w cls m =
    let (premconclW, conclW) = partition_clauses cls w in
    let cardW = PSet.cardinal w in
    let rec inner_loop_partition m =
      match loop cardW PSet.empty premconclW m with
      | Loop -> Loop
      | Model (wr, mr) ->
        (match check_model conclW wr mr with
        | Some (_wconcl, mconcl) -> inner_loop_partition mconcl
        | None -> Model (wr, mr))
      in inner_loop_partition m
  and loop cV u cls m =
    match check_model cls u m with
    | None -> Model (u, m)
    | Some (w, m') ->
      if Int.equal (PSet.cardinal w) cV
      then Loop
      else
        let conclW, conclnW = partition_clauses_concl cls w in
        (match inner_loop w conclW m' with
        | Loop -> Loop
        | Model (wc, mwc) ->
          (match check_model conclnW wc mwc with
          | None -> Model (wc, mwc)
          | Some (wcls, mcls)  -> loop cV wcls cls mcls))
  in loop cV PSet.empty cls m

let check cls m =
  debug Pp.(fun () -> str"Calling loop-checking");
  try let res = check cls m in
    debug Pp.(fun () -> str"Loop-checking terminated");
    res
  with Stack_overflow ->
    CErrors.anomaly (Pp.str "check raised a stack overflow")

let entry_value m e =
  match e with
  | Equiv idx -> (repr m idx).value
  | Canonical can -> can.value

let model_max (m : model) : int =
  PMap.fold (fun _ k acc ->
    match k with Equiv _ -> acc | Canonical can -> max can.value acc)
    m.entries 0

let pr_levelmap (m : model) : Pp.t =
  let open Pp in
  h (prlist_with_sep fnl (fun (u, v) ->
    let value = entry_value m v in
    let point = Index.repr u m.table in
    Point.pr point ++ str" -> " ++ int value) (PMap.bindings m.entries))
  (* Point.Map.pr Pp.int m  *)

let pr_model { model; _ } =
  Pp.(str "model: " ++ pr_levelmap model)

let update_model_value (m : model) l k' =
  let can = repr m l in
  let k' = max can.value k' in
  if Int.equal k' can.value then m
  else change_node m { can with value = k' }

let update_model (cls : clauses) (m : model) : model =
  PMap.fold (fun _concl prems m ->
    List.fold_left (fun m (_k, prem) ->
      List.fold_left (fun m (l, k) -> update_model_value m l k) m prem)
      m prems)
    cls m

let clauses_cardinal (cls : clauses) : int =
  PMap.fold (fun _ prems card ->
    List.length prems + card)
    cls 0

let statistics { model; clauses } =
  let open Pp in
  str" " ++ int (PMap.cardinal model.entries) ++ str" universes, maximal level in the model is " ++ int (model_max model) ++
  str", " ++ int (clauses_cardinal clauses) ++ str" clauses."

let pr_with f (l, n) =
  if Int.equal n 0 then f l
  else Pp.(f l ++ Pp.str"+" ++ int n)


let pr_index_point m idx =
  let point = Index.repr idx m.table in
  Point.pr point

let pr_pointint m = pr_with (pr_index_point m)

let pr_clauses m (cls : clauses) =
  let open Pp in
  PMap.fold (fun concl prems acc ->
    (prlist_with_sep spc (fun (k, prem) ->
      h (prlist_with_sep (fun () -> str ",") (pr_pointint m) prem ++ str " → " ++ pr_pointint m (concl, k) ++ spc ()))
       prems) ++ fnl () ++ acc) cls (Pp.mt())

let infer_clauses_extension (m : model) (clauses : clauses) =
  check_invariants ~required_canonical:(fun _ -> false) { model = m; clauses };
  let model' = update_model clauses m in
  check_invariants ~required_canonical:(fun _ -> false) { model = model'; clauses };
  debug Pp.(fun () -> str"Calling loop-checking" ++ statistics { model = model'; clauses });
  match check clauses model' with
  | Loop -> None
  | Model (_w', model) ->
    let m = { model; clauses } in
    check_invariants ~required_canonical:(fun _ -> false) m;
    Some m

let check_clause m conclv (k, prem) =
  let k0 = min_premise m prem in
  if k0 < 0 then false (* We do not allow vacuously true constraints *)
  else
    let newk = k + k0 in
     if newk <= conclv then true
     else false

let check_clauses m cls =
  PMap.for_all (fun concl cls ->
    let conclv = model_value m concl in
    List.for_all (fun cl -> check_clause m conclv cl) cls)
    cls

let empty_clauses = PMap.empty
let empty = { model = empty_model; clauses = empty_clauses }

let add_clause_aux can kprem clauses =
  PMap.update can.canon
      (fun cls ->
        match cls with
        | None -> Some [kprem]
        | Some cls -> Some (kprem :: cls))
      clauses

let add_clauses_aux can kprem clauses =
  PMap.update can.canon
    (fun cls ->
    match cls with
    | None -> Some kprem
    | Some cls -> Some (kprem @ cls))
    clauses

type pclause_info = (int * (Point.t * int) list)

let to_clause_info m (k, prems : pclause_info) : clause_info =
  let trans_prem (p, k) =
    let can = repr_node m p in
    (can.canon, k)
  in
  (k, List.map trans_prem prems)

(* Logic.10 < Logic.203
  Logic.9 <= Logic.203

  Logic.204 <= Logic.9
  Logic.204 <= Logic.10
  Logic.204 <= Logic.202 *)

let add_clause (m : model) l kprem (cls : clauses) : clauses =
  let lcan = repr_node m l in
  add_clause_aux lcan (to_clause_info m kprem) cls

(* max u_i <= v <-> ∧_i u_i <= v *)
let clauses_of_le_constraint (m : model) u v cls : clauses =
  List.fold_left (fun cls (u, k) -> add_clause m u (k, v) cls) cls u

let _check_leq (m : t) u v =
  let cls = clauses_of_le_constraint m.model u v empty_clauses in
  check_clauses m.model cls

let enforce_eq_can { model; clauses } canu canv =
  let maxval = max canu.value canv.value in
  (* u := v *)
  let can, other, model =
    if Int.equal maxval canu.value then
      canu, canv.canon, enter_equiv model canv.canon canu.canon
    else
      canv, canu.canon, enter_equiv model canu.canon canv.canon
  in
  let clauses =
    let clsother = clauses_of other clauses in
    let clauses = add_clauses_aux can clsother clauses in
    PMap.remove other clauses
  in
  { model; clauses }

let _enforce_eq_indices (m : t) u v =
  let canu = repr m.model u in
  let canv = repr m.model v in
  if canu == canv then m
  else enforce_eq_can m canu canv

let enforce_eq_points (m : t) u v =
  let canu = repr_node m.model u in
  let canv = repr_node m.model v in
  if canu == canv then m
  else enforce_eq_can m canu canv

let clauses_of_point_constraint (m : t) (cstr : univ_constraint) clauses : clauses =
  let (l, k, r) = cstr in (* l <=k r *)
  match k with
  | Lt -> add_clause m.model l (1, [(r, 0)]) clauses (* l < r <-> l + 1 <= r *)
  | Le -> add_clause m.model l (0, [(r, 0)]) clauses
  | Eq -> add_clause m.model l (0, [(r, 0)]) (add_clause m.model r (0, [(l, 0)]) clauses)

let enforce_clauses_of_point_constraint (cstr : univ_constraint) ({ model; clauses } as m) : t =
  let (l, k, r) = cstr in (* l <=k r *)
  match k with
  | Lt -> { model; clauses = add_clause m.model l (1, [(r, 0)]) clauses } (* l < r <-> l + 1 <= r *)
  | Le -> { model; clauses = add_clause m.model l (0, [(r, 0)]) clauses }
  | Eq -> enforce_eq_points m l r
    (* { model; clauses = add_clause m.model l (0, [(r, 0)]) (add_clause m.model r (0, [(l, 0)]) clauses) } *)

type 'a check_function = t -> 'a -> 'a -> bool

let check_lt (m : t) u v =
  let cls = clauses_of_point_constraint m (u, Lt, v) empty_clauses in
  check_clauses m.model cls

let check_leq (m : t) u v =
  let cls = clauses_of_point_constraint m (u, Le, v) empty_clauses in
  check_clauses m.model cls

let check_eq m u v =
  let cls = add_clause m.model u (0, [(v, 0)]) (add_clause m.model v (0, [(u, 0)]) empty_clauses) in
  check_clauses m.model cls

let pr_constraint_type k =
  let open Pp in
  match k with
  | Eq -> str " = "
  | Le -> str " ≤ "
  | Lt -> str " < "

let infer_extension x k y m =
  debug Pp.(fun () -> str"Enforcing constraint " ++ Point.pr x ++ pr_constraint_type k ++ Point.pr y);
  debug Pp.(fun () -> str "current model is: " ++ pr_levelmap m.model);
  check_invariants ~required_canonical:(fun _ -> false) m;
  debug Pp.(fun () ->
    let newcls = clauses_of_point_constraint m (x, k, y) empty_clauses in
    str"Enforcing clauses " ++ pr_clauses m.model newcls);
  let m = enforce_clauses_of_point_constraint (x, k, y) m in
  match infer_clauses_extension m.model m.clauses with
  | None ->
    let newcls = clauses_of_point_constraint m (x, k, y) empty_clauses in
    debug Pp.(fun () -> str"Enforcing clauses " ++ pr_clauses m.model newcls ++ str" resulted in a loop");
    None
  | x -> x

let enforce_leq u v m = infer_extension u Le v m
let enforce_lt u v m = infer_extension u Lt v m
let enforce_eq u v m = infer_extension u Eq v m

type lub = (Point.t * int) list

let clauses_of_constraint m (u : lub) k (v : lub) cls =
  match k with
  | Le -> clauses_of_le_constraint m u v cls
  | Lt -> clauses_of_le_constraint m (List.map (fun (l, k) -> (l, k + 1)) u) v cls
  | Eq -> clauses_of_le_constraint m u v (clauses_of_le_constraint m v u cls)

let enforce_constraint u k v (m : t) =
  let cls = clauses_of_constraint m.model u k v empty_clauses in
  infer_clauses_extension m.model cls

exception AlreadyDeclared

let add_model u { entries; table } =
  if Index.mem u table then raise AlreadyDeclared
  else
    let idx, table = Index.fresh u table in
    let can = Canonical { canon = idx; value = 0 } in
    let entries = PMap.add idx can entries in
    idx, { entries; table }

let add ?(rank:int option) u { model; clauses } =
  let _r = rank in
  debug Pp.(fun () -> str "In add, model is: " ++ pr_levelmap model);
  debug Pp.(fun () -> str"Declaring level " ++ Point.pr u);
  let _idx, model = add_model u model in
  debug Pp.(fun () -> str "In add, new model is: " ++ pr_levelmap model);
  { model; clauses }

exception Undeclared of Point.t

let check_declared { model; _ } us =
  let check l = if not (Index.mem l model.table) then raise (Undeclared l) in
  Point.Set.iter check us

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
let constraints_of_clauses m (clauses : clauses) =
  PMap.fold (fun concl prems cstrs ->
    let conclp = Index.repr concl m.table in
    List.fold_left (fun cstrs (k, prem) ->
      match prem with
      | [(v, 0)] ->
        let vp = Index.repr v m.table in
        if k = 0 then Constraints.add (conclp, Le, vp) cstrs
        else if k = 1 then Constraints.add (conclp, Lt, vp) cstrs
        else assert false
      | _ -> assert false) cstrs prems)
    clauses Constraints.empty

type 'a constraint_fold = Point.t * constraint_type * Point.t -> 'a -> 'a

let constraints_of { model; clauses } fold acc =
  let cstrs = constraints_of_clauses model clauses in
  Constraints.fold fold cstrs acc, []

let constraints_for ~(kept:Point.Set.t) { model; clauses } (fold : 'a constraint_fold) (accu : 'a) =
  (* rmap: partial map from canonical points to kept points *)
  let add_cst u knd v (cst : 'a) =
    fold (Index.repr u model.table, knd, Index.repr v model.table) cst
  in
  let kept = Point.Set.fold (fun u accu -> PSet.add (Index.find u model.table) accu) kept PSet.empty in
  let rmap, csts = PSet.fold (fun u (rmap,csts) ->
      let arcu = repr model u in
      if PSet.mem arcu.canon kept then
        let csts = if Index.equal u arcu.canon then csts
          else add_cst u Eq arcu.canon csts
        in
        PMap.add arcu.canon arcu.canon rmap, csts
      else
        match PMap.find arcu.canon rmap with
        | v -> rmap, add_cst u Eq v csts
        | exception Not_found -> PMap.add arcu.canon u rmap, csts)
      kept (PMap.empty, accu)
  in
  let rec add_from u csts todo = match todo with
    | [] -> csts
    | (prems,k)::todo ->
      let v = match prems with [v, 0] -> v | _ -> assert false in
      (* constraints cannot have premisses of other shapes *)
      let v = repr model v in
      (match PMap.find v.canon rmap with
      | v ->
        let d = if k > 0 then Lt else Le in
        let csts = add_cst u d v csts in
        add_from u csts todo
      | exception Not_found ->
        let cls = clauses_of v.canon clauses in
        (* v is not equal to any kept point *)
        let todo = List.fold_left (fun todo (k', prems') -> (prems', k + k') :: todo)
            todo cls
        in
        add_from u csts todo)
  in
  PSet.fold (fun u csts ->
      let arc = repr model u in
      let cls = clauses_of arc.canon clauses in
      List.fold_left (fun csts (k, prems) -> add_from u csts [prems,k]) csts cls)
    kept csts


(*
  let cstrs = constraints_of_clauses model clauses in
  let cstrs = Constraints.filter (fun (l, _, r) -> Point.Set.mem l kept || Point.Set.mem r kept) cstrs in
  Constraints.fold fold cstrs acc *)

let domain { model; _ } = Index.dom model.table

let choose p { model; _} p' =
  let canp' = repr_node model p' in
  let pointp' = Index.repr canp'.canon model.table in
  if p pointp' then Some pointp'
  else PMap.fold (fun idx e acc ->
      match acc with
      | Some _ -> acc
      | None ->
        match e with
        | Equiv idx' ->
          let canp'' = repr model idx' in
          if canp' == canp'' then
            let pointp' = Index.repr idx model.table in
            if p pointp' then Some pointp'
            else acc
          else acc
        | Canonical _ -> acc)
      model.entries None

type node =
  | Alias of Point.t
  | Node of bool Point.Map.t (** Nodes v s.t. u < v (true) or u <= v (false) *)

type repr = node Point.Map.t
let repr { clauses; model } =
  PMap.fold (fun idx e acc ->
    let conclp = Index.repr idx model.table in
    let node = match e with
    | Equiv idx -> Alias (Index.repr idx model.table)
    | Canonical can ->
      let prems = PMap.find can.canon clauses in
      let map =
        List.fold_left (fun map (k, prem) ->
          match prem with
          | [(v, 0)] ->
            let canv = repr model v in
            let vp = Index.repr canv.canon model.table in
            if k = 0 then Point.Map.add vp false map
            else if k = 1 then Point.Map.add vp true map
            else assert false
          | _ -> assert false) Point.Map.empty prems
      in
      Node map
    in
    Point.Map.add conclp node acc)
  model.entries Point.Map.empty

let pmap_to_point_map table pmap =
  PMap.fold (fun idx v acc ->
    let p = Index.repr idx table in
    Point.Map.add p v acc)
    pmap Point.Map.empty

let valuation_of_model (m : model) =
  let max = model_max m in
  let valm = PMap.map (fun e -> max - entry_value m e) m.entries in
  pmap_to_point_map m.table valm

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
