(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
open Sorts

module G = AcyclicGraph.Make(struct
    type t = Quality.t
    module Set = Quality.Set
    module Map = Quality.Map

    let equal = Quality.equal
    let compare = Quality.compare

    let raw_pr = Quality.raw_pr

    let anomaly_label = "Quality.repr"
    let anomaly_err q = Pp.(str "Quality " ++ Quality.raw_pr q ++ str " undefined.")
  end)

type t = G.t

type path_explanation = G.explanation Lazy.t

type explanation =
  | Path of path_explanation
  | Other of Pp.t

type quality_inconsistency =
  ((QVar.t -> Pp.t) option) * (ElimConstraint.kind * Quality.t * Quality.t * explanation option)

exception QualityInconsistency of quality_inconsistency

(* If s can eliminate to s', we want an edge between s and s'.
   In the acyclic graph, it means setting s to be lower or equal than s'.
   This function ensures a uniform behaviour between [check] and [enforce]. *)
let to_graph_cstr k =
  let open ElimConstraint in
  match k with
    | ElimTo -> AcyclicGraph.Le
    | Equal -> AcyclicGraph.Eq

let check_func k =
  let open AcyclicGraph in
  match to_graph_cstr k with
  | Le -> G.check_leq
  | Eq -> G.check_eq
  | Lt -> assert false

let enforce_func k =
  let open AcyclicGraph in
  match to_graph_cstr k with
  | Le -> G.enforce_leq
  | Eq -> G.enforce_eq
  | Lt -> assert false

let enforce_constraint (q1,k,q2) g =
  match enforce_func k q1 q2 g with
  | None ->
     let e = lazy (G.get_explanation (q1,to_graph_cstr k,q2) g) in
     raise @@ QualityInconsistency (None, (k, q1, q2, Some (Path e)))
  | Some g -> g

let merge_constraints csts g = ElimConstraints.fold enforce_constraint csts g

let check_constraint g (q1, k, q2) = check_func k g q1 q2

let check_constraints csts g = ElimConstraints.for_all (check_constraint g) csts

exception AlreadyDeclared = G.AlreadyDeclared
let add_quality q g =
  let g = G.add q g in
  enforce_constraint (Quality.qtype, ElimConstraint.ElimTo, q) g

let enforce_eliminates_to s1 s2 g =
  enforce_constraint (s1, ElimConstraint.ElimTo, s2) g

let enforce_eq s1 s2 g =
  enforce_constraint (s1, ElimConstraint.Equal, s2) g

(* let add_qvar q g = add_quality g (QVar q) *)

let initial_graph =
  let g = G.empty in
  let g = List.fold_left (fun g q -> G.add q g) g Quality.all_constants in
  (* Enforces the constant constraints defined in the table of
     [Constants.eliminates_to] without reflexivity (should be consistent,
     otherwise the [Option.get] will fail). *)
  List.fold_left
    (fun g q ->
      List.fold_left
        (fun g q' -> if Quality.eliminates_to q q'
                  then Option.get @@ G.enforce_lt q q' g
                  else g) g
        (List.filter (fun q' -> not @@ Quality.equal q q') Quality.all_constants))
    g Quality.all_constants

let eliminates_to g q q' =
  (* FIXME: temporary condition until the [QVar]s are added to the graph *)
  if Quality.is_qtype q || Quality.equal q q'
  then true
  else
    (* FIXME: temporary try-with until the [QVar]s are added to the graph *)
    try check_func ElimConstraint.ElimTo g q q'
    with _ -> false

let sort_eliminates_to g s1 s2 =
  eliminates_to g (quality s1) (quality s2)

let check_eq = G.check_eq

let check_eq_sort g s s' = check_eq g (quality s) (quality s')

let eliminates_to_prop g q = eliminates_to g q Quality.qprop

let domain = G.domain

let qvar_domain g =
  Quality.Set.fold
    (fun q acc -> match q with Quality.QVar q -> QVar.Set.add q acc | _ -> acc)
    (domain g) QVar.Set.empty

let is_empty g = Quality.Set.is_empty (domain g)

let explain_quality_inconsistency defprv (prv, (k, q1, q2, r)) =
  let open Pp in
  let prv = match prv with None -> defprv | Some prv -> prv in
  let pr_cst = function
    | AcyclicGraph.Eq -> str"="
    | AcyclicGraph.Le -> str"->"
    | AcyclicGraph.Lt -> str"->" (* Yes, it's the same as above. *)
  in
  let reason = match r with
    | None -> mt()
    | Some (Other p) -> p
    | Some (Path p) ->
      let pstart, p = Lazy.force p in
      if p = [] then mt ()
      else
        let qualities = pstart :: List.map snd p in
        let constants = List.filter Quality.is_qconst qualities in
        str "because it would identify" ++
          prlist (fun q -> spc() ++ str"and" ++ spc() ++ Quality.pr prv q) constants ++
          spc() ++ str"which is inconsistent." ++ spc() ++
          str"This is introduced by the constraints" ++ spc() ++ Quality.pr prv pstart ++
          prlist (fun (r,v) -> spc() ++ pr_cst r ++ str" " ++ Quality.pr prv v) p
  in
  str "Cannot enforce" ++ spc() ++ Quality.pr prv q1 ++ spc() ++
    ElimConstraint.pr_kind k ++ spc() ++ Quality.pr prv q2 ++ spc() ++ reason

module Internal = struct
  let add_template_qvars =
    QVar.Set.fold @@
      fun v -> enforce_eliminates_to (Quality.QVar v) Quality.qprop
end
