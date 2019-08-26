open Hashset.Combine
open Util

(** Helpers *)
let (<<) f g x = f @@ g x

(** Collection of stage variables *)

module SVars =
struct
  include Int.Set

  type var = elt

  let union_list = List.fold_left union empty

  let pr vars =
    let open Pp in
    let pr_var v = str "s" ++ int v in
    seq [str "{"; pr_enum pr_var (elements vars); str "}"]
end

(** Stages, for sized annotations *)

module Stage =
struct
  type t = Infty | StageVar of SVars.var * int

  let infty = -1 (* For constraint representation only!!! *)

  let mk var size = StageVar (var, size)

  let var_equal = Int.equal

  let compare s1 s2 =
    match s1, s2 with
    | Infty, Infty -> 0
    | Infty, _     -> 1
    | _, Infty     -> -1
    | StageVar (var1, sz1), StageVar (var2, sz2) ->
      let nc = Int.compare var1 var2 in
      if not (Int.equal nc 0) then nc
      else Int.compare sz1 sz2

  let pr s =
    let open Pp in
    match s with
    | Infty -> str "∞"
    | StageVar (s, n) ->
      let pp = str "s" ++ int s in
      if Int.equal n 0 then pp else
      seq [pp; str "+"; int n]
end

(** Annotations, attached to (co)inductive types *)

module Annot =
struct
  open Stage

  type t =
    | Empty (* Bare types with no annotations, input to inference *)
    | Star (* Marks the positions of the (co)recursive types in (co)fixpoints *)
    | Glob (* Marks the positions of the (co)recursive types in global definitions *)
    | Stage (* Sized types *) of Stage.t

  let infty = Stage Infty

  let mk var size = Stage (Stage.mk var size)

  let hat a =
    match a with
    | Stage (StageVar (var, sz)) -> Stage (StageVar (var, succ sz))
    | _ -> a

  let compare a1 a2 =
    match a1, a2 with
    | Empty, Empty -> 0
    | Empty, _ -> -1 | _, Empty -> 1
    | Star, Star   -> 0
    | Star, _  -> -1 | _, Star  -> 1
    | Glob, Glob   -> 0
    | Glob, _  -> -1 | _, Glob  -> 1
    | Stage s1, Stage s2 -> Stage.compare s1 s2

  let pr a =
    let open Pp in
    match a with
    | Empty -> mt ()
    | Star  -> str "*"
    | Glob  -> str "ⁱ"
    | Stage s -> Stage.pr s

  let show a = Pp.string_of_ppcmds (pr a)

  let hash a =
    match a with
    | Empty -> combine 1 (show a |> String.hash)
    | Star  -> combine 2 (show a |> String.hash)
    | Glob  -> combine 3 (show a |> String.hash)
    | Stage Infty -> combine 4 (show a |> String.hash)
    | Stage (StageVar (n, i)) -> combine3 5 (Int.hash n) (Int.hash i)
end

(** Stage state, keeping track of used stage variables *)

module State =
struct
  open SVars
  open Stage
  open Annot

  type t = {
    next: var;
    (* next stage variable to be used *)
    vars: SVars.t;
    (* all used stage variables *)
    pos_vars: SVars.t;
    (* stage variables used to replace star annotations *)
    stack: SVars.t list;
    (* stack of old pos_vars *)
  }

  let init = {
    next = 0;
    vars = empty;
    pos_vars = empty;
    stack = [];
  }

  let push state = { state with
    pos_vars = empty;
    stack = state.pos_vars :: state.stack }
  let pop state =
    let pos_vars, stack = match state.stack with
    | [] -> empty, state.stack
    | hd :: tl -> hd, tl in
    { state with
      pos_vars = SVars.union pos_vars state.pos_vars;
      stack = stack }

  let get_vars state = state.vars
  let get_pos_vars state = state.pos_vars
  let remove_pos_vars rem state =
    { state with pos_vars = diff state.pos_vars rem }

  let next ?s:(s=Empty) state =
    match s with
    | Empty | Stage Infty ->
      mk state.next 0,
      { state with
        next = succ state.next;
        vars = add state.next state.vars }
    | Star ->
      mk state.next 0,
      { state with
        next = succ state.next;
        vars = add state.next state.vars;
        pos_vars = add state.next state.pos_vars }
    | _ -> (s, state)

  let pr state =
    let open Pp in
    let stg_pp = int state.next in
    let vars_pp = SVars.pr state.vars in
    let stars_pp = SVars.pr state.pos_vars in
    seq [str"<"; stg_pp; pr_comma (); vars_pp; pr_comma (); stars_pp; str ">"]
end

(** Collections of stage constraints *)

(* Constraints.t: A weighted, directed graph.
  Given a constraint v1+s1 ⊑ v2+s2, we add an edge
  from v1 to v2 with weight s2 - s1.
  N.B. Infty stages are stored as (-1) *)
module Constraints =
struct
  open Stage
  open Annot

  module G = WeightedDigraph.Make(Int)
  type t = G.t
  type 'a constrained = 'a * t

  let infty = Stage.infty

  let empty () = G.create ()
  let union_list gs =
    let size = List.fold_left (+) 0 @@ List.map G.nb_vertex gs in
    let g = G.create ~size () in
    List.iter (G.iter_edges_e (G.add_edge_e g)) gs; g
  let union g1 g2 = union_list [g1;g2]
  let remove g s =
    if G.mem_vertex g s
    then
      let g' = G.copy g in
      G.remove_vertex g' s; g'
    else g
  let contains g vfrom vto =
    not @@ List.is_empty @@ G.find_all_edges g vfrom vto
  let add a1 a2 g =
    begin
    match a1, a2 with
    | Stage s1, Stage s2 ->
      begin
      match s1, s2 with
      | Infty, Infty -> g
      | StageVar (var1, sz1), StageVar (var2, sz2) ->
        if var_equal var1 var2 && sz1 <= sz2 then g
        else
          let g' = G.copy g in
          G.add_edge_e g' (var1, (sz2 - sz1), var2); g'
      | Infty, StageVar (var, _) ->
        let g' = G.copy g in
        G.add_edge_e g' (infty, 0, var); g'
      | StageVar _, Infty -> g
      end
    | _ -> g
    end

  let sup g s =
    if G.mem_vertex g s
    then SVars.of_list @@ G.succ g s
    else SVars.empty
  let sub g s =
    if G.mem_vertex g s
    then SVars.of_list @@ G.pred g s
    else SVars.empty

  let bellman_ford g =
    let edges = G.bellman_ford g in
    List.fold_left (fun vars (vfrom, _, vto) ->
      SVars.add vfrom @@ SVars.add vto vars) SVars.empty edges

  let pr g =
    let open Pp in
    let pr_edge (vfrom, wt, vto) =
      let sfrom, sto =
        if wt >= 0
        then StageVar (vfrom,   0), StageVar (vto, wt)
        else StageVar (vfrom, -wt), StageVar (vto,  0) in
      let sfrom = if Stage.var_equal vfrom infty then Infty else sfrom in
      let sto   = if Stage.var_equal vto   infty then Infty else sto   in
      seq [Stage.pr sfrom; str "⊑"; Stage.pr sto] in
    let pr_graph =
      prlist_with_sep pr_comma identity @@
      G.fold_edges_e (fun edge prs -> pr_edge edge :: prs) g [] in
    seq [str "{"; pr_graph; str "}"]
end

(** RecCheck *)
open SVars

exception RecCheckFailed of Constraints.t * SVars.t * SVars.t

(* We could use ocamlgraph's Fixpoint module to compute closures
  but their implementation is very wordy and this suffices *)
let closure get_adj cstrnts init =
  let rec closure_rec init fin =
    match choose_opt init with
    | None -> fin
    | Some s ->
      let init_rest = remove s init in
      if mem s fin
      then closure_rec init_rest fin
      else
        let init_new = get_adj cstrnts s in
        closure_rec (union init_rest init_new) (add s fin) in
  filter (not << Stage.var_equal Stage.infty) (closure_rec init empty)

let downward = closure Constraints.sub
let upward = closure Constraints.sup

let rec_check alpha vstar vneq cstrnts =
  let add_from_set annot_sub =
    fold (fun var_sup cstrnts ->
      Constraints.add annot_sub (Annot.mk var_sup 0) cstrnts) in
  let remove_from_set =
    fold (fun var cstrnts ->
      Constraints.remove cstrnts var) in

  (* Step 1: Si = downward closure containing V* *)
  let si = downward cstrnts vstar in

  (* Step 2: Add α ⊑ Si *)
  let cstrnts1 = add_from_set (Annot.mk alpha 0) si cstrnts in

  (* Step 3: Remove negative cycles *)
  let rec remove_neg cstrnts =
    let v_neg = upward cstrnts (Constraints.bellman_ford cstrnts) in
    let cstrnts_neg = remove_from_set v_neg cstrnts in
    let cstrnts_inf = add_from_set Annot.infty v_neg cstrnts_neg in
    if is_empty v_neg then cstrnts else remove_neg cstrnts_inf in
  let cstrnts2 = remove_neg cstrnts1 in

  (* Step 4: Si⊑ = upward closure containing Si *)
  let si_up = upward cstrnts2 si in

  (* Step 5: S¬i = upward closure containing V≠ *)
  let si_neq = upward cstrnts2 vneq in

  (* Step 6: Add ∞ ⊑ S¬i ∩ Si⊑ *)
  let si_inter = inter si_neq si_up in
  let cstrnts3 = add_from_set Annot.infty si_inter cstrnts2 in

  (* Step 7: S∞ = upward closure containing {∞} *)
  let si_inf = upward cstrnts3 (singleton Stage.infty) in

  (* Step 8: Check S∞ ∩ Si = ∅ *)
  let si_null = inter si_inf si in
  if is_empty si_null then cstrnts3
  else raise (RecCheckFailed (cstrnts, si_inf, si))
