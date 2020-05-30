open Hashset.Combine
open Util

(** Helpers *)
let (<<) f g x = f @@ g x

(** Collections of stage variables *)

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

  (* For annotating Consts, Vars, and Rels *)
  type ts = t list option

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

  let equal a1 a2 = Int.equal 0 @@ compare a1 a2

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

  let hashAns =
    Option.hash (List.fold_left (fun h a -> combine h (hash a)) 0)
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

  let next_annots on state =
    match on with
    | None -> None, state
    | Some n ->
      let next_vars = List.interval state.next (state.next + n - 1) in
      let annots = List.map (fun n -> mk n 0) next_vars in
      let state = { state with
        next = state.next + n;
        vars = union state.vars (of_list next_vars) } in
      Some annots, state

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

  module S = Set.Make(struct
    module G = WeightedDigraph.Make(Int)
    type t = G.edge
    let compare = G.E.compare
  end)
  type t = S.t
  type 'a constrained = 'a * t
  let mkEdge var1 size var2 = (var1, size, var2)

  let infty = Stage.infty

  let empty () = S.empty
  let union = S.union
  let union_list = List.fold_left union (empty ())

  let add a1 a2 set =
    begin
    match a1, a2 with
    | Stage s1, Stage s2 ->
      begin
      match s1, s2 with
      | Infty, Infty -> set
      | StageVar (var1, sz1), StageVar (var2, sz2) ->
        if var_equal var1 var2 && sz1 <= sz2 then set
        else
          S.add (mkEdge var1 (sz2 - sz1) var2) set
      | Infty, StageVar (var, _) ->
        S.add (mkEdge infty 0 var) set
      | StageVar _, Infty -> set
      end
    | _ -> set
    end

  let pr set =
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
      S.fold (fun edge prs -> pr_edge edge :: prs) set [] in
    seq [str "{"; pr_graph; str "}"]
end

(** I don't know where to put this... *)
let annots_to_svars =
  let open SVars in
  let open Stage in
  let open Annot in
  function
  | None -> empty
  | Some ans ->
    List.fold_left (fun svars -> function
      | Stage (StageVar (var, _)) -> add var svars
      | _ -> svars)
      empty ans

(** RecCheck functions and internal graph representation of constraints *)

module RecCheck =
  struct
  open SVars

  module G = WeightedDigraph.Make(Int)
  module S = Constraints.S
  type g = G.t

  let to_graph set =
    let g = G.create () in
    S.iter (G.add_edge_e g) set; g
  let of_graph g =
    G.fold_edges_e S.add g S.empty

  (* N.B. [insert] and [remove] are mutating functions!! *)
  let insert g vfrom wt vto =
    G.add_edge_e g (Constraints.mkEdge vfrom wt vto)
  let remove g s =
    G.remove_vertex g s
  let contains g vfrom vto =
    not @@ List.is_empty @@ G.find_all_edges g vfrom vto

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

  exception RecCheckFailed of Constraints.t * SVars.t * SVars.t

  (* We could use ocamlgraph's Fixpoint module to compute closures
    but their implementation is very wordy and this suffices *)
  let closure get_adj cstrnts init =
    let rec closure_rec init fin =
      match choose_opt init with
      | None -> fin
      | Some s ->
        let init_rest = SVars.remove s init in
        if mem s fin
        then closure_rec init_rest fin
        else
          let init_new = get_adj cstrnts s in
          closure_rec (union init_rest init_new) (add s fin) in
    filter (not << Stage.var_equal Stage.infty) (closure_rec init empty)

  let downward = closure sub
  let upward = closure sup

  let rec_check alpha vstar vneq cstrnts =
    let cstrnts' = to_graph cstrnts in
    let insert_from_set var_sub cstrnts =
      iter (fun var_sup -> insert cstrnts var_sub 0 var_sup) in
    let remove_from_set cstrnts =
      iter (fun var ->
        remove cstrnts var) in

    (* Step 1: Si = downward closure containing V* *)
    let si = downward cstrnts' vstar in

    (* Step 2: Add α ⊑ Si *)
    let () = insert_from_set alpha cstrnts' si in

    (* Step 3: Remove negative cycles *)
    let rec remove_neg cstrnts =
      let v_neg = upward cstrnts (bellman_ford cstrnts) in
      let () = remove_from_set cstrnts' v_neg in
      let () = insert_from_set Stage.infty cstrnts v_neg in
      if not (is_empty v_neg) then remove_neg cstrnts in
    let () = remove_neg cstrnts' in

    (* Step 4: Si⊑ = upward closure containing Si *)
    let si_up = upward cstrnts' si in

    (* Step 5: S¬i = upward closure containing V≠ *)
    let si_neq = upward cstrnts' vneq in

    (* Step 6: Add ∞ ⊑ S¬i ∩ Si⊑ *)
    let si_inter = inter si_neq si_up in
    let () = insert_from_set Stage.infty cstrnts' si_inter in

    (* Step 7: S∞ = upward closure containing {∞} *)
    let si_inf = upward cstrnts' (singleton Stage.infty) in

    (* Step 8: Check S∞ ∩ Si = ∅ *)
    let si_null = inter si_inf si in
    if is_empty si_null then of_graph cstrnts'
    else raise (RecCheckFailed (cstrnts, si_inf, si))
end
