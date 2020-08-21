open Hashset.Combine
open Util

(** Helpers *)
let (<<) f g x = f @@ g x

(** Size variables *)

module SVar =
struct
  type t = int
  let equal = Int.equal
  let compare = Int.compare
  let succ = succ
  let skip = (+)
  let infty = -1 (* For constraint representation only!!! *)
  let is_infty = equal infty
  let pr var =
    let open Pp in
    str "s" ++ int var
end

(** Collections of size variables *)

module SVars =
struct
  include Int.Set

  let union_list = List.fold_left union empty

  let pr vars =
    let open Pp in
    let pr_var v = str "s" ++ int v in
    seq [str "{"; pr_enum pr_var (elements vars); str "}"]
end

(** Sizes, for sized annotations *)

module Size =
struct
  type t = Infty | SizeVar of SVar.t * int

  let mk var size = SizeVar (var, size)

  let compare s1 s2 =
    match s1, s2 with
    | Infty, Infty -> 0
    | Infty, _     -> 1
    | _, Infty     -> -1
    | SizeVar (var1, sz1), SizeVar (var2, sz2) ->
      let nc = Int.compare var1 var2 in
      if not (Int.equal nc 0) then nc
      else Int.compare sz1 sz2

  let equal s1 s2 = Int.equal 0 @@ compare s1 s2

  (* Substitute the size variable of [sof] by size expression [sby] *)
  let subst sof sby =
    if sof == sby || equal sof sby then sof else
    match sof with
    | Infty -> sof
    | SizeVar (_, size) ->
      if Int.equal size 0 then sby else
      match sby with
      | Infty -> sby
      | SizeVar (svar, size') -> SizeVar (svar, size + size')

  let pr s =
    let open Pp in
    match s with
    | Infty -> str "∞"
    | SizeVar (s, n) ->
      if Int.equal n 0 then SVar.pr s else
      seq [SVar.pr s; str "+"; int n]

  let show a = Pp.string_of_ppcmds (pr a)

  let hash a =
    match a with
    | Infty -> combine 1 (show a |> String.hash)
    | SizeVar (n, i) -> combine3 2 (Int.hash n) (Int.hash i)
end

(** Annotations, attached to (co)inductive types *)

module Annot =
struct
  open Size

  type t =
    | Empty (* Bare types with no annotations, input to inference *)
    | Star (* Marks the positions of the (co)recursive types in (co)fixpoints *)
    | Size of Size.t (* Sized types *)

  let infty = Size Infty

  let mk var size = Size (Size.mk var size)

  let hat a =
    match a with
    | Size (SizeVar (var, sz)) -> Size (SizeVar (var, succ sz))
    | _ -> a

  let compare a1 a2 =
    match a1, a2 with
    | Empty, Empty -> 0
    | Empty, _ -> -1 | _, Empty -> 1
    | Star, Star   -> 0
    | Star, _  -> -1 | _, Star  -> 1
    | Size s1, Size s2 -> Size.compare s1 s2

  let equal a1 a2 = Int.equal 0 @@ compare a1 a2

  let sizevar_opt = function
    | Size (SizeVar (var, _)) -> Some var
    | _ -> None

  let pr a =
    let open Pp in
    match a with
    | Empty -> mt ()
    | Star  -> str "*"
    | Size s -> Size.pr s

  let show a = Pp.string_of_ppcmds (pr a)

  let hash a =
    match a with
    | Empty -> combine 1 (show a |> String.hash)
    | Star  -> combine 2 (show a |> String.hash)
    | Size s -> combine 3 (Size.hash s)
end

(* (Fake) vectors of annotations, attached to Consts/Vals/Rels *)
module Annots =
struct
  open Size

  (* If bound to a definition body, [int] gives the number of annotations in the body *)
  type t =
    | Assum (* Assumption and not bound to a body, or the body needs no annots *)
    | Bare of int (* Bare term bound to a definition *)
    | Limit of int (* Limit term bound to a definition *)
    | Sized of Size.t array (* Sized term bound to a definition starting with given svar *)

  let vars = function
    | Assum | Bare _ | Limit _ -> SVars.empty
    | Sized sizes ->
      let f svars = function
      | Infty -> svars
      | SizeVar (svar, _) -> SVars.add svar svars in
      Array.fold_left f SVars.empty sizes

  let mk svar n = List.interval svar (svar + n - 1)
    |> List.map (fun var -> Size.mk var 0)
    |> Array.of_list
    |> (fun sizes -> Sized sizes)

  let length = function
    | Assum -> 0
    | Bare n | Limit n -> n
    | Sized sizes -> Array.length sizes

  let pr ans =
    let open Pp in
    match ans with
    | Assum -> mt ()
    | Bare n -> seq [str "{Empty;"; int n; str "}"]
    | Limit n -> seq [str "{Infty;"; int n; str "}"]
    | Sized sizes -> seq [str "{SVar:"; prvect_with_sep pr_comma Size.pr sizes; str "}"]

  let show a = Pp.string_of_ppcmds (pr a)

  let hash ans =
    match ans with
    | Assum -> combine 1 (String.hash "Assum")
    | Bare n -> combine 2 (Int.hash n)
    | Limit n -> combine 3 (Int.hash n)
    | Sized sizes -> combine 4 (Array.fold_left (fun acc t -> combine acc (Size.hash t)) 0 sizes)
end

(** Size state, keeping track of used size variables *)

module State =
struct
  open SVars
  open Size
  open Annot
  open Annots

  type t = {
    next: SVar.t;
    (* next size variable to be used *)
    vars: SVars.t;
    (* all used size variables *)
    pos_vars: SVars.t;
    (* size variables used to replace star annotations *)
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
    | Empty | Size Infty ->
      Annot.mk state.next 0,
      { state with
        next = succ state.next;
        vars = add state.next state.vars }
    | Star ->
      Annot.mk state.next 0,
      { state with
        next = succ state.next;
        vars = add state.next state.vars;
        pos_vars = add state.next state.pos_vars }
    | _ -> (s, state)

  let next_annots check_sized on state =
    match on with
    | Some n when n > 0 ->
      if not check_sized then Limit n, state else
      let next_vars = List.interval state.next (state.next + n - 1) in
      let annots = Annots.mk state.next n in
      let state = { state with
        next = state.next + n;
        vars = union state.vars (of_list next_vars) } in
      annots, state
    | _ -> Assum, state

  let pr state =
    let open Pp in
    let stg_pp = SVar.pr state.next in
    let vars_pp = SVars.pr state.vars in
    let stars_pp = SVars.pr state.pos_vars in
    seq [str"<"; stg_pp; pr_comma (); vars_pp; pr_comma (); stars_pp; str ">"]
end

(** Size variable substitution maps from size variables to sizes *)

module SMap =
struct
  open Size

  module M = Map.Make(SVar)
  type t = Size.t M.t

  let empty = M.empty
  let get var smap =
    match M.find_opt var smap with
    | Some s -> s
    | None -> mk var 0
  let add key s smap =
    match M.find_opt key smap with
    | Some _ -> smap
    | None -> M.add key s smap

  let subst smap sof =
    match sof with
    | Infty -> sof
    | SizeVar (svar, size) ->
      let sby = get svar smap in
      if sof == sby || Size.equal sof sby then sof else
      if Int.equal size 0 then sby else
      match sby with
      | Infty -> sby
      | SizeVar (svar', size') -> SizeVar (svar', size + size')

  let pr smap =
    let open Pp in
    let pr_map (v, s) = SVar.pr v ++ str " ↦ " ++ Size.pr s in
    seq [str "{"; pr_enum pr_map (M.bindings smap); str "}"]
end

(** Collections of size constraints *)

(* Constraints.t: A weighted, directed graph.
  Given a constraint v1+s1 ⊑ v2+s2, we add an edge
  from v1 to v2 with weight s2 - s1.
  N.B. Infty sizes are stored as (-1) *)
module Constraints =
struct
  open Size
  open Annot

  module S = Set.Make(struct
    module G = WeightedDigraph.Make(Int)
    type t = G.edge
    let compare = G.E.compare
  end)

  type t = S.t
  type 'a constrained = 'a * t
  let mkEdge var1 size var2 = (var1, size, var2)

  let empty () = S.empty
  let union = S.union
  let add a1 a2 cstrnts =
    begin
    match a1, a2 with
    | Size s1, Size s2 ->
      begin
      match s1, s2 with
      | Infty, Infty -> cstrnts
      | SizeVar (var1, sz1), SizeVar (var2, sz2) ->
        if SVar.equal var1 var2 && sz1 <= sz2 then cstrnts
        else S.add (mkEdge var1 (sz2 - sz1) var2) cstrnts
      | Infty, SizeVar (var, _) ->
        S.add (mkEdge SVar.infty 0 var) cstrnts
      | SizeVar _, Infty -> cstrnts
      end
    | _ -> cstrnts
    end

  let map smap =
    let f (var1, size, var2) cstrnts =
      let s1 = SMap.get var1 smap in
      let s2 = SMap.get var2 smap in
      match s1, s2 with
      | Infty, Infty -> cstrnts
      | SizeVar (var1, sz1), SizeVar (var2, sz2) ->
        if SVar.equal var1 var2 && sz1 <= sz2 + size then cstrnts
        else S.add (mkEdge var1 (size + sz2 - sz1) var2) cstrnts
      | Infty, SizeVar (var, _) ->
        S.add (mkEdge SVar.infty 0 var) cstrnts
      | SizeVar _, Infty -> cstrnts in
    S.fold f (empty ())

  let pr cstrnts =
    let open Pp in
    let pr_edge (vfrom, wt, vto) =
      let sfrom, sto =
        if wt >= 0
        then SizeVar (vfrom,   0), SizeVar (vto, wt)
        else SizeVar (vfrom, -wt), SizeVar (vto,  0) in
      let sfrom = if SVar.is_infty vfrom then Infty else sfrom in
      let sto   = if SVar.is_infty vto   then Infty else sto   in
      seq [Size.pr sfrom; str "⊑"; Size.pr sto] in
    let pr_graph =
      prlist_with_sep pr_comma identity @@
      S.fold (fun edge prs -> pr_edge edge :: prs) cstrnts [] in
    seq [str "{"; pr_graph; str "}"]
end

(** RecCheck functions and internal graph representation of constraints *)

module RecCheck =
  struct
  open SVars

  module S = Constraints.S
  module G = WeightedDigraph.Make(Int)
  type g = G.t

  let to_graph cstrnts =
    let g = G.create () in
    S.iter (G.add_edge_e g) cstrnts; g
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

  let find_negative_cycle_vars g =
    let edges = G.find_negative_cycle g in
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
    filter (not << SVar.is_infty) (closure_rec init empty)

  (* ⊓ (downward closure), ⊔ (upward closure) *)
  let downward = closure sub
  let upward = closure sup

  let insert_from_set var_sub cstrnts =
    iter (fun var_sup -> insert cstrnts var_sub 0 var_sup)
  let remove_from_set cstrnts =
    iter (fun var ->
      remove cstrnts var)

  let rec remove_neg cstrnts vneg =
    let vneg' = upward cstrnts (find_negative_cycle_vars cstrnts) in
    let () = remove_from_set cstrnts vneg' in
    let () = insert_from_set SVar.infty cstrnts vneg' in
    if not (is_empty vneg') then remove_neg cstrnts (union vneg vneg') else vneg
  let remove_neg cstrnts = remove_neg cstrnts empty

  let rec_check tau vstar vneq cstrnts =
    let cstrnts' = to_graph cstrnts in

    (** Step 1: Add V* ⊑ τ *)
    let () = iter (fun v -> insert cstrnts' v 0 tau) vstar in

    (** Step 2: Vi = ⊓V*; add τ ⊑ Vi *)
    let vi = downward cstrnts' vstar in
    let () = insert_from_set tau cstrnts' vi in

    (** Step 3, 4: Find, remove negative cycles *)
    let () = ignore @@ remove_neg cstrnts' in

    (** Step 5: Add ∞ ⊑ ⊔V≠ ∩ ⊔Vi *)
    let vi_up = upward cstrnts' vi in
    let vneq_up = upward cstrnts' vneq in
    let vinter = inter vneq_up vi_up in
    let () = insert_from_set SVar.infty cstrnts' vinter in

    (** Step 6: Check ⊔{∞} ∩ Vi = ∅ *)
    let vinf = upward cstrnts' (singleton SVar.infty) in
    let vnull = inter vinf vi in
    if is_empty vnull then of_graph cstrnts'
    else raise (RecCheckFailed (cstrnts, vinf, vi))

  let solve cstrnts state =
    let cstrnts = to_graph cstrnts in

    (* Remove all size variables that must be mapped to infty
      and map them to infty in the substitution map *)
    let vneg = remove_neg cstrnts in
    let vinf = upward cstrnts (singleton SVar.infty) in
    let () = iter (fun var -> remove cstrnts var) vinf in
    let smap = SVars.fold (fun var smap -> SMap.add var Size.Infty smap) (union vneg vinf) SMap.empty in

    (* Find a valid substitution map for a given connected component *)
    let solve (state, smap) component =
      let open State in
      let base = state.next in
      let state = { state with next = succ state.next } in

      (* The shortest path of weight w from vfrom to all vtos is the constraint {vfrom ⊑ vto + w}.
        Therefore, we want to map each vto to (vfrom - w). However, hats are never negative,
        so we add to each the maximum weight wmax: [vto ↦ vfrom + wmax - w].
        This has the added bonus of guaranteeing a "minimal" solution in that
        no annotation can have a fewer number of hats than (wmax - w). *)
      let () = List.iter (fun vto -> insert cstrnts base 0 vto) component in
      let shortest_paths = G.all_shortest_paths cstrnts base in
      let wmax = List.fold_left (fun i vj -> max i (snd vj)) min_int shortest_paths in
      let smap = List.fold_left (fun smap (var, w) -> SMap.add var (Size.mk base (wmax - w)) smap) smap shortest_paths in
    state, smap in

    (* Get all the connected components of the graph
      and deal with them one at a time *)
    let components = G.components cstrnts in
    Array.fold_left solve (state, smap) components
end
