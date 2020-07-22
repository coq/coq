open Hashset.Combine
open Util

(** Helpers *)
let (<<) f g x = f @@ g x

(** Size variables *)

module SVar =
struct
  type t = int
  let equal = Int.equal
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

  let pr s =
    let open Pp in
    match s with
    | Infty -> str "∞"
    | SizeVar (s, n) ->
      if Int.equal n 0 then SVar.pr s else
      seq [SVar.pr s; str "+"; int n]
end

(** Annotations, attached to (co)inductive types *)

module Annot =
struct
  open Size

  type t =
    | Empty (* Bare types with no annotations, input to inference *)
    | Star (* Marks the positions of the (co)recursive types in (co)fixpoints *)
    | Glob (* Marks the positions of the (co)recursive types in global definitions *)
    | Size (* Sized types *) of Size.t

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
    | Glob, Glob   -> 0
    | Glob, _  -> -1 | _, Glob  -> 1
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
    | Glob  -> str "ⁱ"
    | Size s -> Size.pr s

  let show a = Pp.string_of_ppcmds (pr a)

  let hash a =
    match a with
    | Empty -> combine 1 (show a |> String.hash)
    | Star  -> combine 2 (show a |> String.hash)
    | Glob  -> combine 3 (show a |> String.hash)
    | Size Infty -> combine 4 (show a |> String.hash)
    | Size (SizeVar (n, i)) -> combine3 5 (Int.hash n) (Int.hash i)
end

(* (Fake) vectors of annotations, attached to Consts/Vals/Rels *)
module Annots =
struct
  open Annot

  (* If bound to a definition body, [int] gives the number of annotations in the body *)
  type t =
    | Assum (* Assumption and not bound to a body, or the body needs no annots *)
    | Bare of int (* Bare term bound to a definition *)
    | Limit of int (* Limit term bound to a definition *)
    | Sized of SVar.t * int (* Sized term bound to a definition starting with given svar *)

  let vars = function
    | Assum | Bare _ | Limit _ -> SVars.empty
    | Sized (svar, n) -> List.interval svar (svar + n - 1)
      |> SVars.of_list

  let mk = function
    | Assum -> []
    | Bare n -> List.make n Empty
    | Limit n -> List.make n infty
    | Sized (svar, n) -> List.interval svar (svar + n - 1)
      |> List.map (fun var -> mk var 0)

  let length = function
    | Assum -> 0
    | Bare n | Limit n | Sized (_, n) -> n

  let pr ans =
    let open Pp in
    match ans with
    | Assum -> mt ()
    | Bare n -> seq [str "{Empty;"; int n; str "}"]
    | Limit n -> seq [str "{Infty;"; int n; str "}"]
    | Sized (svar, n) -> seq [str "{SVar:"; SVar.pr svar; str ";"; int n; str "}"]

  let show a = Pp.string_of_ppcmds (pr a)

  let hash ans =
    match ans with
    | Assum -> combine 1 (String.hash "Assum")
    | Bare n -> combine 2 (Int.hash n)
    | Limit n -> combine 3 (Int.hash n)
    | Sized (svar, n) -> combine3 4 (Int.hash svar) (Int.hash n)
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
      let annots = Sized (state.next, n) in
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
    filter (not << SVar.is_infty) (closure_rec init empty)

  (* ⊓ (downward closure), ⊔ (upward closure) *)
  let downward = closure sub
  let upward = closure sup

  let rec_check tau vstar vneq cstrnts =
    let cstrnts' = to_graph cstrnts in
    let insert_from_set var_sub cstrnts =
      iter (fun var_sup -> insert cstrnts var_sub 0 var_sup) in
    let remove_from_set cstrnts =
      iter (fun var ->
        remove cstrnts var) in

    (** Step 1: Add V* ⊑ τ *)
    let () = iter (fun v -> insert cstrnts' v 0 tau) vstar in

    (** Step 2: Vi = ⊓V*; add τ ⊑ Vi *)
    let vi = downward cstrnts' vstar in
    let () = insert_from_set tau cstrnts' vi in

    (** Step 3, 4: Find, remove negative cycles *)
    let rec remove_neg cstrnts =
      let v_neg = upward cstrnts (bellman_ford cstrnts) in
      let () = remove_from_set cstrnts' v_neg in
      let () = insert_from_set SVar.infty cstrnts v_neg in
      if not (is_empty v_neg) then remove_neg cstrnts in
    let () = remove_neg cstrnts' in

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
end
