open Util

(** From https://github.com/backtracking/ocamlgraph *)

(*
  Some notable changes:
  * Modules not needed for ConcreteBidirectionalLabeled have been removed
  * Blocks.Make => MakeDigraph
  * Components.Make => MakeComp
  * Fixpoint.Make => MakeFix
  * Generic(G : IM with type V.label = int and type E.label = int) =>
    Generic(G: I with type E.label = int)
*)

[@@@ocaml.warning "-32"]
[@@@ocaml.warning "-60"]

(** Sig *)

module type ORDERED_TYPE = sig
  type t
  val compare : t -> t -> int
end

module type ORDERED_TYPE_DFT = sig
  include ORDERED_TYPE
  val default : t
end

module type COMPARABLE = sig
  type t
  val compare : t -> t -> int
  val hash : t -> int
  val equal : t -> t -> bool
end

module type VERTEX = sig
  type t
  include COMPARABLE with type t := t
  type label
  val create : label -> t
  val label : t -> label
end

module type EDGE = sig
  type t
  val compare : t -> t -> int

  type vertex
  val src : t -> vertex
  val dst : t -> vertex

  type label
  val create : vertex -> label -> vertex -> t
  val label : t -> label
end

module type WEIGHT = sig
  type edge
  type t
  val weight : edge -> t
  val compare : t -> t -> int
  val add : t -> t -> t
  val zero : t
end

module type G = sig
  (** {2 Graph structure} *)

  (** Abstract type of graphs *)
  type t

  (** Vertices have type [V.t]. *)
  module V : VERTEX
  type vertex = V.t

  (** Edges have type [E.t] and are labeled with type [E.label].
      [src] (resp. [dst]) returns the origin (resp. the destination) of a
      given edge. *)
  module E : EDGE with type vertex = vertex
  type edge = E.t

  (** Is this an implementation of directed graphs? *)
  val is_directed : bool

  (** {2 Size functions} *)

  val is_empty : t -> bool
  val nb_vertex : t -> int
  val nb_edges : t -> int

  (** Degree of a vertex *)

  val out_degree : t -> vertex -> int
  (** [out_degree g v] returns the out-degree of [v] in [g].
      @raise Invalid_argument if [v] is not in [g]. *)

  val in_degree : t -> vertex -> int
  (** [in_degree g v] returns the in-degree of [v] in [g].
      @raise Invalid_argument if [v] is not in [g]. *)

  (** {2 Membership functions} *)

  val mem_vertex : t -> vertex -> bool
  val mem_edge : t -> vertex -> vertex -> bool
  val mem_edge_e : t -> edge -> bool

  val find_edge : t -> vertex -> vertex -> edge
  (** [find_edge g v1 v2] returns the edge from [v1] to [v2] if it exists.
      Unspecified behaviour if [g] has several edges from [v1] to [v2].
      @raise Not_found if no such edge exists. *)

  val find_all_edges : t -> vertex -> vertex -> edge list
  (** [find_all_edges g v1 v2] returns all the edges from [v1] to [v2].
      @since ocamlgraph 1.8 *)

  (** {2 Successors and predecessors}

      You should better use iterators on successors/predecessors (see
      Section "Vertex iterators"). *)

  val succ : t -> vertex -> vertex list
  (** [succ g v] returns the successors of [v] in [g].
      @raise Invalid_argument if [v] is not in [g]. *)

  val pred : t -> vertex -> vertex list
  (** [pred g v] returns the predecessors of [v] in [g].
      @raise Invalid_argument if [v] is not in [g]. *)

  (** Labeled edges going from/to a vertex *)

  val succ_e : t -> vertex -> edge list
  (** [succ_e g v] returns the edges going from [v] in [g].
      @raise Invalid_argument if [v] is not in [g]. *)

  val pred_e : t -> vertex -> edge list
  (** [pred_e g v] returns the edges going to [v] in [g].
      @raise Invalid_argument if [v] is not in [g]. *)

  (** {2 Graph iterators} *)

  val iter_vertex : (vertex -> unit) -> t -> unit
  (** Iter on all vertices of a graph. *)

  val fold_vertex : (vertex -> 'a -> 'a) -> t -> 'a -> 'a
  (** Fold on all vertices of a graph. *)

  val iter_edges : (vertex -> vertex -> unit) -> t -> unit
  (** Iter on all edges of a graph. Edge label is ignored. *)

  val fold_edges : (vertex -> vertex -> 'a -> 'a) -> t -> 'a -> 'a
  (** Fold on all edges of a graph. Edge label is ignored. *)

  val iter_edges_e : (edge -> unit) -> t -> unit
  (** Iter on all edges of a graph. *)

  val fold_edges_e : (edge -> 'a -> 'a) -> t -> 'a -> 'a
  (** Fold on all edges of a graph. *)

  val map_vertex : (vertex -> vertex) -> t -> t
  (** Map on all vertices of a graph. *)

  (** {2 Vertex iterators}

      Each iterator [iterator f v g] iters [f] to the successors/predecessors
      of [v] in the graph [g] and raises [Invalid_argument] if [v] is not in
      [g]. It is the same for functions [fold_*] which use an additional
      accumulator.

      <b>Time complexity for ocamlgraph implementations:</b>
      operations on successors are in O(1) amortized for imperative graphs and
      in O(ln(|V|)) for persistent graphs while operations on predecessors are
      in O(max(|V|,|E|)) for imperative graphs and in O(max(|V|,|E|)*ln|V|) for
      persistent graphs. *)

  (** iter/fold on all successors/predecessors of a vertex. *)
  val iter_succ : (vertex -> unit) -> t -> vertex -> unit
  val iter_pred : (vertex -> unit) -> t -> vertex -> unit
  val fold_succ : (vertex -> 'a -> 'a) -> t -> vertex -> 'a -> 'a
  val fold_pred : (vertex -> 'a -> 'a) -> t -> vertex -> 'a -> 'a

  (** iter/fold on all edges going from/to a vertex. *)
  val iter_succ_e : (edge -> unit) -> t -> vertex -> unit
  val fold_succ_e : (edge -> 'a -> 'a) -> t -> vertex -> 'a -> 'a
  val iter_pred_e : (edge -> unit) -> t -> vertex -> unit
  val fold_pred_e : (edge -> 'a -> 'a) -> t -> vertex -> 'a -> 'a
end

module type I = sig
  include G
  (** An imperative graph is a graph. *)

  val create : ?size:int -> unit -> t
  (** [create ()] returns an empty graph. Optionally, a size can be
      given, which should be on the order of the expected number of
      vertices that will be in the graph (for hash tables-based
      implementations).  The graph grows as needed, so [size] is
      just an initial guess. *)

  val clear: t -> unit
  (** Remove all vertices and edges from the given graph.
      @since ocamlgraph 1.4 *)

  val copy : t -> t
  (** [copy g] returns a copy of [g]. Vertices and edges (and eventually
      marks, see module [Mark]) are duplicated. *)

  val add_vertex : t -> vertex -> unit
  (** [add_vertex g v] adds the vertex [v] to the graph [g].
      Do nothing if [v] is already in [g]. *)

  val remove_vertex : t -> vertex -> unit
  (** [remove g v] removes the vertex [v] from the graph [g]
      (and all the edges going from [v] in [g]).
      Do nothing if [v] is not in [g].

      <b>Time complexity for ocamlgraph implementations:</b>
      O(|V|*ln(D)) for unlabeled graphs and O(|V|*D)  for
      labeled graphs. D is the maximal degree of the graph. *)

  val add_edge : t -> vertex -> vertex -> t
  (** [add_edge g v1 v2] adds an edge from the vertex [v1] to the vertex [v2]
      in the graph [g].
      Add also [v1] (resp. [v2]) in [g] if [v1] (resp. [v2]) is not in [g].
      Just return [g] if this edge is already in [g]. *)

  val add_edge_e : t -> edge -> unit
  (** [add_edge_e g e] adds the edge [e] in the graph [g].
      Add also [E.src e] (resp. [E.dst e]) in [g] if [E.src e] (resp. [E.dst
      e]) is not in [g].
      Do nothing if [e] is already in [g]. *)

  val remove_edge : t -> vertex -> vertex -> unit
  (** [remove_edge g v1 v2] removes the edge going from [v1] to [v2] from the
      graph [g]. If the graph is labelled, all the edges going from [v1] to
      [v2] are removed from [g].
      Do nothing if this edge is not in [g].
      @raise Invalid_argument if [v1] or [v2] are not in [g]. *)

  val remove_edge_e : t -> edge -> unit
  (** [remove_edge_e g e] removes the edge [e] from the graph [g].
      Do nothing if [e] is not in [g].
      @raise Invalid_argument if [E.src e] or [E.dst e] are not in [g]. *)
end

(** Util *)

module OTProduct(X: ORDERED_TYPE)(Y: ORDERED_TYPE) = struct
  type t = X.t * Y.t
  let compare (x1, y1) (x2, y2) =
    let cv = X.compare x1 x2 in
    if Int.equal cv 0 then Y.compare y1 y2 else cv
end

(** Blocks *)

module type HM = sig
  type 'a return
  type 'a t
  type key
  val create : ?size:int -> unit -> 'a t
  val create_from : 'a t -> 'a t
  val empty : 'a return
  val clear: 'a t -> unit
  val is_empty : 'a t -> bool
  val add : key -> 'a -> 'a t -> 'a t
  val remove : key -> 'a t -> 'a t
  val mem : key -> 'a t -> bool
  val find : key -> 'a t -> 'a
  val find_and_raise : key -> 'a t -> string -> 'a
  val iter : (key -> 'a -> unit) -> 'a t -> unit
  val map : (key -> 'a -> key * 'a) -> 'a t -> 'a t
  val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
  val copy : 'a t -> 'a t
end

module type TBL_BUILDER = functor(X: COMPARABLE) -> HM with type key = X.t

module BidirectionalLabeled
    (V: COMPARABLE)(E: ORDERED_TYPE)(HM: HM with type key = V.t) =
struct
  module VE = OTProduct(V)(E)
  module S = Set.Make(VE)

  module E = struct
    type vertex = V.t
    type label = E.t
    type t = vertex * label * vertex
    let src (v, _, _) = v
    let dst (_, _, v) = v
    let label (_, l, _) = l
    let create v1 l v2 = v1, l, v2
    module C = OTProduct(V)(VE)
    let compare (x1, x2, x3) (y1, y2, y3) =
      C.compare (x1, (x3, x2)) (y1, (y3, y2))
  end
  type edge = E.t

  let mem_edge g v1 v2 =
    try S.exists (fun (v2', _) -> V.equal v2 v2') (snd (HM.find v1 g))
    with Not_found -> false
  let mem_edge_e g (v1, l, v2) =
    try
      let ve = v2, l in
      S.exists (fun ve' -> VE.compare ve ve' = 0) (snd (HM.find v1 g))
    with Not_found ->
      false

  exception Found of edge
  let find_edge g v1 v2 =
    try
      S.iter
        (fun (v2', l) -> if V.equal v2 v2' then raise (Found (v1, l, v2')))
        (snd (HM.find v1 g));
      raise Not_found
    with Found e ->
      e
  let find_all_edges g v1 v2 =
    try
      S.fold
        (fun (v2', l) acc ->
           if V.equal v2 v2' then (v1, l, v2') :: acc else acc)
        (snd (HM.find v1 g))
        []
    with Not_found ->
      []

  let unsafe_remove_edge g v1 v2 =
    let in_set, out_set = HM.find v1 g in
    let del v set = S.filter (fun (v', _) -> not (V.equal v v')) set in
    let g = HM.add v1 (in_set, del v2 out_set) g in
    let in_set, out_set = HM.find v2 g in
    HM.add v2 (del v1 in_set, out_set) g
  let unsafe_remove_edge_e g (v1, l, v2) =
    let in_set, out_set = HM.find v1 g in
    let g = HM.add v1 (in_set, S.remove (v2, l) out_set) g in
    let in_set, out_set = HM.find v2 g in
    HM.add v2 (S.remove (v1, l) in_set, out_set) g
  let remove_edge g v1 v2 =
    (*    if not (HM.mem v2 g) then invalid_arg "[ocamlgraph] remove_edge";*)
    let in_set, out_set = HM.find_and_raise v1 g "[ocamlgraph] remove_edge" in
    let del v set = S.filter (fun (v', _) -> not (V.equal v v')) set in
    let g = HM.add v1 (in_set, del v2 out_set) g in
    let in_set, out_set = HM.find_and_raise v2 g "[ocamlgraph] remove_edge" in
    HM.add v2 (del v1 in_set, out_set) g
  let remove_edge_e g (v1, l, v2) =
    (*    if not (HM.mem v2 g) then invalid_arg "[ocamlgraph] remove_edge_e";*)
    let in_set, out_set = HM.find_and_raise v1 g "[ocamlgraph] remove_edge_e" in
    let g = HM.add v1 (in_set, S.remove (v2, l) out_set) g in
    let in_set, out_set = HM.find_and_raise v2 g "[ocamlgraph] remove_edge_e" in
    HM.add v2 (S.remove (v1, l) in_set, out_set) g

  let iter_succ f g v =
    S.iter
      (fun (w, _) -> f w)
      (snd (HM.find_and_raise v g "[ocamlgraph] iter_succ"))
  let fold_succ f g v =
    S.fold
      (fun (w, _) -> f w)
      (snd (HM.find_and_raise v g "[ocamlgraph] fold_succ"))
  let iter_succ_e f g v =
    S.iter
      (fun (w, l) -> f (v, l, w))
      (snd (HM.find_and_raise v g "[ocamlgraph] iter_succ_e"))
  let fold_succ_e f g v =
    S.fold
      (fun (w, l) -> f (v, l, w))
      (snd (HM.find_and_raise v g "[ocamlgraph] fold_succ_e"))

  let succ g v = fold_succ (fun w l -> w :: l) g v []
  let succ_e g v = fold_succ_e (fun e l -> e :: l) g v []

  let map_vertex f =
    HM.map
      (fun v (s1,s2) ->
         f v,
         (S.fold (fun (v, l) s -> S.add (f v, l) s) s1 S.empty,
          S.fold (fun (v, l) s -> S.add (f v, l) s) s2 S.empty))

  module I = struct
    type t = (S.t * S.t) HM.t
    module PV = V
    module PE = E
    let iter_edges f = HM.iter (fun v (_,outset) ->
        S.iter (fun (w, _) -> f v w) outset)
    let fold_edges f = HM.fold (fun v (_,outset) ->
        S.fold (fun (w, _) -> f v w) outset)
    let iter_edges_e f = HM.iter (fun v (_,outset) ->
        S.iter (fun (w, l) -> f (v, l, w)) outset)
    let fold_edges_e f = HM.fold (fun v (_,outset) ->
        S.fold (fun (w, l) -> f (v, l, w)) outset)
  end
  include I

  let in_degree g v =
    S.cardinal
      (fst (try HM.find v g
            with Not_found -> invalid_arg "[ocamlgraph] in_degree"))

  let iter_pred f g v =
    S.iter
      (fun (w, _) -> f w)
      (fst (HM.find_and_raise v g "[ocamlgraph] iter_pred"))
  let fold_pred f g v =
    S.fold
      (fun (w, _) -> f w)
      (fst (HM.find_and_raise v g "[ocamlgraph] fold_pred"))
  let iter_pred_e f g v =
    S.iter
      (fun (w, l) -> f (w, l, v))
      (fst (HM.find_and_raise v g "[ocamlgraph] iter_pred_e"))
  let fold_pred_e f g v =
    S.fold
      (fun (w, l) -> f (w, l, v))
      (fst (HM.find_and_raise v g "[ocamlgraph] fold_pred_e"))

  let pred g v = fold_pred (fun w l -> w :: l) g v []
  let pred_e g v = fold_pred_e (fun e l -> e :: l) g v []
end

module BidirectionalMinimal(S: Set.S)(HM: HM) = struct
  type vertex = HM.key
  let is_directed = true
  let empty = HM.empty
  let create = HM.create
  let clear = HM.clear
  let is_empty = HM.is_empty
  let copy = HM.copy
  let nb_vertex g = HM.fold (fun _ _ -> succ) g 0
  let nb_edges g = HM.fold (fun _ (_,s) n -> n + S.cardinal s) g 0
  let out_degree g v =
    S.cardinal
      (snd (try HM.find v g
            with Not_found -> invalid_arg "[ocamlgraph] out_degree"))
  let mem_vertex g v = HM.mem v g
  let unsafe_add_vertex g v = HM.add v (S.empty, S.empty) g
  let add_vertex g v = if HM.mem v g then g else unsafe_add_vertex g v
  let iter_vertex f = HM.iter (fun v _ -> f v)
  let fold_vertex f = HM.fold (fun v _ -> f v)
end

module ConcreteVertex(F: TBL_BUILDER)(V: COMPARABLE) = struct
  module V = struct
    include V
    type label = t
    let label v = v
    let create v = v
  end
  module HM = F(V)
end

module Make_Hashtbl(X: COMPARABLE) = struct
  include Hashtbl.Make(X)
  type 'a return = unit
  let empty = ()
  (* never call and not visible for the user thank's to signature
     constraints *)
  let create_from h = create (length h)
  let create ?(size=97) () = create size
  let is_empty h = (length h = 0)
  let find_and_raise k h s = try find h k with Not_found -> invalid_arg s
  let map f h =
    let h' = create_from h  in
    iter (fun k v -> let k, v = f k v in add h' k v) h;
    h'
  let add k v h = replace h k v; h
  let remove k h = remove h k; h
  let mem k h = mem h k
  let find k h = find h k
end

module MakeDigraph(F: TBL_BUILDER) = struct
  module Digraph = struct
    module ConcreteBidirectionalLabeled
        (V: COMPARABLE)(Edge: ORDERED_TYPE_DFT) =
    struct
      include ConcreteVertex(F)(V)
      include BidirectionalLabeled(V)(Edge)(HM)
      include BidirectionalMinimal(S)(HM)
      let unsafe_add_edge_e g (v1, l, v2) =
        let find v g = try HM.find v g with Not_found -> S.empty, S.empty in
        let in_set, out_set = find v1 g in
        let g = HM.add v1 (in_set,S.add (v2,l) out_set) g in
        let in_set, out_set = find v2 g in
        HM.add v2 (S.add (v1,l) in_set,out_set) g
      let add_edge_e g e = if mem_edge_e g e then g else unsafe_add_edge_e g e
      let add_edge g v1 v2 = add_edge_e g (v1, Edge.default, v2)
    end
  end
end

(** Imperative *)

module I = MakeDigraph(Make_Hashtbl)

module Digraph = struct
  module ConcreteBidirectionalLabeled
    (V: COMPARABLE)(E: ORDERED_TYPE_DFT) =
  struct
    include I.Digraph.ConcreteBidirectionalLabeled(V)(E)
    let add_vertex g v = ignore (add_vertex g v)
    let add_edge_e g (v1, l, v2) = ignore (add_edge_e g (v1, l, v2))
    let remove_edge g v1 v2 = ignore (remove_edge g v1 v2)
    let remove_edge_e g e = ignore (remove_edge_e g e)
    let remove_vertex g v =
      if HM.mem v g then begin
        iter_pred_e (fun e -> remove_edge_e g e) g v;
        iter_succ_e (fun e -> remove_edge_e g e) g v;
        ignore (HM.remove v g)
      end
  end
end

(** Components *)

module MakeComp(G: G) = struct
  module H = Hashtbl.Make(G.V)

  type action =
    | Finish of G.V.t * int
    | Visit of G.V.t * G.V.t
    | Test of G.V.t * G.V.t

  let scc g =
    let root = H.create 997 in
    let hashcomp = H.create 997 in
    let stack = ref [] in
    let numdfs = ref 0 in
    let numcomp = ref 0 in
    let rec pop x = function
      | ((y: int), w) :: l when y > x ->
        H.add hashcomp w !numcomp;
        pop x l
      | l -> l
    in
    let cont = ref [] in
    let visit v =
      if not (H.mem root v) then begin
        let n = incr numdfs; !numdfs in
        H.add root v n;
        cont := Finish (v, n) :: !cont;
        G.iter_succ
          (fun w ->
             cont := Visit (v, w) :: Test (v, w) :: !cont)
          g v;
      end
    in
    let rec finish () = match !cont with
      | [] -> ()
      | action :: tail ->
        cont := tail;
        begin match action with
          | Finish (v, n) ->
            if H.find root v = n then begin
              H.add hashcomp v !numcomp;
              let s = pop n !stack in
              stack:= s;
              incr numcomp
            end else
              stack := (n, v) :: !stack;
          | Visit (_, w) -> visit w
          | Test (v, w) ->
            if not (H.mem hashcomp w) then
              H.replace root v (min (H.find root v) (H.find root w))
        end;
        finish ()
    in
    let visit_and_finish v =
      visit v;
      finish ()
    in
    G.iter_vertex visit_and_finish g;
    !numcomp, (fun v -> H.find hashcomp v)

  let scc_array g =
    let n,f = scc g in
    let t = Array.make n [] in
    G.iter_vertex (fun v -> let i = f v in t.(i) <- v :: t.(i)) g;
    t

  let scc_list g =
    let a = scc_array g in
    Array.fold_right (fun l acc -> l :: acc) a []
end

(** Path *)

module BellmanFord
  (G: G)(W: WEIGHT with type edge = G.E.t) =
struct
  open G.E

  module H = Hashtbl.Make(G.V)

  exception NegativeCycle of G.E.t list

  let all_shortest_paths g vs =
    let dist = H.create 97 in
    H.add dist vs W.zero;
    let admissible = H.create 97 in
    let build_cycle_from x0 =
      let rec traverse_parent x ret =
        let e = H.find admissible x in
        let s = src e in
        if G.V.equal s x0 then e :: ret else traverse_parent s (e :: ret)
      in
      traverse_parent x0 []
    in
    let find_cycle x0 =
      let visited = H.create 97 in
      let rec visit x =
        if H.mem visited x then
          build_cycle_from x
        else begin
          H.add visited x ();
          let e = H.find admissible x in
          visit (src e)
        end
      in
      visit x0
    in
    let rec relax i =
      let update = G.fold_edges_e
          (fun e x ->
             let ev1 = src e in
             let ev2 = dst e in
             try begin
               let dev1 = H.find dist ev1 in
               let dev2 = W.add dev1 (W.weight e) in
               let improvement =
                 try W.compare dev2 (H.find dist ev2) < 0
                 with Not_found -> true
               in
               if improvement then begin
                 H.replace dist ev2 dev2;
                 H.replace admissible ev2 e;
                 Some ev2
               end else x
             end with Not_found -> x) g None in
      match update with
      | Some x ->
        if i == G.nb_vertex g then raise (NegativeCycle (find_cycle x))
        else relax (i + 1)
      | None -> dist
    in
    relax 0

  let find_negative_cycle_from g vs =
    try let _ = all_shortest_paths g vs in raise Not_found
    with NegativeCycle l -> l

  module Comp = MakeComp(G)

  let find_negative_cycle g =
    let rec iter = function
      | [] -> []
      | (x :: _) :: cl ->
        begin try find_negative_cycle_from g x with Not_found -> iter cl end
      | [] :: _ ->
        assert false (* a component is not empty *)
    in
    iter (Comp.scc_list g)
end

(** Pack *)

module Generic(G: I with type E.label = int) = struct
  include G

  module W = struct
    type edge = G.E.t
    type t = int
    let weight e = G.E.label e
    let zero = 0
    let add = (+)
    let sub = (-)
    let compare : t -> t -> int = Int.compare
  end

  module BF = BellmanFord(G)(W)
  let bellman_ford = BF.find_negative_cycle
end

module Int = struct
  type t = Int.t
  let compare = Int.compare
  let default = 0
end

module Make(V: COMPARABLE) = Generic(Digraph.ConcreteBidirectionalLabeled(V)(Int))
