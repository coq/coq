(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

module type S =
sig
  type label
  type data
  type t
  val empty : t
  val get : t -> data
  val next : t -> label -> t
  val labels : t -> label list
  val add : label list -> data -> t -> t
  val remove : label list -> data -> t -> t
  val iter : (label list -> data -> unit) -> t -> unit
end

module type Grp =
sig
  type t
  val nil : t
  val is_nil : t -> bool
  val add : t -> t -> t
  val sub : t -> t -> t
end

module Make (Y : Map.OrderedType) (X : Grp) =
struct

module T_codom = Map.Make(Y)

type data = X.t
type label = Y.t
type t = Node of X.t * t T_codom.t

let codom_for_all f m =
  let fold key v accu = f v && accu in
  T_codom.fold fold m true

let empty = Node (X.nil, T_codom.empty)

let next (Node (_,m)) lbl = T_codom.find lbl m

let get (Node (hereset,_)) = hereset

let labels (Node (_,m)) =
  (** FIXME: this is order-dependent. Try to find a more robust presentation? *)
  List.rev (T_codom.fold (fun x _ acc -> x::acc) m [])

let is_empty_node (Node(a,b)) = (X.is_nil a) && (T_codom.is_empty b)

let assure_arc m lbl =
  if T_codom.mem lbl m then
    m
  else
    T_codom.add lbl (Node (X.nil,T_codom.empty)) m

let cleanse_arcs (Node (hereset,m)) =
  let m = if codom_for_all is_empty_node m then T_codom.empty else m in
  Node(hereset, m)

let rec at_path f (Node (hereset,m)) = function
  | [] ->
      cleanse_arcs (Node(f hereset,m))
  | h::t ->
      let m = assure_arc m h in
      cleanse_arcs (Node(hereset,
                         T_codom.add h (at_path f (T_codom.find h m) t) m))

let add path v tm =
  at_path (fun hereset -> X.add v hereset) tm path

let remove path v tm =
  at_path (fun hereset -> X.sub hereset v) tm path

let iter f tlm =
  let rec apprec pfx (Node(hereset,m)) =
    let path = List.rev pfx in
    f path hereset;
    T_codom.iter (fun l tm -> apprec (l::pfx) tm) m
  in
  apprec [] tlm

end
