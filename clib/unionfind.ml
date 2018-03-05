(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** An imperative implementation of partitions via Union-Find *)

(** Paths are compressed imperatively at each lookup of a
    canonical representative. Each union also modifies in-place
    the partition structure.

    Nota: For the moment we use Pervasive's comparison for
    choosing the smallest object as representative. This could
    be made more generic.
*)



module type PartitionSig = sig

  (** The type of elements in the partition *)
  type elt

  (** A set structure over elements *)
  type set

  (** The type of partitions *)
  type t

  (** Initialise an empty partition *)
  val create : unit -> t

  (** Add (in place) an element in the partition, or do nothing
      if the element is already in the partition. *)
  val add : elt -> t -> unit

  (** Find the canonical representative of an element.
      Raise [not_found] if the element isn't known yet. *)
  val find : elt -> t -> elt

  (** Merge (in place) the equivalence classes of two elements.
      This will add the elements in the partition if necessary. *)
  val union : elt -> elt -> t -> unit

  (** Merge (in place) the equivalence classes of many elements. *)
  val union_set : set -> t -> unit

  (** Listing the different components of the partition *)
  val partition : t -> set list

end

module type SetS =
sig
  type t
  type elt
  val singleton : elt -> t
  val union : t -> t -> t
  val choose : t -> elt
  val iter : (elt -> unit) -> t -> unit
end

module type MapS =
sig
  type key
  type +'a t
  val empty : 'a t
  val find : key -> 'a t -> 'a
  val add : key -> 'a -> 'a t -> 'a t
  val mem : key -> 'a t -> bool
  val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
end

module Make (S:SetS)(M:MapS with type key = S.elt) = struct

  type elt = S.elt
  type set = S.t

  type node =
    | Canon of set
    | Equiv of elt

  type t = node ref M.t ref

  let create () = ref (M.empty : node ref M.t)

  let fresh x p =
    let node = ref (Canon (S.singleton x)) in
    p := M.add x node !p;
    x, node

  let rec lookup x p =
    let node = M.find x !p in
    match !node with
      | Canon _ -> x, node
      | Equiv y ->
	let ((z,_) as res) = lookup y p in
	if not (z == y) then node := Equiv z;
	res

  let add x p = if not (M.mem x !p) then ignore (fresh x p)

  let find x p = fst (lookup x p)

  let canonical x p = try lookup x p with Not_found -> fresh x p

  let union x y p =
    let ((x,_) as xcan) = canonical x p in
    let ((y,_) as ycan) = canonical y p in
    if x = y then ()
    else
      let xcan, ycan = if x < y then xcan, ycan else ycan, xcan in
      let x,xnode = xcan and y,ynode = ycan in
      match !xnode, !ynode with
	| Canon lx, Canon ly ->
	  xnode := Canon (S.union lx ly);
	  ynode := Equiv x;
	| _ -> assert false

  let union_set s p =
    try
      let x = S.choose s in
      S.iter (fun y -> union x y p) s
    with Not_found -> ()

  let partition p =
    List.rev (M.fold
		(fun x node acc -> match !node with
		  | Equiv _ -> acc
		  | Canon lx -> lx::acc)
		!p [])

end
