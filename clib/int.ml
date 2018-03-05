(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type t = int

external equal : int -> int -> bool = "%eq"

external compare : int -> int -> int = "caml_int_compare"

let hash i = i land 0x3FFFFFFF

module Self =
struct
  type t = int
  let compare = compare
end

module Set = Set.Make(Self)
module Map =
struct
  include CMap.Make(Self)

  type 'a map = 'a CMap.Make(Self).t

  type 'a _map =
  | MEmpty
  | MNode of 'a map * int * 'a * 'a map * int

  let map_prj : 'a map -> 'a _map = Obj.magic

  let rec find i s = match map_prj s with
  | MEmpty -> raise Not_found
  | MNode (l, k, v, r, h) ->
    if i < k then find i l
    else if i = k then v
    else find i r
end

module List = struct
  let mem = List.memq
  let assoc = List.assq
  let mem_assoc = List.mem_assq
  let remove_assoc = List.remove_assq
end

let min (i : int) j = if i < j then i else j

(** Utility function *)
let rec next from upto =
  if from < upto then next (2 * from + 1) upto
  else from


module PArray =
struct

  type 'a t = 'a data ref
  and 'a data =
  | Root of 'a option array
  | DSet of int * 'a option * 'a t

  let empty n = ref (Root (Array.make n None))

  let rec rerootk t k = match !t with
  | Root _ -> k ()
  | DSet (i, v, t') ->
    let next () = match !t' with
    | Root a as n ->
      let v' = Array.unsafe_get a i in
      let () = Array.unsafe_set a i v in
      let () = t := n in
      let () = t' := DSet (i, v', t) in
      k ()
    | DSet _ -> assert false
    in
    rerootk t' next

  let reroot t = rerootk t (fun () -> ())

  let get t i =
  let () = assert (0 <= i) in
  match !t with
  | Root a ->
    if Array.length a <= i then None
    else Array.unsafe_get a i
  | DSet _ ->
    let () = reroot t in
    match !t with
    | Root a ->
      if Array.length a <= i then None
      else Array.unsafe_get a i
    | DSet _ -> assert false

  let set t i v =
    let () = assert (0 <= i) in
    let () = reroot t in
    match !t with
    | DSet _ -> assert false
    | Root a as n ->
      let len = Array.length a in
      if i < len then
        let old = Array.unsafe_get a i in
        if old == v then t
        else
          let () = Array.unsafe_set a i v in
          let res = ref n in
          let () = t := DSet (i, old, res) in
          res
      else match v with
      | None -> t (** Nothing to do! *)
      | Some _ -> (** we must resize *)
        let nlen = next len (succ i) in
        let nlen = min nlen Sys.max_array_length in
        let () = assert (i < nlen) in
        let a' = Array.make nlen None in
        let () = Array.blit a 0 a' 0 len in
        let () = Array.unsafe_set a' i v in
        let res = ref (Root a') in
        let () = t := DSet (i, None, res) in
        res

end

module PMap =
struct

  type key = int

  (** Invariants:

    1. an empty map is always [Empty].
    2. the set of the [Map] constructor remembers the present keys.
  *)
  type 'a t = Empty | Map of Set.t * 'a PArray.t

  let empty = Empty

  let is_empty = function
  | Empty -> true
  | Map _ -> false

  let singleton k x =
    let len = next 19 (k + 1) in
    let len = min Sys.max_array_length len in
    let v = PArray.empty len in
    let v = PArray.set v k (Some x) in
    let s = Set.singleton k in
    Map (s, v)

  let add k x = function
  | Empty -> singleton k x
  | Map (s, v) ->
    let s = match PArray.get v k with
    | None -> Set.add k s
    | Some _ -> s
    in
    let v = PArray.set v k (Some x) in
    Map (s, v)

  let remove k = function
  | Empty -> Empty
  | Map (s, v) ->
    let s = Set.remove k s in
    if Set.is_empty s then Empty
    else
      let v = PArray.set v k None in
      Map (s, v)

  let mem k = function
  | Empty -> false
  | Map (_, v) ->
    match PArray.get v k with
    | None -> false
    | Some _ -> true

  let find k = function
  | Empty -> raise Not_found
  | Map (_, v) ->
    match PArray.get v k with
    | None -> raise Not_found
    | Some x -> x

  let iter f = function
  | Empty -> ()
  | Map (s, v) ->
    let iter k = match PArray.get v k with
    | None -> ()
    | Some x -> f k x
    in
    Set.iter iter s

  let fold f m accu = match m with
  | Empty -> accu
  | Map (s, v) ->
    let fold k accu = match PArray.get v k with
    | None -> accu
    | Some x -> f k x accu
    in
    Set.fold fold s accu

  let exists f m = match m with
  | Empty -> false
  | Map (s, v) ->
    let exists k = match PArray.get v k with
    | None -> false
    | Some x -> f k x
    in
    Set.exists exists s

  let for_all f m = match m with
  | Empty -> true
  | Map (s, v) ->
    let for_all k = match PArray.get v k with
    | None -> true
    | Some x -> f k x
    in
    Set.for_all for_all s

  let cast = function
  | Empty -> Map.empty
  | Map (s, v) ->
    let bind k = match PArray.get v k with
    | None -> assert false
    | Some x -> x
    in
    Map.bind bind s

  let domain = function
  | Empty -> Set.empty
  | Map (s, _) -> s

end
