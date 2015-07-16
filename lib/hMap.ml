(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

module type HashedType =
sig
  type t
  val compare : t -> t -> int
  val hash : t -> int
end

module SetMake(M : HashedType) =
struct
  (** Hash Sets use hashes to prevent doing too many comparison tests. They
      associate to each hash the set of keys having that hash.

      Invariants:

      1. There is no empty set in the intmap.
      2. All values in the same set have the same hash, which is the int to
         which it is associated in the intmap.
  *)

  module Set = Set.Make(M)

  type elt = M.t

  type t = Set.t Int.Map.t

  let empty = Int.Map.empty

  let is_empty = Int.Map.is_empty

  let mem x s =
    let h = M.hash x in
    try
      let m = Int.Map.find h s in
      Set.mem x m
    with Not_found -> false

  let add x s =
    let h = M.hash x in
    try
      let m = Int.Map.find h s in
      let m = Set.add x m in
      Int.Map.update h m s
    with Not_found ->
      let m = Set.singleton x in
      Int.Map.add h m s

  let singleton x =
    let h = M.hash x in
    let m = Set.singleton x in
    Int.Map.singleton h m

  let remove x s =
    let h = M.hash x in
    try
      let m = Int.Map.find h s in
      let m = Set.remove x m in
      if Set.is_empty m then
        Int.Map.remove h s
      else
        Int.Map.update h m s
    with Not_found -> s

  let union s1 s2 =
    let fu _ m1 m2 = match m1, m2 with
    | None, None -> None
    | (Some _ as m), None | None, (Some _ as m) -> m
    | Some m1, Some m2 -> Some (Set.union m1 m2)
    in
    Int.Map.merge fu s1 s2

  let inter s1 s2 =
    let fu _ m1 m2 = match m1, m2 with
    | None, None -> None
    | Some _, None | None, Some _ -> None
    | Some m1, Some m2 ->
      let m = Set.inter m1 m2 in
      if Set.is_empty m then None else Some m
    in
    Int.Map.merge fu s1 s2

  let diff s1 s2 =
    let fu _ m1 m2 = match m1, m2 with
    | None, None -> None
    | (Some _ as m), None -> m
    | None, Some _ -> None
    | Some m1, Some m2 ->
      let m = Set.diff m1 m2 in
      if Set.is_empty m then None else Some m
    in
    Int.Map.merge fu s1 s2

  let compare s1 s2 = Int.Map.compare Set.compare s1 s2

  let equal s1 s2 = Int.Map.equal Set.equal s1 s2

  let subset s1 s2 =
    let check h m1 =
      let m2 = try Int.Map.find h s2 with Not_found -> Set.empty in
      Set.subset m1 m2
    in
    Int.Map.for_all check s1

  let iter f s =
    let fi _ m = Set.iter f m in
    Int.Map.iter fi s

  let fold f s accu =
    let ff _ m accu = Set.fold f m accu in
    Int.Map.fold ff s accu

  let for_all f s =
    let ff _ m = Set.for_all f m in
    Int.Map.for_all ff s

  let exists f s =
    let fe _ m = Set.exists f m in
    Int.Map.exists fe s

  let filter f s =
    let ff m = Set.filter f m in
    let s = Int.Map.map ff s in
    Int.Map.filter (fun _ m -> not (Set.is_empty m)) s

  let partition f s =
    let fold h m (sl, sr) =
      let (ml, mr) = Set.partition f m in
      let sl = if Set.is_empty ml then sl else Int.Map.add h ml sl in
      let sr = if Set.is_empty mr then sr else Int.Map.add h mr sr in
      (sl, sr)
    in
    Int.Map.fold fold s (Int.Map.empty, Int.Map.empty)

  let cardinal s =
    let fold _ m accu = accu + Set.cardinal m in
    Int.Map.fold fold s 0

  let elements s =
    let fold _ m accu = Set.fold (fun x accu -> x :: accu) m accu in
    Int.Map.fold fold s []

  let min_elt _ = assert false (** Cannot be implemented efficiently *)

  let max_elt _ = assert false (** Cannot be implemented efficiently *)

  let choose s =
    let (_, m) = Int.Map.choose s in
    Set.choose m

  let split s x = assert false (** Cannot be implemented efficiently *)

end

module Make(M : HashedType) =
struct
  (** This module is essentially the same as SetMake, except that we have maps
      instead of sets in the intmap. Invariants are the same. *)
  module Set = SetMake(M)
  module Map = CMap.Make(M)

  type key = M.t

  type 'a t = 'a Map.t Int.Map.t

  let empty = Int.Map.empty

  let is_empty = Int.Map.is_empty

  let mem k s =
    let h = M.hash k in
    try
      let m = Int.Map.find h s in
      Map.mem k m
    with Not_found -> false

  let add k x s =
    let h = M.hash k in
    try
      let m = Int.Map.find h s in
      let m = Map.add k x m in
      Int.Map.update h m s
    with Not_found ->
      let m = Map.singleton k x in
      Int.Map.add h m s

  let singleton k x =
    let h = M.hash k in
    Int.Map.singleton h (Map.singleton k x)

  let remove k s =
    let h = M.hash k in
    try
      let m = Int.Map.find h s in
      let m = Map.remove k m in
      if Map.is_empty m then
        Int.Map.remove h s
      else
        Int.Map.update h m s
    with Not_found -> s

  let merge f s1 s2 =
    let fm h m1 m2 = match m1, m2 with
    | None, None -> None
    | Some m, None ->
      let m = Map.merge f m Map.empty in
      if Map.is_empty m then None
      else Some m
    | None, Some m ->
      let m = Map.merge f Map.empty m in
      if Map.is_empty m then None
      else Some m
    | Some m1, Some m2 ->
      let m = Map.merge f m1 m2 in
      if Map.is_empty m then None
      else Some m
    in
    Int.Map.merge fm s1 s2

  let compare f s1 s2 =
    let fc m1 m2 = Map.compare f m1 m2 in
    Int.Map.compare fc s1 s2

  let equal f s1 s2 =
    let fe m1 m2 = Map.equal f m1 m2 in
    Int.Map.equal fe s1 s2

  let iter f s =
    let fi _ m = Map.iter f m in
    Int.Map.iter fi s

  let fold f s accu =
    let ff _ m accu = Map.fold f m accu in
    Int.Map.fold ff s accu

  let for_all f s =
    let ff _ m = Map.for_all f m in
    Int.Map.for_all ff s

  let exists f s =
    let fe _ m = Map.exists f m in
    Int.Map.exists fe s

  let filter f s =
    let ff m = Map.filter f m in
    let s = Int.Map.map ff s in
    Int.Map.filter (fun _ m -> not (Map.is_empty m)) s

  let partition f s =
    let fold h m (sl, sr) =
      let (ml, mr) = Map.partition f m in
      let sl = if Map.is_empty ml then sl else Int.Map.add h ml sl in
      let sr = if Map.is_empty mr then sr else Int.Map.add h mr sr in
      (sl, sr)
    in
    Int.Map.fold fold s (Int.Map.empty, Int.Map.empty)

  let cardinal s =
    let fold _ m accu = accu + Map.cardinal m in
    Int.Map.fold fold s 0

  let bindings s =
    let fold _ m accu = Map.fold (fun k x accu -> (k, x) :: accu) m accu in
    Int.Map.fold fold s []

  let min_binding _ = assert false (** Cannot be implemented efficiently *)

  let max_binding _ = assert false (** Cannot be implemented efficiently *)

  let fold_left _ _ _ = assert false (** Cannot be implemented efficiently *)

  let fold_right _ _ _ = assert false (** Cannot be implemented efficiently *)

  let choose s =
    let (_, m) = Int.Map.choose s in
    Map.choose m

  let find k s =
    let h = M.hash k in
    let m = Int.Map.find h s in
    Map.find k m

  let split k s = assert false (** Cannot be implemented efficiently *)

  let map f s =
    let fs m = Map.map f m in
    Int.Map.map fs s

  let mapi f s =
    let fs m = Map.mapi f m in
    Int.Map.map fs s

  let modify k f s =
    let h = M.hash k in
    let m = Int.Map.find h s in
    let m = Map.modify k f m in
    Int.Map.update h m s

  let bind f s =
    let fb m = Map.bind f m in
    Int.Map.map fb s

  let domain s = Int.Map.map Map.domain s

  let update k x s =
    let h = M.hash k in
    let m = Int.Map.find h s in
    let m = Map.update k x m in
    Int.Map.update h m s

  let smartmap f s =
    let fs m = Map.smartmap f m in
    Int.Map.smartmap fs s

  let smartmapi f s =
    let fs m = Map.smartmapi f m in
    Int.Map.smartmap fs s

  module Unsafe =
  struct
    let map f s =
      let fs m = Map.Unsafe.map f m in
      Int.Map.map fs s
  end

  module Monad(M : CMap.MonadS) =
  struct
    module IntM = Int.Map.Monad(M)
    module ExtM = Map.Monad(M)
    open M

    let fold f s accu =
      let ff _ m accu = ExtM.fold f m accu in
      IntM.fold ff s accu

    let fold_left _ _ _ = assert false
    let fold_right _ _ _ = assert false
  end

end
