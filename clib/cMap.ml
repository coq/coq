(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

module type OrderedType =
sig
  type t
  val compare : t -> t -> int
end

module type MonadS =
sig
  type +'a t
  val return : 'a -> 'a t
  val (>>=) : 'a t -> ('a -> 'b t) -> 'b t
end

module type S = Map.S

module type ExtS =
sig
  include CSig.MapS
  module Set : CSig.SetS with type elt = key
  val get : key -> 'a t -> 'a
  val set : key -> 'a -> 'a t -> 'a t
  val modify : key -> (key -> 'a -> 'a) -> 'a t -> 'a t
  val domain : 'a t -> Set.t
  val bind : (key -> 'a) -> Set.t -> 'a t
  val fold_left : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
  val fold_right : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
  val height : 'a t -> int
  val filter_range : (key -> int) -> 'a t -> 'a t
  val update: key -> ('a option -> 'a option) -> 'a t -> 'a t
  module Smart :
  sig
    val map : ('a -> 'a) -> 'a t -> 'a t
    val mapi : (key -> 'a -> 'a) -> 'a t -> 'a t
  end
  module Unsafe :
  sig
    val map : (key -> 'a -> key * 'b) -> 'a t -> 'b t
  end
  module Monad(M : MonadS) :
  sig
    val fold : (key -> 'a -> 'b -> 'b M.t) -> 'a t -> 'b -> 'b M.t
    val fold_left : (key -> 'a -> 'b -> 'b M.t) -> 'a t -> 'b -> 'b M.t
    val fold_right : (key -> 'a -> 'b -> 'b M.t) -> 'a t -> 'b -> 'b M.t
  end
end

module MapExt (M : Map.OrderedType) :
sig
  type 'a map = 'a Map.Make(M).t
  val set : M.t -> 'a -> 'a map -> 'a map
  val modify : M.t -> (M.t -> 'a -> 'a) -> 'a map -> 'a map
  val domain : 'a map -> Set.Make(M).t
  val bind : (M.t -> 'a) -> Set.Make(M).t -> 'a map
  val fold_left : (M.t -> 'a -> 'b -> 'b) -> 'a map -> 'b -> 'b
  val fold_right : (M.t -> 'a -> 'b -> 'b) -> 'a map -> 'b -> 'b
  val height : 'a map -> int
  val filter_range : (M.t -> int) -> 'a map -> 'a map
  val update: M.t -> ('a option -> 'a option) -> 'a map -> 'a map
  module Smart :
  sig
    val map : ('a -> 'a) -> 'a map -> 'a map
    val mapi : (M.t -> 'a -> 'a) -> 'a map -> 'a map
  end
  module Unsafe :
  sig
    val map : (M.t -> 'a -> M.t * 'b) -> 'a map -> 'b map
  end
  module Monad(MS : MonadS) :
  sig
    val fold : (M.t -> 'a -> 'b -> 'b MS.t) -> 'a map -> 'b -> 'b MS.t
    val fold_left : (M.t -> 'a -> 'b -> 'b MS.t) -> 'a map -> 'b -> 'b MS.t
    val fold_right : (M.t -> 'a -> 'b -> 'b MS.t) -> 'a map -> 'b -> 'b MS.t
  end
end =
struct
  (** This unsafe module is a way to access to the actual implementations of
      OCaml sets and maps without reimplementing them ourselves. It is quite
      dubious that these implementations will ever be changed... Nonetheless,
      if this happens, we can still implement a less clever version of [domain].
  *)

  module F = Map.Make(M)
  type 'a map = 'a F.t

  module S = Set.Make(M)
  type set = S.t

  type 'a _map =
    | MEmpty
    | MNode of {l:'a map; v:F.key; d:'a; r:'a map; h:int}

  type _set =
  | SEmpty
  | SNode of set * M.t * set * int

  let map_prj : 'a map -> 'a _map = Obj.magic
  let map_inj : 'a _map -> 'a map = Obj.magic
  let set_prj : set -> _set = Obj.magic
  let set_inj : _set -> set = Obj.magic

  let rec set k v (s : 'a map) : 'a map = match map_prj s with
  | MEmpty -> raise Not_found
  | MNode {l; v=k'; d=v'; r; h} ->
    let c = M.compare k k' in
    if c < 0 then
      let l' = set k v l in
      if l == l' then s
      else map_inj (MNode {l=l'; v=k'; d=v'; r; h})
    else if c = 0 then
      if v' == v then s
      else map_inj (MNode {l; v=k'; d=v; r; h})
    else
      let r' = set k v r in
      if r == r' then s
      else map_inj (MNode {l; v=k'; d=v'; r=r'; h})

  let rec modify k f (s : 'a map) : 'a map = match map_prj s with
  | MEmpty -> raise Not_found
  | MNode {l; v; d; r; h} ->
    let c = M.compare k v in
    if c < 0 then
      let l' = modify k f l in
      if l == l' then s
      else map_inj (MNode {l=l'; v; d; r; h})
    else if c = 0 then
      let d' = f v d in
      if d' == d then s
      else map_inj (MNode {l; v; d=d'; r; h})
    else
      let r' = modify k f r in
      if r == r' then s
      else map_inj (MNode {l; v; d; r=r'; h})

  let rec domain (s : 'a map) : set = match map_prj s with
  | MEmpty -> set_inj SEmpty
  | MNode {l; v; r; h; _} ->
    set_inj (SNode (domain l, v, domain r, h))
  (** This function is essentially identity, but OCaml current stdlib does not
      take advantage of the similarity of the two structures, so we introduce
      this unsafe loophole. *)

  let rec bind f (s : set) : 'a map = match set_prj s with
  | SEmpty -> map_inj MEmpty
  | SNode (l, k, r, h) ->
    map_inj (MNode { l=bind f l; v=k; d=f k; r=bind f r; h})
  (** Dual operation of [domain]. *)

  let rec fold_left f (s : 'a map) accu = match map_prj s with
  | MEmpty -> accu
  | MNode {l; v=k; d=v; r; h} ->
    let accu = f k v (fold_left f l accu) in
    fold_left f r accu

  let rec fold_right f (s : 'a map) accu = match map_prj s with
  | MEmpty -> accu
  | MNode {l; v=k; d=v; r; h} ->
    let accu = f k v (fold_right f r accu) in
    fold_right f l accu

  let height s = match map_prj s with
  | MEmpty -> 0
  | MNode {h;_} -> h

  (* Filter based on a range *)
  let filter_range in_range m =
    let rec aux m = function
      | MEmpty -> m
      | MNode {l; v; d; r; _} ->
        let vr = in_range v in
        (* the range is below the current value *)
        if vr < 0 then aux m (map_prj l)
        (* the range is above the current value *)
        else if vr > 0 then aux m (map_prj r)
        (* The current value is in the range *)
        else
          let m = aux m (map_prj l) in
          let m = aux m (map_prj r) in
          F.add v d m
    in aux F.empty (map_prj m)

  (* Imported from OCaml upstream until we can bump the version *)
  let create l x d r =
    let hl = height l and hr = height r in
    map_inj @@ MNode{l; v=x; d; r; h=(if hl >= hr then hl + 1 else hr + 1)}

  let bal l x d r =
    let hl = match map_prj l with MEmpty -> 0 | MNode {h} -> h in
    let hr = match map_prj r with MEmpty -> 0 | MNode {h} -> h in
    if hl > hr + 2 then begin
      match map_prj l with
      | MEmpty -> invalid_arg "Map.bal"
      | MNode{l=ll; v=lv; d=ld; r=lr} ->
        if height ll >= height lr then
          create ll lv ld (create lr x d r)
        else begin
          match map_prj lr with
          | MEmpty -> invalid_arg "Map.bal"
          | MNode{l=lrl; v=lrv; d=lrd; r=lrr}->
            create (create ll lv ld lrl) lrv lrd (create lrr x d r)
        end
    end else if hr > hl + 2 then begin
      match map_prj r with
      | MEmpty -> invalid_arg "Map.bal"
      | MNode{l=rl; v=rv; d=rd; r=rr} ->
        if height rr >= height rl then
          create (create l x d rl) rv rd rr
        else begin
          match map_prj rl with
          | MEmpty -> invalid_arg "Map.bal"
          | MNode{l=rll; v=rlv; d=rld; r=rlr} ->
            create (create l x d rll) rlv rld (create rlr rv rd rr)
        end
    end else
      map_inj @@ MNode{l; v=x; d; r; h=(if hl >= hr then hl + 1 else hr + 1)}

  let rec remove_min_binding m = match map_prj m with
    | MEmpty -> invalid_arg "Map.remove_min_elt"
    | MNode {l;v;d;r;_} ->
      match map_prj l with
      | MEmpty -> r
      | _ -> bal (remove_min_binding l) v d r

  let merge t1 t2 =
    match (map_prj t1, map_prj t2) with
      (MEmpty, t) -> map_inj t
    | (t, MEmpty) -> map_inj t
    | (_, _) ->
      let (x, d) = F.min_binding t2 in
      bal t1 x d (remove_min_binding t2)

  let rec update x f m = match map_prj m with
    | MEmpty ->
      begin match f None with
        | None -> map_inj MEmpty
        | Some data -> map_inj @@ MNode{l=map_inj MEmpty; v=x; d=data; r=map_inj MEmpty; h=1}
      end
    | MNode {l; v; d; r; h} as m ->
      let c = M.compare x v in
      if c = 0 then begin
        match f (Some d) with
        | None -> merge l r
        | Some data ->
          if d == data then map_inj m else
            map_inj @@ MNode{l; v=x; d=data; r; h}
      end else if c < 0 then
        let ll = update x f l in
        if l == ll then map_inj m else bal ll v d r
      else
        let rr = update x f r in
        if r == rr then map_inj m else bal l v d rr

  (* End of Imported OCaml *)

  module Smart =
  struct

    let rec map f (s : 'a map) = match map_prj s with
    | MEmpty -> map_inj MEmpty
    | MNode {l; v=k; d=v; r; h} ->
      let l' = map f l in
      let r' = map f r in
      let v' = f v in
      if l == l' && r == r' && v == v' then s
      else map_inj (MNode {l=l'; v=k; d=v'; r=r'; h})

    let rec mapi f (s : 'a map) = match map_prj s with
    | MEmpty -> map_inj MEmpty
    | MNode {l; v=k; d=v; r; h} ->
      let l' = mapi f l in
      let r' = mapi f r in
      let v' = f k v in
      if l == l' && r == r' && v == v' then s
      else map_inj (MNode {l=l'; v=k; d=v'; r=r'; h})

  end

  module Unsafe =
  struct

    let rec map f (s : 'a map) : 'b map = match map_prj s with
    | MEmpty -> map_inj MEmpty
    | MNode {l; v=k; d=v; r; h} ->
      let (k, v) = f k v in
      map_inj (MNode {l=map f l; v=k; d=v; r=map f r; h})

  end

  module Monad(M : MonadS) =
  struct

    open M

    let rec fold_left f s accu = match map_prj s with
    | MEmpty -> return accu
    | MNode {l; v=k; d=v; r; h} ->
      fold_left f l accu >>= fun accu ->
      f k v accu >>= fun accu ->
      fold_left f r accu

    let rec fold_right f s accu = match map_prj s with
    | MEmpty -> return accu
    | MNode {l; v=k; d=v; r; h} ->
      fold_right f r accu >>= fun accu ->
      f k v accu >>= fun accu ->
      fold_right f l accu

    let fold = fold_left

  end

end

module Make(M : Map.OrderedType) =
struct
  include Map.Make(M)
  include MapExt(M)
  let get k m = try find k m with Not_found -> assert false
end
