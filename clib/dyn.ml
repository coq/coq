(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

module type TParam =
sig
  type 'a t
end

module type MapS =
sig
  type t
  type 'a obj
  type 'a key
  val empty : t
  val add : 'a key -> 'a obj -> t -> t
  val remove : 'a key -> t -> t
  val find : 'a key -> t -> 'a obj
  val mem : 'a key -> t -> bool

  type any = Any : 'a key * 'a obj -> any

  type map = { map : 'a. 'a key -> 'a obj -> 'a obj }
  val map : map -> t -> t

  val iter : (any -> unit) -> t -> unit
  val fold : (any -> 'r -> 'r) -> t -> 'r -> 'r
end

module type PreS =
sig
type 'a tag
type t = Dyn : 'a tag * 'a -> t

val create : string -> 'a tag
val eq : 'a tag -> 'b tag -> ('a, 'b) CSig.eq option
val repr : 'a tag -> string

type any = Any : 'a tag -> any

val name : string -> any option

module Map(M : TParam) : MapS with type 'a obj = 'a M.t with type 'a key = 'a tag

val dump : unit -> (int * string) list

end

module type S =
sig
  include PreS

  module Easy : sig

    val make_dyn_tag : string -> ('a -> t) * (t -> 'a) * 'a tag
    val make_dyn : string -> ('a -> t) * (t -> 'a)
    val inj : 'a -> 'a tag -> t
    val prj : t -> 'a tag -> 'a option
  end

end

module Make () = struct
module Self : PreS = struct
(* Dynamics, programmed with DANGER !!! *)

type 'a tag = int

type t = Dyn : 'a tag * 'a -> t

type any = Any : 'a tag -> any

let dyntab = ref (Int.Map.empty : string Int.Map.t)
(** Instead of working with tags as strings, which are costly, we use their
    hash. We ensure unicity of the hash in the [create] function. If ever a
    collision occurs, which is unlikely, it is sufficient to tweak the offending
    dynamic tag. *)

let create (s : string) =
  let hash = Hashtbl.hash s in
  let () =
    if Int.Map.mem hash !dyntab then
      let old = Int.Map.find hash !dyntab in
      let () = Printf.eprintf "Dynamic tag collision: %s vs. %s\n%!" s old in
      assert false
  in
  let () = dyntab := Int.Map.add hash s !dyntab in
  hash

let eq : 'a 'b. 'a tag -> 'b tag -> ('a, 'b) CSig.eq option =
  fun h1 h2 -> if Int.equal h1 h2 then Some (Obj.magic CSig.Refl) else None

let repr s =
  try Int.Map.find s !dyntab
  with Not_found ->
    let () = Printf.eprintf "Unknown dynamic tag %i\n%!" s in
    assert false

let name s =
  let hash = Hashtbl.hash s in
  if Int.Map.mem hash !dyntab then Some (Any hash) else None

let dump () = Int.Map.bindings !dyntab

module Map(M : TParam) =
struct
type t = Obj.t M.t Int.Map.t
type 'a obj = 'a M.t
type 'a key = 'a tag
let cast : 'a M.t -> 'b M.t = Obj.magic
let empty = Int.Map.empty
let add tag v m = Int.Map.add tag (cast v) m
let remove tag m = Int.Map.remove tag m
let find tag m = cast (Int.Map.find tag m)
let mem = Int.Map.mem

type any = Any : 'a tag * 'a M.t -> any

type map = { map : 'a. 'a tag -> 'a M.t -> 'a M.t }
let map f m = Int.Map.mapi f.map m

let iter f m = Int.Map.iter (fun k v -> f (Any (k, v))) m
let fold f m accu = Int.Map.fold (fun k v accu -> f (Any (k, v)) accu) m accu
end

end
include Self

module Easy = struct

(* now tags are opaque, we can do the trick *)
let make_dyn_tag (s : string) =
 (fun (type a) (tag : a tag) ->
  let infun : (a -> t) = fun x -> Dyn (tag, x) in
  let outfun : (t -> a) = fun (Dyn (t, x)) ->
    match eq tag t with
    | None -> assert false
    | Some CSig.Refl -> x
  in
  infun, outfun, tag)
 (create s)

let make_dyn (s : string) =
  let inf, outf, _ = make_dyn_tag s in inf, outf

let inj x tag = Dyn(tag,x)
let prj : type a. t -> a tag -> a option =
    fun (Dyn(tag',x)) tag ->
    match eq tag tag' with
    | None -> None
    | Some CSig.Refl -> Some x
end

end

