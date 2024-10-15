(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

module type ValueS =
sig
  type 'a t
end

module type Tag = sig type _ tag = .. end

module Make (Tag:Tag) = struct
  open Tag

  module type OneTag = sig
    type a
    type _ tag += T : a tag
  end
  type 'a onetag = (module OneTag with type a = 'a)

  let refl = Some CSig.Refl

  let eq_onetag (type a b) (tag:a onetag) (tag':b tag) : (a,b) CSig.eq option =
    let module T = (val tag) in
    match tag' with
    | T.T -> refl
    | _ -> None

  let make (type a) () : a onetag =
    (module struct type nonrec a = a type _ tag += T : a tag end)

  let tag_of_onetag (type a) (tag:a onetag) : a tag =
    let module T = (val tag) in
    T.T

  module type MapS = sig
    type t
    type _ value

    val empty : t

    val find : 'a tag -> t -> 'a value

    val add : 'a onetag -> 'a value -> t -> t

    val mem : 'a tag -> t -> bool

    val modify : 'a tag -> ('a value -> 'a value) -> t -> t

  end

  module Map (V:ValueS) = struct

    type v = V : 'a onetag * 'a V.t -> v

    let key t = Obj.Extension_constructor.(id (of_val t))
    let onekey t = key (tag_of_onetag t)

    module M = Int.Map
    type t = v M.t

    let empty = M.empty

    let find (type a) (tag:a tag) m : a V.t =
      let V (tag', v) = M.find (key tag) m in
      let module T = (val tag') in
      match tag with
      | T.T -> v
      | _ -> assert false

    let add tag v m = M.add (onekey tag) (V (tag, v)) m

    let mem tag m = M.mem (key tag) m

    let modify (type a) (tag:a tag) (f:a V.t -> a V.t) m =
      M.modify (key tag) (fun _ (V (tag', v)) ->
          let module T = (val tag') in
          match tag with
          | T.T -> V (tag', f v)
          | _ -> assert false) m

  end
end
