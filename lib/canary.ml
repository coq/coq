(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

type t = Obj.t

let obj = Obj.new_block Obj.closure_tag 0
  (** This is an empty closure block. In the current implementation, it is
      sufficient to allow marshalling but forbid equality. Sadly still allows
      hash. *)
  (** FIXME : use custom blocks somehow. *)

module type Obj = sig type t end

module Make(M : Obj) =
struct
  type canary = t
  type t = (canary * M.t)

  let prj (_, x) = x
  let inj x = (obj, x)
end
