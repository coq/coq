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
  type t
  val compare : t -> t -> int
end

module Pair (M:S) (N:S) = struct
  type t = M.t * N.t

  let compare (a,b) (a',b') =
    let i = M.compare a a' in
    if Int.equal i 0 then N.compare b b'
    else i
end

module UnorderedPair (M:S) = struct
  type t = M.t * M.t

  let reorder (a,b as p) =
    if M.compare a b <= 0 then p else (b,a)

  let compare p p' =
    let p = reorder p and p' = reorder p' in
    let module P = Pair(M)(M) in P.compare p p'
end
