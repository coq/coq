(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

module Arg =
struct
  module DYN = Dyn.Make()
  module Map = DYN.Map
  type ('a, 'b) tag = ('a * 'b) DYN.tag
  let eq = DYN.eq
  let repr = DYN.repr
  let create = DYN.create
  type glb = Glb : (_,'a) tag * 'a  -> glb
end

module type Param = sig type ('raw, 'glb) t end

module ArgMap (M : Param) =
struct
  type _ pack = Pack : ('raw, 'glb) M.t -> ('raw * 'glb) pack
  include Arg.Map(struct type 'a t = 'a pack end)
end

module Val = Dyn.Make()
