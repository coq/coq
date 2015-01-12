(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Genarg

module TacStore = Store.Make(struct end)

type interp_sign = {
  lfun : tlevel generic_argument Id.Map.t;
  extra : TacStore.t }

type ('glb, 'top) interp_fun = interp_sign ->
    Goal.goal Evd.sigma -> 'glb -> Evd.evar_map * 'top

module InterpObj =
struct
  type ('raw, 'glb, 'top) obj = ('glb, 'top) interp_fun
  let name = "interp"
  let default _ = None
end

module Interp = Register(InterpObj)

let interp = Interp.obj
let register_interp0 = Interp.register0

let generic_interp ist gl v =
  let unpacker wit v =
    let (sigma, ans) = interp wit ist gl (glb v) in
    (sigma, in_gen (topwit wit) ans)
  in
  unpack { unpacker; } v
