(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

type t = {
  system  : States.state;        (* summary + libstack *)
  proof   : Proof_global.t;      (* proof state *)
  shallow : bool                 (* is the state trimmed down (libstack) *)
}

let s_cache = ref (States.freeze ~marshallable:`No)
let s_proof = ref (Proof_global.freeze ~marshallable:`No)

let invalidate_cache () =
  s_cache := Obj.magic 0;
  s_proof := Obj.magic 0

let freeze_interp_state marshallable =
  { system = (s_cache := States.freeze ~marshallable; !s_cache);
    proof  = (s_proof := Proof_global.freeze ~marshallable; !s_proof);
    shallow = marshallable = `Shallow }

let unfreeze_interp_state { system; proof } =
  if (!s_cache != system) then (s_cache := system; States.unfreeze system);
  if (!s_proof != proof)  then (s_proof := proof;  Proof_global.unfreeze proof)
