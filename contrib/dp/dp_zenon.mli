
open Fol

(* arnaud: trucs factices *)
  module Proof_type :
    sig
      type tactic = Tacticals.tactic
    end
(* arnaud: /trucs factices *)

val set_debug : bool -> unit

val proof_from_file : string -> Proof_type.tactic

