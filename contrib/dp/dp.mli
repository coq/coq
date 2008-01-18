
open Libnames

(* arnaud: trucs factices *)
type tactic = Tacticals.tactic
(* arnaud: /trucs factices *)

val simplify : tactic
val ergo : tactic
val yices : tactic
val cvc_lite : tactic
val harvey : tactic
val zenon : tactic
val gwhy : tactic

val dp_hint : reference list -> unit
val set_timeout : int -> unit
val set_debug : bool -> unit
val set_trace : bool -> unit


