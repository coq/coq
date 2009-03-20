
open Libnames
open Proof_type

val simplify : tactic
val ergo : tactic
val yices : tactic
val cvc_lite : tactic
val harvey : tactic
val zenon : tactic
val gwhy : tactic

val dp_hint : reference list -> unit
val dp_timeout : int -> unit
val dp_debug : bool -> unit
val dp_trace : bool -> unit
val dp_prelude : string list -> unit
val dp_predefined : reference -> string -> unit


