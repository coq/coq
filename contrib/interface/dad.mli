open Proof_type;;
open Tacmach;;


val dad_rule_names : unit -> string list;;
val start_dad : unit -> unit;;
val dad_tac : (Coqast.t -> 'a) -> tactic_arg list -> goal sigma ->
                  goal list sigma * validation;;
val add_dad_rule : string -> Coqast.t -> (int list) -> (int list) ->
                   int -> (int list) -> Coqast.t -> unit;;
