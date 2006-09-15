type result =
    Okay
  | Wrong_num_gg of Proof_type.goal list
  | Tac_failure of exn
  | Cancelled

type info = {
    goal_num : int;
    num_gg : int;
    cool : Proof_type.tactic;
    mutable res : result
}

(* Raised when a tactic created in the new proof a different
   number of goals than in the old one.
   old number * new number *)
exception Tactic_diverged of int * int

val reset : unit -> unit

val get_new_num : int -> int

val discarding : int -> int -> unit

val keeping : int -> int -> unit

val is_discarded : int -> bool
