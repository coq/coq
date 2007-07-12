open Util

type obligation_info = (Names.identifier * Term.types * bool * Intset.t) array
    (* ident, type, opaque or transparent, dependencies *)

val set_default_tactic : Tacexpr.glob_tactic_expr -> unit
val default_tactic : unit -> Proof_type.tactic

val add_definition : Names.identifier ->  Term.constr -> Term.types -> 
  obligation_info -> unit

val add_mutual_definitions : 
  (Names.identifier * Term.constr * Term.types * obligation_info) list -> int array -> unit

val subtac_obligation : int * Names.identifier option * Topconstr.constr_expr option -> unit

val next_obligation : Names.identifier option -> unit

val solve_obligations : Names.identifier option -> Proof_type.tactic -> int 
(* Number of remaining obligations to be solved for this program *)

val solve_all_obligations : Proof_type.tactic -> unit 

val try_solve_obligation : int -> Names.identifier option -> Proof_type.tactic -> unit

val try_solve_obligations : Names.identifier option -> Proof_type.tactic -> unit

val show_obligations : Names.identifier option -> unit

val admit_obligations : Names.identifier option -> unit

exception NoObligations of Names.identifier option

val explain_no_obligations : Names.identifier option -> Pp.std_ppcmds

