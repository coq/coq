open Names
open Util
open Libnames

type obligation_info = (Names.identifier * Term.types * loc * bool * Intset.t) array
    (* ident, type, location, opaque or transparent, dependencies *)

type progress = (* Resolution status of a program *)
    | Remain of int  (* n obligations remaining *)
    | Dependent (* Dependent on other definitions *)
    | Defined of global_reference (* Defined as id *)
	
val set_default_tactic : Tacexpr.glob_tactic_expr -> unit
val default_tactic : unit -> Proof_type.tactic

val set_proofs_transparency : bool -> unit (* true = All transparent, false = Opaque if possible *)
val get_proofs_transparency : unit -> bool

type definition_hook = global_reference -> unit

val add_definition : Names.identifier ->  Term.constr -> Term.types -> 
  ?implicits:(Topconstr.explicitation * (bool * bool)) list ->
  ?kind:Decl_kinds.definition_kind ->
  ?hook:definition_hook -> obligation_info -> progress

type notations = (string * Topconstr.constr_expr * Topconstr.scope_name option) list

val add_mutual_definitions : 
  (Names.identifier * Term.constr * Term.types *
      (Topconstr.explicitation * (bool * bool)) list * obligation_info) list -> 
  ?kind:Decl_kinds.definition_kind ->
  notations ->
  Command.fixpoint_kind -> unit

val subtac_obligation : int * Names.identifier option * Topconstr.constr_expr option -> unit

val next_obligation : Names.identifier option -> unit

val solve_obligations : Names.identifier option -> Proof_type.tactic -> progress
(* Number of remaining obligations to be solved for this program *)

val solve_all_obligations : Proof_type.tactic -> unit 

val try_solve_obligation : int -> Names.identifier option -> Proof_type.tactic -> unit

val try_solve_obligations : Names.identifier option -> Proof_type.tactic -> unit

val show_obligations : ?msg:bool -> Names.identifier option -> unit

val show_term : Names.identifier option -> unit

val admit_obligations : Names.identifier option -> unit

exception NoObligations of Names.identifier option

val explain_no_obligations : Names.identifier option -> Pp.std_ppcmds

