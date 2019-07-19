open Vernacexpr

(** Special Fixpoint handling when command is activated. *)

val do_fixpoint :
  (* When [false], assume guarded. *)
  scope:DeclareDef.locality -> poly:bool -> fixpoint_expr list -> unit

val do_cofixpoint :
  (* When [false], assume guarded. *)
  scope:DeclareDef.locality -> poly:bool -> cofixpoint_expr list -> unit
