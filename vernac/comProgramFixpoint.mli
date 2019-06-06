open Decl_kinds
open Vernacexpr

(** Special Fixpoint handling when command is activated. *)

val do_fixpoint :
  (* When [false], assume guarded. *)
  scope:locality -> poly:bool -> (fixpoint_expr * decl_notation list) list -> unit

val do_cofixpoint :
  (* When [false], assume guarded. *)
  scope:locality -> poly:bool -> (cofixpoint_expr * decl_notation list) list -> unit
