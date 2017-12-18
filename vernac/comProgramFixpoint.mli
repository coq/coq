open Decl_kinds
open Vernacexpr

(** Special Fixpoint handling when command is activated. *)

val do_fixpoint :
  (* When [false], assume guarded. *)
  locality -> polymorphic -> (fixpoint_expr * decl_notation list) list -> unit

val do_cofixpoint :
  (* When [false], assume guarded. *)
  locality -> polymorphic -> (cofixpoint_expr * decl_notation list) list -> unit
