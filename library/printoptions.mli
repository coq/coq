(** Printing options record *)

(* storage of the options is in the current instance of the record *)

type t = {
  allow_match_default_clause : bool;
  coercions : bool;
  compact_contexts : bool;
  existential_instances : bool;
  factorizable_match_patterns : bool;
  implicit : bool;
  implicit_defensive : bool;
  let_binder_types : bool;
  matching : bool;
  notations : bool;
  primitive_projection_compatibility : bool;
  primitive_projection_parameters : bool;
  projections : bool;
  records : bool;
  synth : bool;
  universes : bool;
  wildcard : bool;
}

(** the record used for Set Printing All *)
val all_options : t

(** getter/setter for Printing options *)
val get : unit -> t
val set : t -> unit

(** getter/setters for Printing options *)
val set_printing_all : local:bool -> unit
val unset_printing_all : unit -> unit
val set_printing_sugared : local:bool -> unit
val set_printing_defaults : local:bool -> unit

(** run function in context of temporary printing option *)
val with_printing_option : (t -> t) -> ('a -> 'b) -> 'a -> 'b
