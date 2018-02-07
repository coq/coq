(** Printing options record *)

(* storage of the options is in the current instance of the record *)

type t = {
  printing_allow_match_default_clause : bool;
  printing_coercions : bool;
  printing_compact_contexts : bool;
  printing_existential_instances : bool;
  printing_factorizable_match_patterns : bool;
  printing_implicit : bool;
  printing_implicit_defensive : bool;
  printing_matching : bool;
  printing_notations : bool;
  printing_primitive_projection_compatibility : bool;
  printing_primitive_projection_parameters : bool;
  printing_projections : bool;
  printing_records : bool;
  printing_synth : bool;
  printing_universes : bool;
  printing_wildcard : bool;
}

(** the record used for Set Printing All *)
val all_options : t

(** getter/setter for Printing options *)
val get_current_options : unit -> t
val set_current_options : t -> unit

(** getter/setters for Printing options *)
val set_printing_all : unit -> unit
val set_printing_sugared : unit -> unit
val set_printing_defaults : unit -> unit

(** getters for print options *)
val printing_allow_match_default_clause : unit -> bool
val printing_coercions : unit -> bool
val printing_compact_contexts : unit -> bool
val printing_existential_instances : unit -> bool
val printing_factorizable_match_patterns : unit -> bool
val printing_implicit : unit -> bool
val printing_implicit_defensive : unit -> bool
val printing_matching : unit -> bool
val printing_notations : unit -> bool
val printing_primitive_projection_compatibility : unit -> bool
val printing_primitive_projection_parameters : unit -> bool
val printing_projections : unit -> bool
val printing_records : unit -> bool
val printing_synth : unit -> bool
val printing_universes : unit -> bool
val printing_wildcard : unit -> bool

(** setters for print options *)
val set_printing_allow_match_default_clause : bool -> unit
val set_printing_coercions : bool -> unit
val set_printing_compact_contexts : bool -> unit
val set_printing_existential_instances : bool -> unit
val set_printing_factorizable_match_patterns : bool -> unit
val set_printing_implicit : bool -> unit
val set_printing_implicit_defensive : bool -> unit
val set_printing_matching : bool -> unit
val set_printing_notations : bool -> unit
val set_printing_primitive_projection_compatibility : bool -> unit
val set_printing_primitive_projection_parameters : bool -> unit
val set_printing_projections : bool -> unit
val set_printing_records : bool -> unit
val set_printing_synth : bool -> unit
val set_printing_universes : bool -> unit
val set_printing_wildcard : bool -> unit

(** predicate to see if Printing All in effect *)
val printing_all : unit -> bool

(** run function in context of temporary printing option *)
val with_printing_option : (t -> t) -> ('a -> 'b) -> 'a -> 'b
