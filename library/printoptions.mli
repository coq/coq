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

(** values for default, "Printing All" "Sugar All" *)
val default_options : t
val all_options : t
val sugared_options : t

(** getter/setter for Printing options *)
val get : unit -> t
val set : t -> unit

(** run function in context of temporary printing option *)
val with_printing_option : (t -> t) -> ('a -> 'b) -> 'a -> 'b
