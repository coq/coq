
(* $Id$ *)

open Pp

type identifier
type name = Name of identifier | Anonymous

val make_ident : string -> int -> identifier
val string_of_id : identifier -> string
val id_of_string : string -> identifier

val explode_id : identifier -> string list
val print_id : identifier -> std_ppcmds
val pr_idl : identifier list -> std_ppcmds
val atompart_of_id : identifier -> string
val index_of_id : identifier -> int
val id_ord : identifier -> identifier -> int
val id_without_number : identifier -> bool

module Idset : Set.S with type elt = identifier

val lift_ident : identifier -> identifier
val next_ident_away_from : identifier -> identifier list -> identifier
val next_ident_away : identifier -> identifier list -> identifier
val next_name_away : name -> identifier list -> identifier
val next_name_away_with_default : 
  string -> name -> identifier list -> identifier
val get_new_ids : int -> identifier -> identifier list -> identifier list

val id_of_name : identifier -> name -> identifier

type path_kind = CCI | FW | OBJ

val string_of_kind : path_kind -> string
val kind_of_string : string -> path_kind


type section_path

val make_path : string list -> identifier -> path_kind -> section_path
val repr_path : section_path -> string list * identifier * path_kind
val dirpath : section_path -> string list
val basename : section_path -> identifier
val kind_of_path : section_path -> path_kind

val path_of_string : string -> section_path
val string_of_path : section_path -> string
val string_of_path_mind : section_path -> identifier -> string

val coerce_path : path_kind -> section_path -> section_path
val fwsp_of : section_path -> section_path
val ccisp_of : section_path -> section_path
val objsp_of : section_path -> section_path
val fwsp_of_ccisp : section_path -> section_path
val ccisp_of_fwsp : section_path -> section_path
val append_to_path : section_path -> string -> section_path

val sp_ord : section_path -> section_path -> int
val sp_gt : section_path * section_path -> bool

module Spset : Set.S with type elt = section_path
module Spmap : Map.S with type key = section_path

(* Hash-consing *)
val hcons_names : unit ->
  (section_path -> section_path) * (section_path -> section_path) *
  (name -> name) * (identifier -> identifier) * (string -> string)
