
(* $Id$ *)

(*i*)
open Pp
(*i*)

(*s Identifiers *)

type identifier
type name = Name of identifier | Anonymous

(* Constructor of an identifier;
   [make_ident] builds an identifier from a string and an optional index; if
   the string ends by a digit, a ["_"] is inserted *)
val make_ident : string -> int option -> identifier

(* Some destructors of an identifier *)
val atompart_of_id : identifier -> string
val first_char : identifier -> string
val index_of_id : identifier -> int option

(* Parsing and printing of identifiers *)
val string_of_id : identifier -> string
val id_of_string : string -> identifier
val print_id : identifier -> std_ppcmds

(* Identifiers sets and maps *)
module Idset : Set.S with type elt = identifier
module Idmap : Map.S with type key = identifier

val lift_ident : identifier -> identifier
val next_ident_away_from : identifier -> identifier list -> identifier
val next_ident_away : identifier -> identifier list -> identifier
val next_name_away : name -> identifier list -> identifier
val next_name_away_with_default : 
  string -> name -> identifier list -> identifier

(*s [path_kind] is currently degenerated, [FW] is not used *)
type path_kind = CCI | FW | OBJ

(* parsing and printing of path kinds *)
val string_of_kind : path_kind -> string
val kind_of_string : string -> path_kind

(*s Directory paths = section names paths *)
type dir_path = string list

(* Printing of directory paths as ["#module#submodule"] *)
val string_of_dirpath : dir_path -> string

(*s Section paths *)
type section_path

(* Constructors of [section_path] *)
val make_path : dir_path -> identifier -> path_kind -> section_path

(* Destructors of [section_path] *)
val repr_path : section_path -> dir_path * identifier * path_kind
val dirpath : section_path -> dir_path
val basename : section_path -> identifier
val kind_of_path : section_path -> path_kind

val sp_of_wd : string list -> section_path
val wd_of_sp : section_path -> string list

(* Parsing and printing of section path as ["#module#id#kind"] *)
val path_of_string : string -> section_path
val string_of_path : section_path -> string
val print_sp : section_path -> std_ppcmds

(*i
val string_of_path_mind : section_path -> identifier -> string
val coerce_path : path_kind -> section_path -> section_path
val fwsp_of : section_path -> section_path
val ccisp_of : section_path -> section_path
val objsp_of : section_path -> section_path
val fwsp_of_ccisp : section_path -> section_path
val ccisp_of_fwsp : section_path -> section_path
val append_to_path : section_path -> string -> section_path

val sp_gt : section_path * section_path -> bool
i*)
val sp_ord : section_path -> section_path -> int

(* [is_dirpath_prefix p1 p2=true] if [p1] is a prefix of or is equal to [p2] *)
val dirpath_prefix_of : dir_path -> dir_path -> bool
(*i
module Spset : Set.S with type elt = section_path
i*)
module Spmap : Map.S with type key = section_path

(*s Specific paths for declarations *)
type constant_path = section_path
type inductive_path = section_path * int
type constructor_path = inductive_path * int

(* Hash-consing *)
val hcons_names : unit ->
  (section_path -> section_path) * (section_path -> section_path) *
  (name -> name) * (identifier -> identifier) * (string -> string)

