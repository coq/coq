(* This module is extracted from Meta-Prl. *)

type token = string
and atom = string list
val opname_token : token
type opname = {
  mutable opname_token : token;
  mutable opname_name : string list;
} 
val nil_opname : opname
val mk_opname : string -> opname -> opname
val make_opname : string list -> opname
val eq : opname -> opname -> bool
val dest_opname : opname -> string list
val string_of_opname : opname -> string
