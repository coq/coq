
(*i $Id$ i*)

open Names
open Term
open Miniml

(*s Result of an extraction. *)

type type_var = Varity | Vskip

type signature = (type_var * identifier) list

type extraction_result =
  | Emltype of ml_type * signature * identifier list
  | Emlterm of ml_ast

(*s Extraction functions. *)

val extract_constr : constr -> extraction_result

(*s ML declaration corresponding to a Coq reference. *)

val extract_declaration : global_reference -> ml_decl


