
(*i $Id$ i*)

open Names
open Term
open Miniml
open Environ

(*s Result of an extraction. *)

type type_var = Varity | Vprop | Vdefault

type signature = (type_var * identifier) list

type extraction_result =
  | Emltype of ml_type * signature * identifier list
  | Emlterm of ml_ast
  | Eprop

(*s Extraction functions. *)

val extract_constr : env -> constr -> extraction_result

(*s ML declaration corresponding to a Coq reference. *)

val extract_declaration : global_reference -> ml_decl


