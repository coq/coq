(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id$ *)

open Names
open Term

(* Some misc. functions *)

val reraise_with_loc : Coqast.loc -> ('a -> 'b) -> 'a -> 'b

val list_of_some : 'a option -> 'a list
val difference : 'a list -> 'a list -> 'a list

val at_id : identifier -> string -> identifier
val un_at : identifier -> identifier * string
val is_at : identifier -> bool

val result_id : identifier
val adr_id : identifier -> identifier

val renaming_of_ids : identifier list -> identifier list
                     -> (identifier * identifier) list * identifier list

val reset_names : unit -> unit
val pre_name    : name -> identifier
val post_name   : name -> identifier
val inv_name    : name -> identifier
val test_name   : name -> identifier
val bool_name   : unit -> identifier
val var_name    : name -> identifier
val phi_name    : unit -> identifier
val for_name    : unit -> identifier
val label_name  : unit -> string

val id_of_name : name -> identifier

(* CIC terms *)

val isevar : constr

val subst_in_constr : (identifier * identifier) list -> constr -> constr
val subst_in_ast : (identifier * identifier) list -> Coqast.t -> Coqast.t
val subst_ast_in_ast : (identifier * Coqast.t) list -> Coqast.t -> Coqast.t
val real_subst_in_constr : (identifier * constr) list -> constr -> constr

val constant : string -> constr
val coq_constant : string list -> string -> section_path
val conj : constr -> constr -> constr

val coq_true : constr
val coq_false : constr

val connective_and : identifier
val connective_or  : identifier
val connective_not : identifier
val is_connective : identifier -> bool

val n_mkNamedProd : constr -> (identifier * constr) list -> constr
val n_lambda  : constr -> (identifier * constr) list -> constr
val abstract : (identifier * constr) list -> constr -> constr

(* for debugging purposes *)

val debug : bool ref
val deb_mess : Pp.std_ppcmds -> unit

