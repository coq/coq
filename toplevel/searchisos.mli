(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

val search_in_lib : bool ref
val type_search : Term.constr -> unit
val require_module2 : bool option -> string -> string option -> bool -> unit
val upd_tbl_ind_one : unit -> unit
val seetime : bool ref
val load_leaf_entry : string -> Names.section_path * Libobject.obj -> unit
