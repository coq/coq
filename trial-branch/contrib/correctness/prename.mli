(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id$ *)

open Names

(* Abstract type for renamings 
 * 
 * Records the names of the mutables objets (ref, arrays) at the different
 * moments of the evaluation, called dates
 *)

type t

type date = string


val empty_ren : t
val update    : t -> date -> identifier list -> t
    (* assign new names for the given variables, associated to a new date *)
val next      : t -> identifier list -> t
    (* assign new names for the given variables, associated to a new
     * date which is generated from an internal counter *)
val push_date : t -> date -> t
    (* put a new date on top of the stack *)

val valid_date   : date -> t -> bool
val current_date : t -> date
val all_dates    : t -> date list

val current_var  : t -> identifier      -> identifier
val current_vars : t -> identifier list -> (identifier * identifier) list
    (* gives the current names of some variables *)

val avoid : t -> identifier list -> t
val fresh : t -> identifier list -> (identifier * identifier) list
    (* introduces new names to avoid and renames some given variables *)

val var_at_date  : t -> date -> identifier -> identifier
    (* gives the name of a variable at a given date *)
val vars_at_date : t -> date -> identifier list
                 -> (identifier * identifier) list
    (* idem for a list of variables *)  

(* pretty-printers *)

val pp : t -> Pp.std_ppcmds
val ppr : t -> unit

