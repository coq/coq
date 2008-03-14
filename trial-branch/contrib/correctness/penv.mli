(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id$ *)

open Ptype
open Past
open Names
open Libnames
open Term

(* Environment for imperative programs.
 * 
 * Here we manage the global environment, which is imperative,
 * and we provide a functional local environment. 
 *
 * The most important functions, is_in_env, type_in_env and fold_all
 * first look in the local environment then in the global one.
 *)

(* local environments *)

type local_env

val empty : local_env
val add : (identifier * type_v) -> local_env -> local_env
val add_set : identifier -> local_env -> local_env
val is_local : local_env -> identifier -> bool
val is_local_set : local_env -> identifier -> bool

(* typed programs *)

type typing_info = {
  env : local_env;
  kappa : constr ml_type_c
}
  
type typed_program = (typing_info, constr) t

(* global environment *)

val add_global : identifier -> type_v -> typed_program option -> object_name
val add_global_set : identifier -> object_name
val is_global : identifier -> bool
val is_global_set : identifier -> bool
val lookup_global : identifier -> type_v

val all_vars : unit -> identifier list
val all_refs : unit -> identifier list

(* a table keeps the program (for extraction) *)

val find_pgm : identifier -> typed_program option

(* a table keeps the initializations of mutable objects *)

val initialize : identifier -> constr -> unit
val find_init : identifier -> constr

(* access in env (local then global) *)

val type_in_env : local_env -> identifier -> type_v
val is_in_env : local_env -> identifier -> bool

type type_info = Set | TypeV of type_v
val fold_all : (identifier * type_info -> 'a -> 'a) -> local_env -> 'a -> 'a

(* local environnements also contains a list of recursive functions
 * with the associated variant *)

val add_recursion : identifier * (identifier*variant) -> local_env -> local_env
val find_recursion : identifier -> local_env -> identifier * variant

(* We also maintain a table of the currently edited proofs of programs
 * in order to add them in the environnement when the user does Save *)

val new_edited : identifier -> type_v * typed_program -> unit
val is_edited : identifier -> bool
val register : identifier -> identifier -> unit

