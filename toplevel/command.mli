(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*i*)
open Names
open Term
open Declare
open Library
open Nametab
(*i*)

(*s Declaration functions. The following functions take ASTs,
   transform them into [constr] and then call the corresponding
   functions of [Declare]; they return an absolute reference to the
   defined object *)

val constant_entry_of_com :
  Coqast.t * Coqast.t option * bool -> Safe_typing.constant_entry

val declare_global_definition :
  Names.identifier ->
  Safe_typing.constant_entry ->
  Declare.strength -> bool -> Nametab.global_reference

val definition_body : identifier -> bool * strength -> 
  Coqast.t -> Coqast.t option -> global_reference

val definition_body_red : Tacred.red_expr option -> identifier
  -> bool * strength -> Coqast.t -> Coqast.t option -> global_reference

val syntax_definition : identifier -> Coqast.t -> unit

(*i
val abstraction_definition : identifier -> int array -> Coqast.t -> unit
i*)

val hypothesis_def_var : bool -> identifier -> strength -> Coqast.t
  -> global_reference

val parameter_def_var : identifier -> Coqast.t -> constant

val build_mutual : 
  (identifier * Coqast.t) list -> 
    (identifier * Coqast.t * (identifier * Coqast.t) list) list -> bool -> unit

val declare_mutual_with_eliminations :
  Indtypes.mutual_inductive_entry -> section_path

val build_recursive :
  (identifier * ((identifier * Coqast.t) list) * Coqast.t * Coqast.t) list 
  -> unit

val build_corecursive :  (identifier * Coqast.t * Coqast.t) list -> unit

val build_scheme : (identifier * bool * Nametab.qualid * Coqast.t) list -> unit

val start_proof_com : identifier option -> strength -> Coqast.t -> unit

(*s [save_named b] saves the current completed proof under the name it
was started; boolean [b] tells if the theorem is declared opaque; it
fails if the proof is not completed *)

val save_named : bool -> unit

(* [save_anonymous b name] behaves as [save_named] but declares the theorem
under the name [name] and respects the strength of the declaration *)

val save_anonymous : bool -> identifier -> unit

(* [save_anonymous_with_strength s b name] behaves as [save_anonymous] but
   declares the theorem under the name [name] and gives it the
   strength [strength] *)

val save_anonymous_with_strength : strength -> bool -> identifier -> unit

(* [get_current_context ()] returns the evar context and env of the
   current open proof if any, otherwise returns the empty evar context
   and the current global env *)

val get_current_context : unit -> Evd.evar_map * Environ.env
