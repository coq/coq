(***********************************************************************
    v      *   The Coq Proof Assistant  /  The Coq Development Team     
   <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud 
     \VV/  *************************************************************
      //   *      This file is distributed under the terms of the       
           *       GNU Lesser General Public License Version 2.fix_expr        
  ***********************************************************************)

open Names
open Term
open Decl_kinds
open Topconstr
open Tacexpr
open Vernacexpr
open Proof_type
open Pfedit

(** A hook start_proof calls on the type of the definition being started *)
val set_start_hook : (types -> unit) -> unit

val start_proof : identifier -> goal_kind -> types ->
  ?init_tac:tactic -> ?compute_guard:lemma_possible_guards -> 
    declaration_hook -> unit

val start_proof_com : goal_kind ->
  (lident option * (local_binder list * constr_expr * (lident option * recursion_order_expr) option)) list ->
  declaration_hook -> unit

val start_proof_with_initialization : 
  goal_kind -> (bool * lemma_possible_guards * tactic list option) option ->
  (identifier * (types * (int * Impargs.manual_explicitation list))) list ->
  declaration_hook -> unit

(** A hook the next three functions pass to cook_proof *)
val set_save_hook : (Proof.proof -> unit) -> unit

(** {6 Sect } *)
(** [save_named b] saves the current completed proof under the name it
was started; boolean [b] tells if the theorem is declared opaque; it
fails if the proof is not completed *)

val save_named : bool -> unit

(** [save_anonymous b name] behaves as [save_named] but declares the theorem
under the name [name] and respects the strength of the declaration *)

val save_anonymous : bool -> identifier -> unit

(** [save_anonymous_with_strength s b name] behaves as [save_anonymous] but
   declares the theorem under the name [name] and gives it the
   strength [strength] *)

val save_anonymous_with_strength : theorem_kind -> bool -> identifier -> unit

(** [admit ()] aborts the current goal and save it as an assmumption *)

val admit : unit -> unit

(** [get_current_context ()] returns the evar context and env of the
   current open proof if any, otherwise returns the empty evar context
   and the current global env *)

val get_current_context : unit -> Evd.evar_map * Environ.env
