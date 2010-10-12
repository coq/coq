(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Term
open Declarations
open Sign

(** Unsafe environments. We define here a datatype for environments.
   Since typing is not yet defined, it is not possible to check the
   informations added in environments, and that is why we speak here
   of ``unsafe'' environments. *)

(** Environments have the following components:
   - a context for de Bruijn variables
   - a context for de Bruijn variables vm values
   - a context for section variables and goal assumptions
   - a context for section variables and goal assumptions vm values
   - a context for global constants and axioms
   - a context for inductive definitions
   - a set of universe constraints
   - a flag telling if Set is, can be, or cannot be set impredicative *)




type env
val pre_env : env -> Pre_env.env
val env_of_pre_env : Pre_env.env -> env

type named_context_val
val eq_named_context_val : named_context_val -> named_context_val -> bool

val empty_env : env

val universes     : env -> Univ.universes
val rel_context   : env -> rel_context
val named_context : env -> named_context
val named_context_val : env -> named_context_val


val engagement    : env -> engagement option

(** is the local context empty *)
val empty_context : env -> bool

(** {5 Context of de Bruijn variables ([rel_context]) } *)

val nb_rel           : env -> int
val push_rel         : rel_declaration -> env -> env
val push_rel_context :     rel_context -> env -> env
val push_rec_types   : rec_declaration -> env -> env

(** Looks up in the context of local vars referred by indice ([rel_context]) 
   raises [Not_found] if the index points out of the context *)
val lookup_rel    : int -> env -> rel_declaration
val evaluable_rel : int -> env -> bool

(** {6 Recurrence on [rel_context] } *)

val fold_rel_context :
  (env -> rel_declaration -> 'a -> 'a) -> env -> init:'a -> 'a

(** {5 Context of variables (section variables and goal assumptions) } *)

val named_context_of_val : named_context_val -> named_context
val named_vals_of_val : named_context_val -> Pre_env.named_vals
val val_of_named_context : named_context -> named_context_val
val empty_named_context_val : named_context_val


(** [map_named_val f ctxt] apply [f] to the body and the type of
   each declarations.
   *** /!\ ***   [f t] should be convertible with t *)
val map_named_val :
   (constr -> constr) -> named_context_val -> named_context_val

val push_named : named_declaration -> env -> env
val push_named_context_val  :
    named_declaration -> named_context_val -> named_context_val



(** Looks up in the context of local vars referred by names ([named_context]) 
   raises [Not_found] if the identifier is not found *)

val lookup_named     : variable -> env -> named_declaration
val lookup_named_val : variable -> named_context_val -> named_declaration
val evaluable_named  : variable -> env -> bool
val named_type : variable -> env -> types
val named_body : variable -> env -> constr option

(** {6 Recurrence on [named_context]: older declarations processed first } *)

val fold_named_context :
  (env -> named_declaration -> 'a -> 'a) -> env -> init:'a -> 'a

(** Recurrence on [named_context] starting from younger decl *)
val fold_named_context_reverse :
  ('a -> named_declaration -> 'a) -> init:'a -> env -> 'a

(** This forgets named and rel contexts *)
val reset_context : env -> env

(** This forgets rel context and sets a new named context *)
val reset_with_named_context : named_context_val -> env -> env

(** {5 Global constants }
  {6 Add entries to global environment } *)

val add_constant : constant -> constant_body -> env -> env

(** Looks up in the context of global constant names 
   raises [Not_found] if the required path is not found *)
val lookup_constant    : constant -> env -> constant_body
val evaluable_constant1 : constant -> env -> bool
val evaluable_constant_prim : constant -> env -> bool

(** {6 ... } *)
(** [constant_value env c] raises [NotEvaluableConst Opaque] if
   [c] is opaque and [NotEvaluableConst NoBody] if it has no
   body and [Not_found] if it does not exist in [env] *)

type const_evaluation_result = CteNoBody | CteOpaque | CtePrim of Native.op

exception NotEvaluableConst of const_evaluation_result

val constant_value1     : env -> constant -> constr_substituted constant_def
val constant_value_def     : env -> constant -> constr
val constant_type      : env -> constant -> constant_type
val constant_opt_value1 : env -> constant -> constr option

(** {5 Inductive types } *)

val add_mind : mutual_inductive -> mutual_inductive_body -> env -> env

(** Looks up in the context of global inductive names 
   raises [Not_found] if the required path is not found *)
val lookup_mind : mutual_inductive -> env -> mutual_inductive_body

(** {5 Modules } *)

val add_modtype : module_path -> module_type_body -> env -> env

(** [shallow_add_module] does not add module components *)
val shallow_add_module : module_path -> module_body -> env -> env

val lookup_module : module_path -> env -> module_body
val lookup_modtype : module_path -> env -> module_type_body

(** {5 Universe constraints } *)

val set_universes   :   Univ.universes -> env -> env
val add_constraints : Univ.constraints -> env -> env

val set_engagement : engagement -> env -> env

(** {6 Sets of referred section variables }
   [global_vars_set env c] returns the list of [id]'s occurring either
   directly as [Var id] in [c] or indirectly as a section variable
   dependent in a global reference occurring in [c] *)

val global_vars_set : env -> constr -> Idset.t

(** the constr must be a global reference *)
val vars_of_global : env -> constr -> identifier list

val keep_hyps : env -> Idset.t -> section_context

(** {5 Unsafe judgments. }
    We introduce here the pre-type of judgments, which is
  actually only a datatype to store a term with its type and the type of its
  type. *)

type unsafe_judgment = {
  uj_val  : constr;
  uj_type : types }

val make_judge : constr -> types -> unsafe_judgment
val j_val  : unsafe_judgment -> constr
val j_type : unsafe_judgment -> types

type unsafe_type_judgment = {
  utj_val  : constr;
  utj_type : sorts }


(** {6 Compilation of global declaration } *)

val compile_constant_body :
    env -> constr_substituted constant_def -> bool -> Cemitcodes.body_code
                                 (* boxed *)

exception Hyp_not_found

(** [apply_to_hyp sign id f] split [sign] into [tail::(id,_,_)::head] and
   return [tail::(f head (id,_,_) (rev tail))::head].
   the value associated to id should not change *)
val apply_to_hyp : named_context_val -> variable ->
  (named_context -> named_declaration -> named_context -> named_declaration) ->
    named_context_val

(** [apply_to_hyp_and_dependent_on sign id f g] split [sign] into
   [tail::(id,_,_)::head] and
   return [(g tail)::(f (id,_,_))::head]. *)
val apply_to_hyp_and_dependent_on : named_context_val -> variable ->
  (named_declaration -> named_context_val -> named_declaration) ->
    (named_declaration -> named_context_val -> named_declaration) ->
      named_context_val

val insert_after_hyp : named_context_val -> variable ->
  named_declaration ->
    (named_context -> unit) -> named_context_val

val remove_hyps : identifier list -> (named_declaration -> named_declaration) -> (Pre_env.lazy_val -> Pre_env.lazy_val) -> named_context_val -> named_context_val


(** {5 Reduction of primitive} *)
val retroknowledge : env -> Pre_env.retroknowledge
val add_retroknowledge : env -> Native.retro_action * constr -> env

module type RedNativeEntries =
  sig
    type elem
    type args
    module Parray : Native.PARRAY

    val get : args -> int -> elem
    val get_int :  elem -> Native.Uint31.t
    val get_parray : elem -> elem * elem Parray.t
    val mkInt : env -> Native.Uint31.t -> elem
    val mkBool : env -> bool -> elem
    val mkCarry : env -> bool -> elem -> elem (* true if carry *)
    val mkPair : env -> elem -> elem -> elem
    val mkLt : env -> elem
    val mkEq : env -> elem
    val mkGt : env -> elem
    val mkArray : env -> elem -> elem Parray.t -> elem
    val mkClos : name -> constr -> constr -> elem array -> elem
  end

module type RedNative =
 sig
   type elem
   type args
   val red_prim : env -> Native.prim_op -> args -> elem
   val red_caml_prim : env -> Native.caml_prim -> args -> elem
   val red_iterator : env -> Native.iterator -> constr -> args -> elem
   val red_op : env -> Native.op -> constr -> args -> elem option
 end

module RedNative : 
  functor (E:RedNativeEntries) -> 
    RedNative with type elem = E.elem
    with type args = E.args

