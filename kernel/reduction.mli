(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Term
open Context
open Environ

val left2right : bool ref

(***********************************************************************
  s Reduction functions *)

val whd_betaiotazeta        : env -> constr -> constr
val whd_betadeltaiota       : env -> constr -> constr
val whd_betadeltaiota_nolet : env -> constr -> constr

val whd_betaiota     : env -> constr -> constr
val nf_betaiota      : env -> constr -> constr

(***********************************************************************
  s conversion functions *)

exception NotConvertible
exception NotConvertibleVect of int

type 'a conversion_function = env -> 'a -> 'a -> unit
type 'a trans_conversion_function = Names.transparent_state -> 'a conversion_function
type 'a universe_conversion_function = env -> Univ.universes -> 'a -> 'a -> unit
type 'a trans_universe_conversion_function = 
  Names.transparent_state -> 'a universe_conversion_function

type conv_pb = CONV | CUMUL

type 'a universe_compare = 
  { (* Might raise NotConvertible *)
    compare : env -> conv_pb -> sorts -> sorts -> 'a -> 'a;
    compare_instances: bool (* Instance of a flexible constant? *) -> 
		       Univ.Instance.t -> Univ.Instance.t -> 'a -> 'a;
  } 

type 'a universe_state = 'a * 'a universe_compare

type ('a,'b) generic_conversion_function = env -> 'b universe_state -> 'a -> 'a -> 'b

type 'a infer_conversion_function = env -> Univ.universes -> 'a -> 'a -> Univ.constraints

val check_sort_cmp_universes :
  env -> conv_pb -> sorts -> sorts -> Univ.universes -> unit

(* val sort_cmp : *)
(*     conv_pb -> sorts -> sorts -> Univ.constraints -> Univ.constraints *)

(* val conv_sort      : sorts conversion_function *)
(* val conv_sort_leq  : sorts conversion_function *)

val trans_conv_cmp       : ?l2r:bool -> conv_pb -> constr trans_conversion_function
val trans_conv           :
  ?l2r:bool -> ?evars:(existential->constr option) -> constr trans_conversion_function
val trans_conv_leq       :
  ?l2r:bool -> ?evars:(existential->constr option) -> types trans_conversion_function

val trans_conv_universes     :
  ?l2r:bool -> ?evars:(existential->constr option) -> constr trans_universe_conversion_function
val trans_conv_leq_universes :
  ?l2r:bool -> ?evars:(existential->constr option) -> types trans_universe_conversion_function

val conv_cmp       : ?l2r:bool -> conv_pb -> constr conversion_function
val conv           :
  ?l2r:bool -> ?evars:(existential->constr option) -> constr conversion_function
val conv_leq       :
  ?l2r:bool -> ?evars:(existential->constr option) -> types conversion_function
val conv_leq_vecti :
  ?l2r:bool -> ?evars:(existential->constr option) -> types array conversion_function

val infer_conv : ?l2r:bool -> ?evars:(existential->constr option) -> 
  ?ts:Names.transparent_state -> constr infer_conversion_function
val infer_conv_leq : ?l2r:bool -> ?evars:(existential->constr option) -> 
  ?ts:Names.transparent_state -> types infer_conversion_function

val generic_conv : conv_pb -> bool -> (existential->constr option) -> 
  Names.transparent_state -> (constr,'a) generic_conversion_function

(** option for conversion *)
val set_vm_conv : (conv_pb -> types conversion_function) -> unit
val vm_conv : conv_pb -> types conversion_function

val set_nat_conv :
  (conv_pb -> Nativelambda.evars -> types conversion_function) -> unit
val native_conv : conv_pb -> Nativelambda.evars -> types conversion_function

val set_default_conv : (conv_pb -> ?l2r:bool -> types conversion_function) -> unit
val default_conv     : conv_pb -> ?l2r:bool -> types conversion_function
val default_conv_leq : ?l2r:bool -> types conversion_function

(************************************************************************)

(** Builds an application node, reducing beta redexes it may produce. *)
val beta_appvect : constr -> constr array -> constr

(** Builds an application node, reducing the [n] first beta-zeta redexes. *)
val betazeta_appvect : int -> constr -> constr array -> constr

(** Pseudo-reduction rule  Prod(x,A,B) a --> B[x\a] *)
val hnf_prod_applist : env -> types -> constr list -> types


(***********************************************************************
  s Recognizing products and arities modulo reduction *)

val dest_prod       : env -> types -> rel_context * types
val dest_prod_assum : env -> types -> rel_context * types
val dest_lam_assum  : env -> types -> rel_context * types

exception NotArity

val dest_arity : env -> types -> arity (* raises NotArity if not an arity *)
val is_arity   : env -> types -> bool
