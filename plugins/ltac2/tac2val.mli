(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names

(** {5 Toplevel values} *)

(** {5 Dynamic semantics} *)

(** Values are represented in a way similar to OCaml, i.e. they contrast
    immediate integers (integers, constructors without arguments) and structured
    blocks (tuples, arrays, constructors with arguments), as well as a few other
    base cases, namely closures, strings, named constructors, and dynamic type
    coming from the Rocq implementation. *)

type tag = int

type closure

type valexpr =
| ValInt of int
  (** Immediate integers *)
| ValBlk of tag * valexpr array
  (** Structured blocks *)
| ValStr of Bytes.t
  (** Strings *)
| ValCls of closure
  (** Closures *)
| ValOpn of KerName.t * valexpr array
  (** Open constructors *)
| ValExt : 'a Tac2dyn.Val.tag * 'a -> valexpr
  (** Arbitrary data *)

module Valexpr :
sig
  type t = valexpr
  val is_int : t -> bool
  val tag : t -> int
  val field : t -> int -> t
  val set_field : t -> int -> t -> unit
  val make_block : int -> t array -> t
  val make_int : int -> t
end

(** Closures *)

type 'a arity

val arity_one : (valexpr -> valexpr Proofview.tactic) arity
val arity_suc : 'a arity -> (valexpr -> 'a) arity

val mk_closure : 'v arity -> 'v -> closure
(** The arrows in ['v] should be pure. Use [tclLIFT] or do
    [tclUNIT () >>= fun () -> f args] when you need effects. *)

val mk_closure_val : 'v arity -> 'v -> valexpr
(** Composition of [mk_closure] and [ValCls] *)

val annotate_closure : Tac2expr.frame -> closure -> closure
(** The closure must not be already annotated *)

val purify_closure : 'v arity -> 'v -> 'v
(** For internal use (Tac2externals). Wraps the applications of the ['v] argument
    to make it pure. *)

val to_closure : valexpr -> closure

val apply : closure -> valexpr list -> valexpr Proofview.tactic
(** Given a closure, apply it to some arguments. Handling of argument mismatches
    is done automatically, i.e. in case of over or under-application. *)

val apply_val : valexpr -> valexpr list -> valexpr Proofview.tactic
(** Composition of [to_closure] and [apply] *)

val abstract : int -> (valexpr list -> valexpr Proofview.tactic) -> closure
(** Turn a fixed-arity function into a closure. The inner function is guaranteed
    to be applied to a list whose size is the integer argument. *)
