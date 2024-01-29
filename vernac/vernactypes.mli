(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(** Interpretation of extended vernac phrases. *)

module Prog : sig
  type state = Declare.OblState.t
  type stack = state NeList.t

  type (_,_) t =
    | Ignore : (unit, unit) t
    | Modify : (state, state) t
    | Read : (state, unit) t
    | Push : (unit, unit) t
    | Pop : (state, unit) t
end

module Proof : sig
  type state = Declare.Proof.t

  type (_,_) t =
    | Ignore : (unit, unit) t
    | Modify : (state, state) t
    | Read : (state, unit) t
    | ReadOpt : (state option, unit) t
    | Reject : (unit, unit) t
    | Close : (state, unit) t
    | Open : (unit, state) t
end

type typed_vernac =
    TypedVernac : {
      prog : ('in1, 'out1) Prog.t;
      proof : ('in2, 'out2) Proof.t;
      run : pm:'in1 -> proof:'in2 -> 'out1 * 'out2;
    } -> typed_vernac

val typed_vernac
  : ('in1, 'out1) Prog.t
  -> ('in2, 'out2) Proof.t
  -> (pm:'in1 -> proof:'in2 -> 'out1 * 'out2)
  -> typed_vernac

val run : typed_vernac -> pm:Prog.stack -> stack:Vernacstate.LemmaStack.t option
  -> Vernacstate.LemmaStack.t option * Prog.stack

(** Some convenient typed_vernac constructors. Used by coqpp. *)

val vtdefault : (unit -> unit) -> typed_vernac
val vtnoproof : (unit -> unit) -> typed_vernac
val vtcloseproof : (lemma:Declare.Proof.t -> pm:Declare.OblState.t -> Declare.OblState.t) -> typed_vernac
val vtopenproof : (unit -> Declare.Proof.t) -> typed_vernac
val vtmodifyproof : (pstate:Declare.Proof.t -> Declare.Proof.t) -> typed_vernac
val vtreadproofopt : (pstate:Declare.Proof.t option -> unit) -> typed_vernac
val vtreadproof : (pstate:Declare.Proof.t -> unit) -> typed_vernac
val vtreadprogram : (pm:Declare.OblState.t -> unit) -> typed_vernac
val vtmodifyprogram : (pm:Declare.OblState.t -> Declare.OblState.t) -> typed_vernac
val vtdeclareprogram : (pm:Declare.OblState.t -> Declare.Proof.t) -> typed_vernac
val vtopenproofprogram : (pm:Declare.OblState.t -> Declare.OblState.t * Declare.Proof.t) -> typed_vernac
