(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
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

module OpaqueAccess : sig
  type _ t =
    | Ignore : unit t
    | Access : Global.indirect_accessor t
end

type ('prog,'proof,'opaque_access) state_gen = {
  prog : 'prog;
  proof : 'proof;
  opaque_access : 'opaque_access;
}

type no_state = (unit, unit, unit) state_gen
val no_state : no_state
(** Useful for patterns like [{ no_state with proof = newproof }] when
    modifying a subset of the state. *)

val ignore_state : ((unit, unit) Prog.t, (unit, unit) Proof.t, unit OpaqueAccess.t) state_gen

type 'r typed_vernac_gen =
    TypedVernac : {
      spec : (('inprog, 'outprog) Prog.t,
              ('inproof, 'outproof) Proof.t,
              'inaccess OpaqueAccess.t) state_gen;
      run : ('inprog, 'inproof, 'inaccess) state_gen -> ('outprog, 'outproof, unit) state_gen * 'r;
    } -> 'r typed_vernac_gen

type typed_vernac = unit typed_vernac_gen

val typed_vernac_gen
  : (('inprog, 'outprog) Prog.t, ('inproof, 'outproof) Proof.t, 'inaccess OpaqueAccess.t) state_gen
  -> (('inprog, 'inproof, 'inaccess) state_gen -> ('outprog, 'outproof, unit) state_gen * 'r)
  -> 'r typed_vernac_gen

val map_typed_vernac : ('a -> 'b) -> 'a typed_vernac_gen -> 'b typed_vernac_gen

val typed_vernac
  : (('inprog, 'outprog) Prog.t, ('inproof, 'outproof) Proof.t, 'inaccess OpaqueAccess.t) state_gen
  -> (('inprog, 'inproof, 'inaccess) state_gen -> ('outprog, 'outproof, unit) state_gen)
  -> typed_vernac

type full_state = (Prog.stack, Vernacstate.LemmaStack.t option, unit) state_gen

val run : 'r typed_vernac_gen -> full_state -> full_state * 'r

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
val vtopaqueaccess : (opaque_access:Global.indirect_accessor -> unit) -> typed_vernac
