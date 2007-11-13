(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id: sequence.mli aspiwack $ *)

(* This module implements a small list-like datatype with fast append. 
   Operations are not tailrec. *)

type 'a sequence

val iter : ('a -> unit) -> 'a sequence -> unit

val map : ('a -> 'b) -> 'a sequence -> 'b sequence

val element : 'a -> 'a sequence

val append : 'a sequence -> 'a sequence -> 'a sequence
