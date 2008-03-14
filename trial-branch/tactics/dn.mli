(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(* Discrimination nets. *)

type ('lbl,'tree) decompose_fun = 'tree -> ('lbl * 'tree list) option

type ('lbl,'pat,'inf) t (* = (('lbl * int) option,'pat * 'inf) Tlm.t *)

val create : unit -> ('lbl,'pat,'inf) t

(* [add t f (tree,inf)] adds a structured object [tree] together with
   the associated information [inf] to the table [t]; the function
   [f] is used to translated [tree] into its prefix decomposition: [f]
   must decompose any tree into a label characterizing its root node and
   the list of its subtree *)

val add : ('lbl,'pat,'inf) t -> ('lbl,'pat) decompose_fun -> 'pat * 'inf
  -> ('lbl,'pat,'inf) t

val rmv : ('lbl,'pat,'inf) t -> ('lbl,'pat) decompose_fun -> 'pat * 'inf 
  -> ('lbl,'pat,'inf) t

(* [lookup t f tree] looks for trees (and their associated
   information) in table [t] such that the structured object [tree]
   matches against them; [f] is used to translated [tree] into its
   prefix decomposition: [f] must decompose any tree into a label
   characterizing its root node and the list of its subtree *)

val lookup : ('lbl,'pat,'inf) t -> ('lbl,'term) decompose_fun -> 'term
  -> ('pat * 'inf) list

val app : (('pat * 'inf) -> unit) -> ('lbl,'pat,'inf) t -> unit
