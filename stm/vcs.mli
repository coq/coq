(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* This module builds a VCS like interface on top of Dag, used to build
   a Dag instance by the State Transaction Machine.

   This data structure does not hold system states:
   - Edges are meant to hold a diff.
     The delta between two states, or equivalent data like a vernac_expr whose
     execution corresponds to the application of the diff.
   - Nodes are empty, unless one adds explicit info.
     The info could be a system state, obtaind by applying all the diffs
     from the initial state, but is not necessarily there.
   As a consequence, "checkout" just updates the current branch.

   The type [id] is the type of commits (a node in the dag)
   The type [Vcs.t] has 4 parameters:
    ['info] data attached to a node (like a system state)
    ['diff] data attached to an edge (the commit content, a "patch")
    ['kind] extra data attached to a branch (like being the master branch)
    ['cdata] extra data hold by dag properties
*)

module type Kind =
sig
  type 'a t
  val master : 'a t
end

module type S = sig

  module Branch :
  sig
    type t
    val make : string -> t
    val equal : t -> t -> bool
    val compare : t -> t -> int
    val to_string : t -> string
    val master : t
  end

  type id

  type 'a kind_gen
  type kind = Branch.t kind_gen

  type branch_info = {
    kind : kind;
    root : id;
    pos  : id;
  }

  type ('diff,'info,'property_data) t

  val empty : id -> ('diff,'info,'property_data) t

  val current_branch : ('e,'i,'c) t -> Branch.t
  val branches : ('e,'i,'c) t -> Branch.t list

  val get_branch : ('e,'i,'c) t -> Branch.t -> branch_info
  val reset_branch : ('e,'i,'c) t -> Branch.t -> id -> ('e,'i,'c) t
  val branch :
    ('e,'i,'c) t -> ?root:id -> ?pos:id ->
        Branch.t -> kind -> ('e,'i,'c) t
  val delete_branch : ('e,'i,'c) t -> Branch.t -> ('e,'i,'c) t
  val merge :
    ('diff,'i,'c) t -> id -> ours:'diff -> theirs:'diff -> ?into:Branch.t ->
            Branch.t -> ('diff,'i,'c) t
  val commit : ('diff,'i,'c) t -> id -> 'diff -> ('diff,'i,'c) t
  val rewrite_merge :
    ('diff,'i,'c) t -> id -> ours:'diff -> theirs:'diff -> at:id ->
            Branch.t -> ('diff,'i,'c) t
  val checkout : ('e,'i,'c) t -> Branch.t -> ('e,'i,'c) t

  val set_info : ('e,'info,'c) t -> id -> 'info -> ('e,'info,'c) t
  val get_info : ('e,'info,'c) t -> id -> 'info option

  (* Read only dag *)
  module Dag : Dag.S with type node = id
  val dag : ('diff,'info,'cdata) t -> ('diff,'info,'cdata) Dag.t

  (* Properties are not a concept typical of a VCS, but a useful metadata
   * of a DAG (or graph). *)
  val create_property : ('e,'i,'c) t -> id list -> 'c -> ('e,'i,'c) t
  val property_of : ('e,'i,'c) t -> id -> 'c Dag.Property.t list
  val delete_property : ('e,'i,'c) t -> 'c Dag.Property.t -> ('e,'i,'c) t

  (* Removes all unreachable nodes and returns them *)
  val gc : ('e,'info,'c) t -> ('e,'info,'c) t * Dag.NodeSet.t
  val reachable : ('e,'info,'c) t -> id -> Dag.NodeSet.t


end

module Make(OT : Map.OrderedType)(K : Kind) : S
with type id = OT.t
and type Dag.node = OT.t
and type 'a kind_gen = 'a K.t
and type Dag.NodeSet.t = Set.Make(OT).t
and type Dag.NodeSet.elt = OT.t

