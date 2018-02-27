(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
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
  
  type ('kind) branch_info = {
    kind : [> `Master] as 'kind;
    root : id;
    pos  : id;
  }
  
  type ('kind,'diff,'info,'property_data) t constraint 'kind = [> `Master ]
  
  val empty : id -> ('kind,'diff,'info,'property_data) t
  
  val current_branch : ('k,'e,'i,'c) t -> Branch.t
  val branches : ('k,'e,'i,'c) t -> Branch.t list
  
  val get_branch : ('k,'e,'i,'c) t -> Branch.t -> 'k branch_info
  val reset_branch : ('k,'e,'i,'c) t -> Branch.t -> id -> ('k,'e,'i,'c) t
  val branch :
    ('kind,'e,'i,'c) t -> ?root:id -> ?pos:id ->
        Branch.t -> 'kind -> ('kind,'e,'i,'c) t
  val delete_branch : ('k,'e,'i,'c) t -> Branch.t -> ('k,'e,'i,'c) t
  val merge :
    ('k,'diff,'i,'c) t -> id -> ours:'diff -> theirs:'diff -> ?into:Branch.t ->
            Branch.t -> ('k,'diff,'i,'c) t
  val commit : ('k,'diff,'i,'c) t -> id -> 'diff -> ('k,'diff,'i,'c) t
  val rewrite_merge :
    ('k,'diff,'i,'c) t -> id -> ours:'diff -> theirs:'diff -> at:id ->
            Branch.t -> ('k,'diff,'i,'c) t
  val checkout : ('k,'e,'i,'c) t -> Branch.t -> ('k,'e,'i,'c) t
  
  val set_info : ('k,'e,'info,'c) t -> id -> 'info -> ('k,'e,'info,'c) t
  val get_info : ('k,'e,'info,'c) t -> id -> 'info option

  (* Read only dag *)
  module Dag : Dag.S with type node = id
  val dag : ('kind,'diff,'info,'cdata) t -> ('diff,'info,'cdata) Dag.t
  
  (* Properties are not a concept typical of a VCS, but a useful metadata
   * of a DAG (or graph). *)
  val create_property : ('k,'e,'i,'c) t -> id list -> 'c -> ('k,'e,'i,'c) t
  val property_of : ('k,'e,'i,'c) t -> id -> 'c Dag.Property.t list
  val delete_property : ('k,'e,'i,'c) t -> 'c Dag.Property.t -> ('k,'e,'i,'c) t 

  (* Removes all unreachable nodes and returns them *)
  val gc : ('k,'e,'info,'c) t -> ('k,'e,'info,'c) t * Dag.NodeSet.t
  val reachable : ('k,'e,'info,'c) t -> id -> Dag.NodeSet.t

 
end

module Make(OT : Map.OrderedType) : S
with type id = OT.t
and type Dag.node = OT.t
and type Dag.NodeSet.t = Set.Make(OT).t
and type Dag.NodeSet.elt = OT.t

