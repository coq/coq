(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2013     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
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
   The type [Vcs.t] has 3 parameters:
    ['info] data attached to a node (like a system state)
    ['diff] data attached to an edge (the commit content, a "patch")
    ['kind] extra data attached to a branch (like being the master branch)
*)

module type S = sig

  type branch_name
  val mk_branch_name : string -> branch_name
  val string_of_branch_name : branch_name -> string
  
  val master : branch_name
  
  type id
  
  type ('kind) branch_info = {
    kind : [> `Master] as 'kind;
    root : id;
    pos  : id;
  }
  
  type ('kind,'diff,'info) t constraint 'kind = [> `Master ]
  
  val empty : default_info:'info -> id -> ('kind,'diff,'info) t
  
  val current_branch : ('k,'e,'i) t -> branch_name
  val branches : ('k,'e,'i) t -> branch_name list
  
  val get_branch : ('k,'e,'i) t -> branch_name -> 'k branch_info
  val reset_branch : ('k,'e,'i) t -> branch_name -> id -> ('k,'e,'i) t
  val branch :
    ('kind,'e,'i) t -> ?root:id -> branch_name -> 'kind -> ('kind,'e,'i) t
  val delete_branch : ('k,'e,'i) t -> branch_name -> ('k,'e,'i) t
  val merge : (* a 'diff is always Nop, fix that XXX *)
    ('k,'diff,'i) t -> id -> ours:'diff -> theirs:'diff -> ?into:branch_name ->
            branch_name -> ('k,'diff,'i) t
  val commit : ('k,'diff,'i) t -> id -> 'diff -> ('k,'diff,'i) t
  val checkout : ('k,'e,'i) t -> branch_name -> ('k,'e,'i) t
  
  val set_info : ('k,'e,'info) t -> id -> 'info -> ('k,'e,'info) t
  val get_info : ('k,'e,'info) t -> id -> 'info

  val create_cluster : ('k,'e,'i) t -> id list -> ('k,'e,'i) t

  (* read only dag *)
  module Dag : Dag.S with type node = id
  val dag : ('k,'diff,'info) t -> ('diff,'info) Dag.t

end

module Make(OT : Map.OrderedType) : S with type id = OT.t
