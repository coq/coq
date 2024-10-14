(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open CErrors

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

  val create_property : ('e,'i,'c) t -> id list -> 'c -> ('e,'i,'c) t
  val property_of : ('e,'i,'c) t -> id -> 'c Dag.Property.t list
  val delete_property : ('e,'i,'c) t -> 'c Dag.Property.t -> ('e,'i,'c) t

  (* Removes all unreachable nodes and returns them *)
  val gc : ('e,'info,'c) t -> ('e,'info,'c) t * Dag.NodeSet.t
  val reachable : ('e,'info,'c) t -> id -> Dag.NodeSet.t

end

module Make(OT : Map.OrderedType)(K : Kind) = struct

module Dag = Dag.Make(OT)

type id = OT.t

module Branch =
struct
  type t = string
  let make =
    let bid = ref 0 in
    fun s -> incr bid; string_of_int !bid ^ "_" ^ s
  let equal = CString.equal
  let compare = CString.compare
  let to_string s = s
  let master = "master"
end

type 'a kind_gen = 'a K.t
type kind = Branch.t kind_gen

module BranchMap = Map.Make(Branch)

type branch_info = {
  kind : kind;
  root : id;
  pos  : id;
}

type ('edge,'info,'property_data) t = {
  cur_branch   : Branch.t;
  heads        : branch_info BranchMap.t;
  dag          : ('edge,'info,'property_data) Dag.t;
}

let empty root = {
  cur_branch = Branch.master;
  heads = BranchMap.singleton Branch.master { root = root; pos = root; kind = K.master };
  dag = Dag.empty;
}

let add_node vcs id edges =
  assert (not (CList.is_empty edges));
  { vcs with dag =
     List.fold_left (fun g (t,tgt) -> Dag.add_edge g id t tgt) vcs.dag edges }

let get_branch vcs head =
  try BranchMap.find head vcs.heads
  with Not_found -> anomaly (str"head " ++ str head ++ str" not found.")

let reset_branch vcs head id =
  let map name h =
    if Branch.equal name head then { h with pos = id } else h
  in
  { vcs with heads = BranchMap.mapi map vcs.heads; }

let current_branch vcs = vcs.cur_branch

let branch
  vcs ?(root=(get_branch vcs vcs.cur_branch).pos) ?(pos=root) name kind
=
  { vcs with
      heads = BranchMap.add name { kind; root; pos } vcs.heads;
      cur_branch = name }

let delete_branch vcs name =
  if Branch.equal Branch.master name then vcs else
  let filter n _ = not (Branch.equal n name) in
  { vcs with heads = BranchMap.filter filter vcs.heads }

let merge vcs id ~ours:tr1 ~theirs:tr2 ?(into = vcs.cur_branch) name =
  assert (not (Branch.equal name into));
  let br_id = (get_branch vcs name).pos in
  let cur_id = (get_branch vcs into).pos in
  let vcs = add_node vcs id [tr1,cur_id; tr2,br_id] in
  let vcs = reset_branch vcs into id in
  vcs

let del_edge id vcs tgt = { vcs with dag = Dag.del_edge vcs.dag id tgt }

let rewrite_merge vcs id ~ours:tr1 ~theirs:tr2 ~at:cur_id name =
  let br_id = (get_branch vcs name).pos in
  let old_edges = List.map fst (Dag.from_node vcs.dag id) in
  let vcs = List.fold_left (del_edge id) vcs old_edges in
  let vcs = add_node vcs id [tr1,cur_id; tr2,br_id] in
  vcs

let commit vcs id tr =
  let vcs = add_node vcs id [tr, (get_branch vcs vcs.cur_branch).pos] in
  let vcs = reset_branch vcs vcs.cur_branch id in
  vcs

let checkout vcs name = { vcs with cur_branch = name }

let set_info vcs id info = { vcs with dag = Dag.set_info vcs.dag id info }
let get_info vcs id = Dag.get_info vcs.dag id

let create_property vcs l i = { vcs with dag = Dag.create_property vcs.dag l i }
let property_of vcs i = Dag.property_of vcs.dag i
let delete_property vcs c = { vcs with dag = Dag.del_property vcs.dag c }

let branches vcs = BranchMap.fold (fun x _ accu -> x :: accu) vcs.heads []
let dag vcs = vcs.dag

let rec closure s d n =
  let l = try Dag.from_node d n with Not_found -> [] in
  List.fold_left (fun s (n',_) ->
    if Dag.NodeSet.mem n' s then s
    else closure s d n')
  (Dag.NodeSet.add n s) l

let reachable vcs i = closure Dag.NodeSet.empty vcs.dag i

let gc vcs =
  let alive =
    BranchMap.fold (fun b { pos } s -> closure s vcs.dag pos)
      vcs.heads Dag.NodeSet.empty in
  let dead = Dag.NodeSet.diff (Dag.all_nodes vcs.dag) alive in
  { vcs with dag = Dag.del_nodes vcs.dag dead }, dead

end
