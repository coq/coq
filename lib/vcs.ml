(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2013     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Errors

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

  (* Branches have [branch_info] attached to them. *)
  type ('kind) branch_info = {
    kind : [> `Master] as 'kind;
    root : id;
    pos  : id;
  }

  type ('kind,'diff,'info) t constraint 'kind = [> `Master ]

  val empty : id -> ('kind,'diff,'info) t

  val current_branch : ('k,'e,'i) t -> Branch.t
  val branches : ('k,'e,'i) t -> Branch.t list

  val get_branch : ('k,'e,'i) t -> Branch.t -> 'k branch_info
  val reset_branch : ('k,'e,'i) t -> Branch.t -> id -> ('k,'e,'i) t
  val branch :
    ('kind,'e,'i) t -> ?root:id -> Branch.t -> 'kind -> ('kind,'e,'i) t
  val delete_branch : ('k,'e,'i) t -> Branch.t -> ('k,'e,'i) t
  val merge : (* a 'diff is always Nop, fix that XXX *)
    ('k,'diff,'i) t -> id -> ours:'diff -> theirs:'diff -> ?into:Branch.t ->
            Branch.t -> ('k,'diff,'i) t
  val commit : ('k,'diff,'i) t -> id -> 'diff -> ('k,'diff,'i) t
  val checkout : ('k,'e,'i) t -> Branch.t -> ('k,'e,'i) t

  val set_info : ('k,'e,'info) t -> id -> 'info -> ('k,'e,'info) t
  val get_info : ('k,'e,'info) t -> id -> 'info option

  val create_cluster : ('k,'e,'i) t -> id list -> ('k,'e,'i) t

  module Dag : Dag.S with type node = id
  val dag : ('k,'diff,'info) t -> ('diff,'info) Dag.t

end

module Make(OT : Map.OrderedType) = struct

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

module BranchMap = Map.Make(Branch)

type 'kind branch_info = {
  kind : [> `Master] as 'kind;
  root : id;
  pos  : id;
}

type ('kind,'edge,'info) t = {
  cur_branch   : Branch.t;
  heads        : 'kind branch_info BranchMap.t;
  dag          : ('edge,'info) Dag.t;
}

let empty root = {
  cur_branch = Branch.master;
  heads = BranchMap.singleton Branch.master { root = root; pos = root; kind = `Master };
  dag = Dag.empty;
}

let add_node vcs id edges =
  assert (not (CList.is_empty edges));
  { vcs with dag =
     List.fold_left (fun g (t,tgt) -> Dag.add_edge g id t tgt) vcs.dag edges }

let get_branch vcs head =
  try BranchMap.find head vcs.heads
  with Not_found -> anomaly (str"head " ++ str head ++ str" not found")

let reset_branch vcs head id =
  let map name h =
    if Branch.equal name head then { h with pos = id } else h
  in
  { vcs with heads = BranchMap.mapi map vcs.heads; }

let branch vcs ?(root = (get_branch vcs vcs.cur_branch).pos) name kind =
  { vcs with
      heads = BranchMap.add name { root; pos = root; kind } vcs.heads;
      cur_branch = name }

let delete_branch vcs name =
  let filter n _ = not (Branch.equal n name) in
  { vcs with heads = BranchMap.filter filter vcs.heads }

let merge vcs id ~ours:tr1 ~theirs:tr2 ?(into = vcs.cur_branch) name =
  assert (not (Branch.equal name into));
  let br_id = (get_branch vcs name).pos in
  let cur_id = (get_branch vcs into).pos in
  let vcs = add_node vcs id [tr1,cur_id; tr2,br_id] in
  let vcs = reset_branch vcs into id in
  vcs

let commit vcs id tr =
  let vcs = add_node vcs id [tr, (get_branch vcs vcs.cur_branch).pos] in
  let vcs = reset_branch vcs vcs.cur_branch id in
  vcs

let checkout vcs name = { vcs with cur_branch = name }

let set_info vcs id info = { vcs with dag = Dag.set_info vcs.dag id info }
let get_info vcs id = Dag.get_info vcs.dag id

let create_cluster vcs l = { vcs with dag = Dag.create_cluster vcs.dag l }

let current_branch vcs = vcs.cur_branch
let branches vcs = BranchMap.fold (fun x _ accu -> x :: accu) vcs.heads []
let dag vcs = vcs.dag

end
