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

  type branch_name
  val mk_branch_name : string -> branch_name
  val string_of_branch_name : branch_name -> string
  
  val master : branch_name
  
  type id
  
  (* Branches have [branch_info] attached to them. *)
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

  module Dag : Dag.S with type node = id
  val dag : ('k,'diff,'info) t -> ('diff,'info) Dag.t

end

module Make(OT : Map.OrderedType) = struct

module Dag = Dag.Make(OT)

type id = OT.t

type branch_name = string
let mk_branch_name = 
  let bid = ref 0 in
  fun s -> incr bid; string_of_int !bid ^ "_" ^ s
let string_of_branch_name s = s
  
let master = "master"

type 'kind branch_info = {
  kind : [> `Master] as 'kind;
  root : id;
  pos  : id;
}

type ('kind,'edge,'info) t = {
  cur_branch   : branch_name;
  heads        : (branch_name * 'kind branch_info) list;
  dag          : ('edge,'info) Dag.t;
  default_info : 'info;
}

let empty ~default_info root = {
  cur_branch = master; 
  heads = [ master, { root = root; pos = root; kind = `Master } ];
  dag = Dag.empty;
  default_info;
}

let add_node vcs id edges =
  assert (edges <> []);
  { vcs with dag =
     List.fold_left (fun g (t,tgt) -> Dag.add_edge g id t tgt) vcs.dag edges }

let get_branch vcs head =
  try List.assoc head vcs.heads
  with Not_found -> anomaly (str"head " ++ str head ++ str" not found")

let reset_branch vcs head id = { vcs with
  heads =
    List.map (fun (name, h as orig) -> 
      if name = head then name, { h with pos = id } else orig)
    vcs.heads }

let branch vcs ?(root = (get_branch vcs vcs.cur_branch).pos) name kind =
  { vcs with
      heads = (name, { root; pos = root; kind }) :: vcs.heads;
      cur_branch = name }

let delete_branch vcs name = { vcs with
  heads = List.filter (fun (n, _) -> n <> name) vcs.heads }

let merge vcs id ~ours:tr1 ~theirs:tr2 ?(into = vcs.cur_branch) name =
  assert (name <> into);
  let local = into = vcs.cur_branch in
  let br_id = (get_branch vcs name).pos in
  let cur_id = (get_branch vcs into).pos in
  let vcs = add_node vcs id [tr1,cur_id; tr2,br_id] in
  let vcs = reset_branch vcs into id in
  let vcs = if  local then reset_branch vcs name id else vcs in
  vcs

let commit vcs id tr =
  let vcs = add_node vcs id [tr, (get_branch vcs vcs.cur_branch).pos] in
  let vcs = reset_branch vcs vcs.cur_branch id in
  vcs

let checkout vcs name = { vcs with cur_branch = name }

let set_info vcs id info = { vcs with dag = Dag.set_info vcs.dag id info }
let get_info vcs id =
  match Dag.get_info vcs.dag id with Some x -> x | None -> vcs.default_info

let create_cluster vcs l = { vcs with dag = Dag.create_cluster vcs.dag l }

let current_branch vcs = vcs.cur_branch
let branches vcs = List.map fst vcs.heads
let dag vcs = vcs.dag

end
