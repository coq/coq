(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* enable in case of stm problems  *)
(* let stm_debug () = CDebug.(get_flag misc) *)
let stm_debug = ref false

let stm_pr_err s  = Format.eprintf "%s] %s\n%!"     (Spawned.process_id ()) s
let stm_pp_err pp = Format.eprintf "%s] @[%a@]\n%!" (Spawned.process_id ()) Pp.pp_with pp

let stm_prerr_endline s = if !stm_debug then begin stm_pr_err (s ()) end else ()
let stm_pperr_endline s = if !stm_debug then begin stm_pp_err (s ()) end else ()

let stm_prerr_debug   s = if CDebug.(get_flag misc) then begin stm_pr_err (s ()) end else ()

open Pp
open CErrors
open Names
open Feedback
open Vernacexpr
open Vernacextend

module PG_compat = Vernacstate.Declare [@@ocaml.warning "-3"]

let is_vtkeep = function VtKeep _ -> true | _ -> false
let get_vtkeep = function VtKeep x -> x | _ -> assert false

module AsyncOpts = struct

  type cache = Force
  type async_proofs = APoff | APonLazy | APon
  type tac_error_filter = FNone | FOnly of string list | FAll

  type stm_opt = {
    async_proofs_n_workers : int;
    async_proofs_n_tacworkers : int;

    async_proofs_cache : cache option;
    async_proofs_mode : async_proofs;

    async_proofs_private_flags : string option;
    async_proofs_never_reopen_branch : bool;

    async_proofs_tac_error_resilience : tac_error_filter;
    async_proofs_cmd_error_resilience : bool;
    async_proofs_delegation_threshold : float;

    async_proofs_worker_priority : CoqworkmgrApi.priority;
  }

  let default_opts = {
    async_proofs_n_workers = 1;
    async_proofs_n_tacworkers = 2;

    async_proofs_cache = None;

    async_proofs_mode = APoff;

    async_proofs_private_flags = None;
    async_proofs_never_reopen_branch = false;

    async_proofs_tac_error_resilience = FOnly [ "curly" ];
    async_proofs_cmd_error_resilience = true;
    async_proofs_delegation_threshold = 0.03;

    async_proofs_worker_priority = CoqworkmgrApi.Low;
  }

  let cur_opt : stm_opt option ref = ref None
  let set_cur_opt o = assert (Option.is_empty !cur_opt); cur_opt := Some o
  let cur_opt () = match !cur_opt with
    | Some o -> o
    | None ->
      anomaly Pp.(str "Incorrect stm init: accessing options before they are set.")
end

open AsyncOpts

let async_proofs_is_master opt =
  opt.async_proofs_mode = APon &&
  !Flags.async_proofs_worker_id = "master"

let execution_error ?loc state_id msg =
    feedback ~id:state_id (Message (Error, loc, [], msg))

module Hooks = struct

let state_computed = ref (fun ~doc:_ state_id ~in_cache ->
    feedback ~id:state_id Processed)

let state_ready = ref (fun ~doc:_ state_id -> ())

let forward_feedback =
  let m = Mutex.create () in
  ref (function
    | { doc_id = did; span_id = id; route; contents } ->
        CThread.with_lock m ~scope:(fun () -> feedback ~did ~id ~route contents))

let unreachable_state = ref (fun ~doc:_ _ _ -> ())

let document_add = ref (fun _ _ -> ())

let document_edit = ref (fun _ -> ())

let sentence_exec = ref (fun _ -> ())

end

let async_proofs_workers_extra_env = ref [||]

type aast = {
  verbose : bool;
  indentation : int;
  strlen : int;
  mutable expr : vernac_control; (* mutable: Proof using hinted by aux file *)
}
let pr_ast { expr; indentation } = Pp.(int indentation ++ str " " ++ Ppvernac.pr_vernac expr)

(* Commands piercing opaque (probably should be using the vernactypes system instead) *)
let may_pierce_opaque = function
  | VernacSynPure (VernacPrint _) -> true
  | VernacSynterp (VernacExtend ({ ext_plugin = "coq-core.plugins.extraction" }, _)) -> true
  | _ -> false

type depth = int
type 'branch branch_type_gen =
  | Master
  | Proof of depth
  | Edit of
      Stateid.t * Stateid.t  * Vernacextend.vernac_qed_type * 'branch

module Kind =
struct
  type 'a t = 'a branch_type_gen
  let master = Master
end

module Vcs_ = Vcs.Make(Stateid.Self)(Kind)
type future_proof = Declare.Proof.closed_proof_output option Future.computation

type branch_type = Vcs_.Branch.t Kind.t
(* TODO 8.7 : split commands and tactics, since this type is too messy now *)
type cqueue = MainQueue | SkipQueue
type cmd_t = {
  ctac : bool; (* is a tactic *)
  ceff : bool; (* is a side-effecting command in the middle of a proof *)
  cast : aast;
  cids : Names.Id.t list;
  cblock : proof_block_name option;
  cqueue : cqueue;
  cancel_switch : AsyncTaskQueue.cancel_switch; }
type fork_t = aast * Vcs_.Branch.t * opacity_guarantee * Names.Id.t list
type qed_t = {
  qast : aast;
  keep : vernac_qed_type;
  mutable fproof : (future_proof option * AsyncTaskQueue.cancel_switch) option;
  brname : Vcs_.Branch.t;
  brinfo : Vcs_.branch_info
}
type seff_t = ReplayCommand of aast | CherryPickEnv
type alias_t = Stateid.t * aast

type transaction =
  | Cmd    of cmd_t
  | Fork   of fork_t
  | Qed    of qed_t
  | Sideff of seff_t
  | Alias  of alias_t
  | Noop
type step =
  | SCmd    of cmd_t
  | SFork   of fork_t * Stateid.t option
  | SQed    of qed_t * Stateid.t
  | SSideff of seff_t * Stateid.t
  | SAlias  of alias_t

type visit = { step : step; next : Stateid.t }

let mkTransTac cast cblock cqueue =
  Cmd { ctac = true; cast; cblock; cqueue; cids = []; ceff = false; cancel_switch = ref false }

let mkTransCmd cast cids ceff cqueue =
  Cmd { ctac = false; cast; cblock = None; cqueue; cids; ceff; cancel_switch = ref false }

type cached_state =
  | EmptyState
  | ParsingState of Pcoq.frozen_t
  | FullState of Vernacstate.t
  | ErrorState of Pcoq.frozen_t option * Exninfo.iexn
type branch = Vcs_.Branch.t * Vcs_.branch_info
type backup = { mine : branch; others : branch list }

module DynBlockData : Dyn.S = Dyn.Make ()

(* Clusters of nodes implemented as Dag properties.  While Dag and Vcs impose
 * no constraint on properties, here we impose boxes to be non overlapping.
 * Such invariant makes sense for the current kinds of boxes (proof blocks and
 * entire proofs) but may make no sense and dropped/refined in the future.
 * Such invariant is useful to detect broken proof block detection code *)
type box =
  | ProofTask of pt
  | ProofBlock of static_block_declaration * proof_block_name
and pt = { (* TODO: inline records in OCaml 4.03 *)
  lemma : Stateid.t;
  qed   : Stateid.t;
}
and static_block_declaration = {
  block_start : Stateid.t;
  block_stop  : Stateid.t;
  dynamic_switch : Stateid.t;
  carry_on_data : DynBlockData.t;
}

(* Functions that work on a Vcs with a specific branch type *)
module Vcs_aux : sig

  val proof_nesting : ('t,'i,'c) Vcs_.t -> int
  val find_proof_at_depth :
          ('t, 'i,'c) Vcs_.t -> int ->
      Vcs_.Branch.t * Vcs_.branch_info
  exception Expired
  val visit : (transaction,'i,'c) Vcs_.t -> Vcs_.Dag.node -> visit

end = struct (* {{{ *)

  let proof_nesting vcs =
    List.fold_left max 0
      (CList.map_filter
        (function
         | { Vcs_.kind = Proof n } -> Some n
         | { Vcs_.kind = Edit _ } -> Some 1
         | _ -> None)
        (List.map (Vcs_.get_branch vcs) (Vcs_.branches vcs)))

  let find_proof_at_depth vcs pl =
    try List.find (function
          | _, { Vcs_.kind = Proof n } -> Int.equal n pl
          | _, { Vcs_.kind = Edit _ } -> anomaly(Pp.str "find_proof_at_depth")
          | _ -> false)
        (List.map (fun h -> h, Vcs_.get_branch vcs h) (Vcs_.branches vcs))
    with Not_found -> failwith "find_proof_at_depth"

  exception Expired
  let visit vcs id =
    if Stateid.equal id Stateid.initial then
      anomaly(Pp.str "Visiting the initial state id.")
    else if Stateid.equal id Stateid.dummy then
      anomaly(Pp.str "Visiting the dummy state id.")
    else
    try
      match Vcs_.Dag.from_node (Vcs_.dag vcs) id with
      | [n, Cmd x] -> { step = SCmd x; next = n }
      | [n, Alias x] -> { step = SAlias x; next = n }
      | [n, Fork x] -> { step = SFork (x,None); next = n }
      | [n, Fork x; p, Noop] -> { step = SFork (x,Some p); next = n }
      | [p, Noop; n, Fork x] -> { step = SFork (x,Some p); next = n }
      | [n, Qed x; p, Noop]
      | [p, Noop; n, Qed x] -> { step = SQed (x,p); next = n }
      | [n, Sideff CherryPickEnv; p, Noop]
      | [p, Noop; n, Sideff CherryPickEnv]-> { step = SSideff (CherryPickEnv, p); next = n }
      | [n, Sideff (ReplayCommand x); p, Noop]
      | [p, Noop; n, Sideff (ReplayCommand x)]-> { step = SSideff(ReplayCommand x,p); next = n }
      | [n, Sideff (ReplayCommand x)]-> {step = SSideff(ReplayCommand x, Stateid.dummy); next=n}
      | _ -> anomaly (Pp.str ("Malformed VCS at node "^Stateid.to_string id^"."))
    with Not_found -> raise Expired

end (* }}} *)

(*************************** THE DOCUMENT *************************************)
(******************************************************************************)

(* The main document type associated to a VCS *)
type stm_doc_type =
  | VoDoc       of string
  | VosDoc      of string
  | Interactive of Coqargs.top

(* Dummy until we land the functional interp patch + fixed start_library *)
type doc = int
let dummy_doc : doc = 0

(* Imperative wrap around VCS to obtain _the_ VCS that is the
 * representation of the document Coq is currently processing *)
module VCS : sig

  exception Expired

  module Branch : (module type of Vcs_.Branch with type t = Vcs_.Branch.t)
  type id = Stateid.t
  type branch_info = Vcs_.branch_info = {
    kind : branch_type;
    root : id;
    pos  : id;
  }

  type vcs = (transaction, state_info, box) Vcs_.t
  and state_info = { (* TODO: Make this record private to VCS *)
    mutable n_reached : int;      (* debug cache: how many times was computed *)
    mutable n_goals : int;        (* open goals: indentation *)
    mutable state : cached_state; (* state value *)
    mutable proof_mode : Pvernac.proof_mode option;
    mutable vcs_backup : vcs option * backup option;
  }

  val init : stm_doc_type -> id -> Pcoq.frozen_t -> doc
  (* val get_type : unit -> stm_doc_type *)
  val set_ldir : Names.DirPath.t -> unit
  val get_ldir : unit -> Names.DirPath.t

  val is_interactive : unit -> bool
  val is_vos_doc : unit -> bool

  val current_branch : unit -> Branch.t
  val checkout : Branch.t -> unit
  val branches : unit -> Branch.t list
  val get_branch : Branch.t -> branch_info
  val get_branch_pos : Branch.t -> id
  val new_node : ?id:Stateid.t -> Pvernac.proof_mode option -> unit -> id
  val merge : id -> ours:transaction -> ?into:Branch.t -> Branch.t -> unit
  val rewrite_merge : id -> ours:transaction -> at:id -> Branch.t -> unit
  val delete_branch : Branch.t -> unit
  val commit : id -> transaction -> unit
  val mk_branch_name : aast -> Branch.t
  val edit_branch : Branch.t
  val branch : ?root:id -> ?pos:id -> Branch.t -> branch_type -> unit
  val reset_branch : Branch.t -> id -> unit
  val reachable : id -> Stateid.Set.t
  val cur_tip : unit -> id

  val get_info : id -> state_info
  val reached : id -> unit
  val goals : id -> int -> unit
  val set_state : id -> cached_state -> unit
  val get_state : id -> cached_state
  val set_parsing_state : id -> Pcoq.frozen_t -> unit
  val get_parsing_state : id -> Pcoq.frozen_t option
  val get_proof_mode : id -> Pvernac.proof_mode option

  (* cuts from start -> stop, raising Expired if some nodes are not there *)
  val slice : block_start:id -> block_stop:id -> vcs
  val nodes_in_slice : block_start:id -> block_stop:id -> Stateid.t list

  val create_proof_task_box : id list -> qed:id -> block_start:id -> unit
  val create_proof_block : static_block_declaration -> string -> unit
  val box_of : id -> box list
  val delete_boxes_of : id -> unit
  val proof_task_box_of : id -> pt option

  val proof_nesting : unit -> int
  val checkout_shallowest_proof_branch : unit -> unit
  val propagate_sideff : action:seff_t -> Stateid.t list
  val propagate_qed : unit -> unit

  val gc : unit -> unit

  val visit : id -> visit

  val print : ?now:bool -> unit -> unit

  val backup : unit -> vcs
  val restore : vcs -> unit

end = struct (* {{{ *)

  include Vcs_
  exception Expired = Vcs_aux.Expired

  open Printf

  type vcs = (transaction, state_info, box) t
  and state_info = { (* TODO: Make this record private to VCS *)
    mutable n_reached : int;      (* debug cache: how many times was computed *)
    mutable n_goals : int;        (* open goals: indentation *)
    mutable state : cached_state; (* state value *)
    mutable proof_mode : Pvernac.proof_mode option;
    mutable vcs_backup : vcs option * backup option;
  }
  let default_info proof_mode =
    {
      n_reached = 0; n_goals = 0;
      state = EmptyState;
      proof_mode;
      vcs_backup = (None,None);
    }

  let print_dag vcs () =

    (* Due to threading, be wary that this will be called from the
       toplevel with we_are_parsing set to true, as indeed, the
       toplevel is waiting for input . What a race! XD

       In case you are hitting the race enable stm_debug.
    *)
    if !stm_debug then Flags.in_synterp_phase := false;

    let fname =
      "stm_" ^ Str.global_replace (Str.regexp " ") "_" (Spawned.process_id ()) in
    let string_of_transaction = function
      | Cmd { cast = t } | Fork (t, _,_,_) ->
          (try Pp.string_of_ppcmds (pr_ast t) with e when CErrors.noncritical e -> "ERR")
      | Sideff (ReplayCommand t) ->
          sprintf "Sideff(%s)"
            (try Pp.string_of_ppcmds (pr_ast t) with e when CErrors.noncritical e -> "ERR")
      | Sideff CherryPickEnv -> "EnvChange"
      | Noop -> " "
      | Alias (id,_) -> sprintf "Alias(%s)" (Stateid.to_string id)
      | Qed { qast } -> Pp.string_of_ppcmds (pr_ast qast) in
    let is_green id =
      match get_info vcs id with
      | Some { state = FullState _ } -> true
      | _ -> false in
    let is_red id =
      match get_info vcs id with
      | Some { state = ErrorState _ } -> true
      | _ -> false in
    let head = current_branch vcs in
    let heads =
      List.map (fun x -> x, (get_branch vcs x).pos) (branches vcs) in
    let graph = dag vcs in
    let quote s =
      Str.global_replace (Str.regexp "\n") "<BR/>"
       (Str.global_replace (Str.regexp "<") "&lt;"
        (Str.global_replace (Str.regexp ">") "&gt;"
         (Str.global_replace (Str.regexp "\"") "&quot;"
          (Str.global_replace (Str.regexp "&") "&amp;"
           (String.sub s 0 (min (String.length s) 20)))))) in
    let fname_dot, fname_ps =
      let f = "/tmp/" ^ Filename.basename fname in
      f ^ ".dot", f ^ ".pdf" in
    let node id = "s" ^ Stateid.to_string id in
    let edge tr =
      sprintf "<<FONT POINT-SIZE=\"12\" FACE=\"sans\">%s</FONT>>"
        (quote (string_of_transaction tr)) in
    let node_info id =
      match get_info vcs id with
      | None -> ""
      | Some info ->
          sprintf "<<FONT POINT-SIZE=\"12\">%s</FONT>" (Stateid.to_string id) ^
          sprintf " <FONT POINT-SIZE=\"11\">r:%d g:%d</FONT>>"
            info.n_reached info.n_goals in
    let color id =
      if is_red id then "red" else if is_green id then "green" else "white" in
    let nodefmt oc id =
      fprintf oc "%s [label=%s,style=filled,fillcolor=%s];\n"
        (node id) (node_info id) (color id) in

    let ids = ref Stateid.Set.empty in
    let boxes = ref [] in
    (* Fill in *)
    Dag.iter graph (fun from _ _ l ->
      ids := Stateid.Set.add from !ids;
      List.iter (fun box -> boxes := box :: !boxes)
        (Dag.property_of graph from);
      List.iter (fun (dest, _) ->
        ids := Stateid.Set.add dest !ids;
        List.iter (fun box -> boxes := box :: !boxes)
          (Dag.property_of graph dest))
      l);
    boxes := CList.sort_uniquize Dag.Property.compare !boxes;

    let oc = open_out fname_dot in
    output_string oc "digraph states {\n";
    Dag.iter graph (fun from cf _ l ->
      List.iter (fun (dest, trans) ->
       fprintf oc "%s -> %s [xlabel=%s,labelfloat=true];\n"
           (node from) (node dest) (edge trans)) l
    );

    let contains b1 b2 =
      Stateid.Set.subset
        (Dag.Property.having_it b2) (Dag.Property.having_it b1) in
    let same_box = Dag.Property.equal in
    let outerboxes boxes =
       List.filter (fun b ->
         not (List.exists (fun b1 ->
           not (same_box b1 b) && contains b1 b) boxes)
         ) boxes in
    let rec rec_print b =
      boxes := CList.remove same_box b !boxes;
      let sub_boxes = List.filter (contains b) (outerboxes !boxes) in
      fprintf oc "subgraph cluster_%s {\n" (Dag.Property.to_string b);
      List.iter rec_print sub_boxes;
      Stateid.Set.iter (fun id ->
        if Stateid.Set.mem id !ids then begin
          ids := Stateid.Set.remove id !ids;
          nodefmt oc id
        end)
        (Dag.Property.having_it b);
      match Dag.Property.data b with
      | ProofBlock ({ dynamic_switch = id }, lbl) ->
          fprintf oc "label=\"%s (test:%s)\";\n" lbl (Stateid.to_string id);
          fprintf oc "color=red; }\n"
      | ProofTask _ -> fprintf oc "color=blue; }\n"
      in
    List.iter rec_print (outerboxes !boxes);
    Stateid.Set.iter (nodefmt oc) !ids;

    List.iteri (fun i (b,id) ->
      let shape = if Branch.equal head b then "box3d" else "box" in
      fprintf oc "b%d -> %s;\n" i (node id);
      fprintf oc "b%d [shape=%s,label=\"%s\"];\n" i shape
        (Branch.to_string b);
    ) heads;

    output_string oc "}\n";
    close_out oc;
    ignore(Sys.command
      ("dot -Tpdf -Gcharset=latin1 " ^ fname_dot ^ " -o" ^ fname_ps))

  let vcs : vcs ref = ref (empty Stateid.dummy)

  let doc_type = ref (Interactive (Coqargs.TopLogical (Names.DirPath.make [])))
  let ldir = ref Names.DirPath.empty

  let init dt id ps =
    doc_type := dt;
    vcs := empty id;
    let info = { (default_info None) with state = ParsingState ps } in
    vcs := set_info !vcs id info;
    dummy_doc

  let set_ldir ld =
    ldir := ld

  let get_ldir () = !ldir
  (* let get_type () = !doc_type *)

  let is_interactive () =
    match !doc_type with
    | Interactive _ -> true
    | _ -> false

  let is_vos_doc () =
    match !doc_type with
    | VosDoc _ -> true
    | _ -> false

  let current_branch () = current_branch !vcs

  let checkout head = vcs := checkout !vcs head
  let branches () = branches !vcs
  let get_branch head = get_branch !vcs head
  let get_branch_pos head = (get_branch head).pos
  let new_node ?(id=Stateid.fresh ()) proof_mode () =
    assert(Vcs_.get_info !vcs id = None);
    vcs := set_info !vcs id (default_info proof_mode);
    id
  let merge id ~ours ?into branch =
    vcs := merge !vcs id ~ours ~theirs:Noop ?into branch
  let delete_branch branch = vcs := delete_branch !vcs branch
  let reset_branch branch id = vcs := reset_branch !vcs branch id
  let commit id t = vcs := commit !vcs id t
  let rewrite_merge id ~ours ~at branch =
    vcs := rewrite_merge !vcs id ~ours ~theirs:Noop ~at branch
  let reachable id = reachable !vcs id
  let mk_branch_name { expr = x } = Branch.make
    (match x.CAst.v.Vernacexpr.expr with
    | VernacSynPure (VernacDefinition (_,({CAst.v=Name i},_),_)) -> Id.to_string i
    | VernacSynPure (VernacStartTheoremProof (_,[({CAst.v=i},_),_])) -> Id.to_string i
    | VernacSynPure (VernacInstance (({CAst.v=Name i},_),_,_,_,_)) -> Id.to_string i
    | _ -> "branch")
  let edit_branch = Branch.make "edit"
  let branch ?root ?pos name kind = vcs := branch !vcs ?root ?pos name kind
  let get_info id =
    match get_info !vcs id with
    | Some x -> x
    | None -> raise Vcs_aux.Expired
  let set_state id s =
    let info = get_info id in
    info.state <- s;
    let is_full_state_valid = match s with
      | FullState _ -> true
      | EmptyState | ErrorState _ | ParsingState _ -> false
    in
    if async_proofs_is_master (cur_opt()) && is_full_state_valid then
      !Hooks.state_ready ~doc:dummy_doc (* XXX should be taken in input *) id

  let get_state id = (get_info id).state

  let get_parsing_state id =
    stm_pperr_endline (fun () -> str "retrieve parsing state state " ++ str (Stateid.to_string id) ++ str " }}}");
    match (get_info id).state with
    | FullState s -> Some Vernacstate.(Synterp.parsing s.synterp)
    | ParsingState s -> Some s
    | ErrorState (s,_) -> s
    | EmptyState -> None

  let set_parsing_state id ps =
    let info = get_info id in
    let new_state =
      match info.state with
      | FullState s -> assert false
      | ParsingState s -> assert false
      | ErrorState _ -> assert false
      | EmptyState -> ParsingState ps
    in
    info.state <- new_state

  let get_proof_mode id = (get_info id).proof_mode

  let reached id =
    let info = get_info id in
    info.n_reached <- info.n_reached + 1
  let goals id n = (get_info id).n_goals <- n
  let cur_tip () = get_branch_pos (current_branch ())

  let proof_nesting () = Vcs_aux.proof_nesting !vcs

  let checkout_shallowest_proof_branch () =
    if List.mem edit_branch (Vcs_.branches !vcs) then begin
      checkout edit_branch
    end else
      let pl = proof_nesting () in
      try
        let branch = fst @@ Vcs_aux.find_proof_at_depth !vcs pl in
        checkout branch
      with Failure _ ->
        checkout Branch.master

  (* copies the transaction on every open branch *)
  let propagate_sideff ~action =
    List.map (fun b ->
      checkout b;
      let proof_mode = get_proof_mode @@ get_branch_pos b in
      let id = new_node proof_mode () in
      merge id ~ours:(Sideff action) ~into:b Branch.master;
      id)
    (List.filter (fun b -> not (Branch.equal b Branch.master)) (branches ()))

  let propagate_qed () =
    List.iter (fun b ->
      checkout b;
      let proof_mode = get_proof_mode @@ get_branch_pos b in
      let id = new_node proof_mode () in
      let parsing = Option.get @@ get_parsing_state (get_branch_pos b) in
      merge id ~ours:(Sideff CherryPickEnv) ~into:b Branch.master;
      set_parsing_state id parsing)
    (List.filter (fun b -> not (Branch.equal b Branch.master)) (branches ()))

  let visit id = Vcs_aux.visit !vcs id

  let nodes_in_slice ~block_start ~block_stop =
    let rec aux id =
      if Stateid.equal id block_start then [] else
      match visit id with
      | { next = n; step = SCmd x } -> (id,Cmd x) :: aux n
      | { next = n; step = SAlias x } -> (id,Alias x) :: aux n
      | { next = n; step = SSideff (ReplayCommand x,_) } ->
           (id,Sideff (ReplayCommand x)) :: aux n
      | _ -> anomaly Pp.(str("Cannot slice from "^ Stateid.to_string block_start ^
                         " to "^Stateid.to_string block_stop^"."))
    in aux block_stop

  (* [slice] copies a slice of the DAG, keeping only the last known valid state.
     When it copies a state, it drops the libobjects and keeps only the structure. *)
  let slice ~block_start ~block_stop =
    let l = nodes_in_slice ~block_start ~block_stop in
    let copy_info v id =
      let info = get_info id in
      Vcs_.set_info v id
        { info with state = EmptyState;
                    vcs_backup = None,None } in
    let make_shallow = function
      | FullState st -> FullState (Vernacstate.Stm.make_shallow st)
      | x -> x
    in
    let copy_info_w_state v id =
      let info = get_info id in
      Vcs_.set_info v id { info with state = make_shallow info.state; vcs_backup = None,None } in
    let copy_proof_blockes v =
      let nodes = Vcs_.Dag.all_nodes (Vcs_.dag v) in
      let props =
        Stateid.Set.fold (fun n pl -> Vcs_.property_of !vcs n @ pl) nodes [] in
      let props = CList.sort_uniquize Vcs_.Dag.Property.compare props in
      List.fold_left (fun v p ->
        Vcs_.create_property v
          (Stateid.Set.elements (Vcs_.Dag.Property.having_it p))
          (Vcs_.Dag.Property.data p)) v props
    in
    let v = Vcs_.empty block_start in
    let v = copy_info v block_start in
    let v = List.fold_right (fun (id,tr) v ->
      let v = Vcs_.commit v id tr in
      let v = copy_info v id in
      v) l v in
    (* Stm should have reached the beginning of proof *)
    assert (match get_state block_start
            with FullState _ -> true | _  -> false);
    (* We put in the new dag the most recent state known to master *)
    let rec fill id =
      match get_state id with
      | EmptyState | ErrorState _ | ParsingState _ -> fill (Vcs_aux.visit v id).next
      | FullState _ -> copy_info_w_state v id
    in
    let v = fill block_stop in
    (* We put in the new dag the first state (since Qed shall run on it,
     * see check_task_aux) *)
    let v = copy_info_w_state v block_start in
    copy_proof_blockes v

  let nodes_in_slice ~block_start ~block_stop =
    List.rev (List.map fst (nodes_in_slice ~block_start ~block_stop))

  let topo_invariant l =
    let all = List.fold_right Stateid.Set.add l Stateid.Set.empty in
    List.for_all
      (fun x ->
         let props = property_of !vcs x in
         let sets = List.map Dag.Property.having_it props in
         List.for_all (fun s -> Stateid.Set.(subset s all || subset all s)) sets)
      l

  let create_proof_task_box l ~qed ~block_start:lemma =
    if not (topo_invariant l) then anomaly Pp.(str "overlapping boxes.");
    vcs := create_property !vcs l (ProofTask { qed; lemma })
  let create_proof_block ({ block_start; block_stop} as decl) name =
    let l = nodes_in_slice ~block_start ~block_stop in
    if not (topo_invariant l) then anomaly Pp.(str "overlapping boxes.");
    vcs := create_property !vcs l (ProofBlock (decl, name))
  let box_of id = List.map Dag.Property.data (property_of !vcs id)
  let delete_boxes_of id =
    List.iter (fun x -> vcs := delete_property !vcs x) (property_of !vcs id)
  let proof_task_box_of id =
    match
      CList.map_filter (function ProofTask x -> Some x | _ -> None) (box_of id)
    with
    | [] -> None
    | [x] -> Some x
    | _ -> anomaly Pp.(str "node with more than 1 proof task box.")

  let gc () =
    let old_vcs = !vcs in
    let new_vcs, erased_nodes = gc old_vcs in
    Stateid.Set.iter (fun id ->
        match (Vcs_aux.visit old_vcs id).step with
        | SQed ({ fproof = Some (_, cancel_switch) }, _)
        | SCmd { cancel_switch } ->
             cancel_switch := true
        | _ -> ())
      erased_nodes;
    vcs := new_vcs

  module NB : sig (* Non blocking Sys.command *)

    val command : now:bool -> (unit -> unit) -> unit

  end = struct

    let m = Mutex.create ()
    let c = Condition.create ()
    let job = ref None
    let worker = ref None

    let set_last_job j =
      CThread.with_lock m ~scope:(fun () ->
          job := Some j;
          Condition.signal c)

    let get_last_job () =
      CThread.with_lock m ~scope:(fun () ->
          while Option.is_empty !job do Condition.wait c m; done;
          match !job with
          | None -> assert false
          | Some x -> job := None; x)

    let run_command () =
      try while true do get_last_job () () done
      with e -> () (* No failure *)

    let command ~now job =
      if now then job ()
      else begin
        set_last_job job;
        if Option.is_empty !worker then
          worker := Some (CThread.create run_command ())
      end

  end

  let print ?(now=false) () =
    if CDebug.(get_flag misc) then NB.command ~now (print_dag !vcs)

  let backup () = !vcs
  let restore v = vcs := v

end (* }}} *)

type state = Valid of Vernacstate.t option | Expired | Error of exn

let state_of_id ~doc id =
  try match VCS.get_state id with
    | FullState s -> Valid (Some s)
    | ErrorState (_,(e,_)) -> Error e
    | EmptyState | ParsingState _ -> Valid None
  with VCS.Expired -> Expired

let () =
  Stateid.set_is_valid (fun ~doc id -> state_of_id ~doc id <> Expired)

(****** A cache: fills in the nodes of the VCS document with their value ******)
module State : sig

  type t

  val freeze : unit -> t
  val unfreeze : t -> unit

  (** The function is from unit, so it uses the current state to define
      a new one.  I.e. one may been to install the right state before
      defining a new one.
      Warning: an optimization in installed_cached requires that state
      modifying functions are always executed using this wrapper. *)
  val define :
    doc:doc ->
    ?safe_id:Stateid.t ->
    ?redefine:bool -> ?cache:bool ->
    ?feedback_processed:bool -> (unit -> unit) -> Stateid.t -> unit

  val install_cached : Stateid.t -> unit
  (* val install_parsing_state : Stateid.t -> unit *)
  val is_cached : ?cache:bool -> Stateid.t -> bool
  val is_cached_and_valid : ?cache:bool -> Stateid.t -> bool

  val exn_on : Stateid.t -> valid:Stateid.t -> Exninfo.iexn -> Exninfo.iexn

  (* to send states across worker/master *)
  val get_cached : Stateid.t -> Vernacstate.t

  type partial_state =
    | Full of Vernacstate.t
    | ProofOnly of Stateid.t * Vernacstate.Stm.pstate

  val assign : Stateid.t -> partial_state -> unit

  (* Handlers for initial state, prior to document creation. *)
  val register_root_state : unit -> unit
  val restore_root_state : unit -> unit

  val purify : ('a -> 'b) -> 'a -> 'b

end = struct (* {{{ *)

  type t = { id : Stateid.t; vernac_state : Vernacstate.t }

  (* cur_id holds Stateid.dummy in case the last attempt to define a state
   * failed, so the global state may contain garbage *)
  let cur_id = ref Stateid.dummy
  let freeze () = { id = !cur_id; vernac_state = Vernacstate.freeze_full_state () }
  let unfreeze st =
    Vernacstate.unfreeze_full_state st.vernac_state;
    cur_id := st.id

  let invalidate_cur_state () = cur_id := Stateid.dummy

  type partial_state =
    | Full of Vernacstate.t
    | ProofOnly of Stateid.t * Vernacstate.Stm.pstate

  let cache_state id =
    VCS.set_state id (FullState (Vernacstate.freeze_full_state ()))

  let freeze_invalid id iexn =
    let ps = VCS.get_parsing_state id in
    VCS.set_state id (ErrorState (ps,iexn))

  let is_cached ?(cache=false) id only_valid =
    if Stateid.equal id !cur_id then
      try match VCS.get_info id with
        | ({ state = EmptyState } | { state = ParsingState _ }) when cache -> cache_state id; true
        | _ -> true
      with VCS.Expired -> false
    else
      try match VCS.get_state id with
        | EmptyState | ParsingState _ -> false
        | FullState _ -> true
        | ErrorState _ -> not only_valid
      with VCS.Expired -> false

  let is_cached_and_valid ?cache id = is_cached ?cache id true
  let is_cached ?cache id = is_cached ?cache id false

  let install_cached id =
    match VCS.get_state id with
    | FullState s ->
       Vernacstate.unfreeze_full_state s;
       cur_id := id

    | ErrorState (_,ie) ->
       Exninfo.iraise ie

    | EmptyState | ParsingState _ ->
      (* coqc has a 1 slot cache and only for valid states *)
      if (VCS.is_interactive ()) || not (Stateid.equal id !cur_id) then
        anomaly Pp.(str "installing a non cached state.")

  (*
  let install_parsing_state id =
    if not (Stateid.equal id !cur_id) then begin
      Vernacstate.Parser.install @@ VCS.get_parsing_state id
    end
     *)

  let get_cached id =
    try match VCS.get_state id with
    | FullState s -> s
    | _ -> anomaly Pp.(str "not a cached state.")
    with VCS.Expired -> anomaly Pp.(str "not a cached state (expired).")

  let assign id what =
    if VCS.get_state id <> EmptyState then () else
    try match what with
    | Full s ->
         let s =
           try
            let prev = (VCS.visit id).next in
            if is_cached_and_valid prev
            then
              let open Vernacstate in
              { s with interp = { s.interp with
                lemmas = PG_compat.copy_terminators
                           ~src:((get_cached prev).interp.lemmas) ~tgt:s.interp.lemmas }}
            else s
           with VCS.Expired -> s in
         VCS.set_state id (FullState s)
    | ProofOnly(ontop,pstate) ->
         if is_cached_and_valid ontop then
           let s = get_cached ontop in
           let s = Vernacstate.Stm.set_pstate s pstate in
           VCS.set_state id (FullState s)
    with VCS.Expired -> ()

  let exn_on id ~valid (e, info) =
    match Stateid.get info with
    | Some _ -> (e, info)
    | None ->
        let loc = Loc.get_loc info in
        execution_error ?loc id (iprint (e, info));
        (e, Stateid.add info ~valid id)

  (* [define] puts the system in state [id] calling [f ()] *)
  (* [safe_id] is the last known valid state before execution *)
  let define ~doc ?safe_id ?(redefine=false) ?(cache=false) ?(feedback_processed=true)
        f id
  =
    feedback ~id:id (ProcessingIn !Flags.async_proofs_worker_id);
    let str_id = Stateid.to_string id in
    if is_cached id && not redefine then
      anomaly Pp.(str"defining state "++str str_id++str" twice.");
    try
      stm_prerr_endline (fun () -> "defining "^str_id^" (cache="^
        if cache then "Y)" else "N)");
      f ();
      if cache then cache_state id;
      stm_prerr_endline (fun () -> "setting cur id to "^str_id);
      cur_id := id;
      if feedback_processed then
        !Hooks.state_computed~doc id ~in_cache:false;
      VCS.reached id;
      if PG_compat.there_are_pending_proofs () then
        VCS.goals id (PG_compat.get_open_goals ())
    with e ->
      let (e, info) = Exninfo.capture e in
      let good_id = !cur_id in
      invalidate_cur_state ();
      VCS.reached id;
      let ie =
        match Stateid.get info, safe_id with
        | None, None -> (exn_on id ~valid:good_id (e, info))
        | None, Some good_id -> (exn_on id ~valid:good_id (e, info))
        | Some _, None -> (e, info)
        | Some (_,at), Some id -> (e, Stateid.add info ~valid:id at) in
      if cache then freeze_invalid id ie;
      !Hooks.unreachable_state ~doc id ie;
      Exninfo.iraise ie

  let init_state = ref None

  let register_root_state () =
    init_state := Some (Vernacstate.freeze_full_state ())

  let restore_root_state () =
    cur_id := Stateid.dummy;
    Vernacstate.unfreeze_full_state (Option.get !init_state)

  (* Protect against state changes *)
  let purify f x =
    let st = freeze () in
    try
      let res = f x in
      Vernacstate.Interp.invalidate_cache ();
      unfreeze st;
      res
    with e ->
      let e = Exninfo.capture e in
      Vernacstate.Interp.invalidate_cache ();
      unfreeze st;
      Exninfo.iraise e

end (* }}} *)

(* Wrapper for the proof-closing special path for Qed *)
let stm_qed_delay_proof ?route ~proof ~id ~st ~loc ~control pending : Vernacstate.Interp.t =
  set_id_for_feedback ?route dummy_doc id;
  Vernacinterp.interp_qed_delayed_proof ~proof ~st ~control (CAst.make ?loc pending)

(* Wrapper for Vernacentries.interp to set the feedback id *)
(* It is currently called 19 times, this number should be certainly
   reduced... *)
let stm_vernac_interp ?route id st { verbose; expr } : Vernacstate.t =
  (* The Stm will gain the capability to interpret commmads affecting
     the whole document state, such as backtrack, etc... so we start
     to design the stm command interpreter now *)
  set_id_for_feedback ?route dummy_doc id;
  Aux_file.record_in_aux_set_at ?loc:expr.CAst.loc ();
  (* We need to check if a command should be filtered from
   * vernac_entries, as it cannot handle it. This should go away in
   * future refactorings.
  *)
  let is_filtered_command = function
    VernacSynPure (VernacResetName _ | VernacResetInitial | VernacBack _
    | VernacRestart | VernacUndo _ | VernacUndoTo _
    | VernacAbortAll) -> true
    | _ -> false
  in
  (* XXX unsupported attributes *)
  let cmd = expr.CAst.v.expr in
  if is_filtered_command cmd then
    (stm_pperr_endline Pp.(fun () -> str "ignoring " ++ Ppvernac.pr_vernac expr); st)
  else begin
    stm_pperr_endline Pp.(fun () -> str "interpreting " ++ Ppvernac.pr_vernac expr);
    Vernacinterp.(interp ~intern:fs_intern ?verbosely:(Some verbose) ~st expr)
  end

(****************************** CRUFT *****************************************)
(******************************************************************************)

(* The backtrack module simulates the classic behavior of a linear document *)
module Backtrack : sig

  val record : unit -> unit

  (* we could navigate the dag, but this ways easy *)
  val branches_of : Stateid.t -> backup

  (* Returns the state that the command should backtract to *)
  val undo_vernac_classifier : vernac_control -> doc:doc -> Stateid.t
  val get_prev_proof : doc:doc -> Stateid.t -> Proof.t option
  val get_proof : doc:doc -> Stateid.t -> Proof.t option

end = struct (* {{{ *)

  let record () =
    List.iter (fun current_branch ->
      let mine = current_branch, VCS.get_branch current_branch in
      let info = VCS.get_info (VCS.get_branch_pos current_branch) in
      let others =
        CList.map_filter (fun b ->
          if Vcs_.Branch.equal b current_branch then None
          else Some(b, VCS.get_branch b)) (VCS.branches ()) in
      let backup = if fst info.vcs_backup <> None then fst info.vcs_backup
        else Some (VCS.backup ()) in
      let branches = if snd info.vcs_backup <> None then snd info.vcs_backup
        else Some { mine; others } in
      info.vcs_backup <- backup, branches)
    [VCS.current_branch (); VCS.Branch.master]

  let branches_of id =
    let info = VCS.get_info id in
    match info.vcs_backup with
    | _, None ->
       anomaly Pp.(str"Backtrack.branches_of "++str(Stateid.to_string id)++
                   str": a state with no vcs_backup.")
    | _, Some x -> x

  type ('a, 'b) cont = Stop of 'a | Cont of 'b

  let rec fold_until f acc id =
    let next acc =
      if id = Stateid.initial then raise Not_found
      else fold_until f acc (VCS.visit id).next in
    let info = VCS.get_info id in
    match info.vcs_backup with
    | None, _ -> next acc
    | Some vcs, _ ->
        let ids, tactic, undo =
          if id = Stateid.initial || id = Stateid.dummy then [],false,0 else
          match VCS.visit id with
          | { step = SFork ((_,_,_,l),_) } -> l, false,0
          | { step = SCmd { cids = l; ctac } } -> l, ctac,0
          | { step = SAlias (_,{ expr }) } when not (Vernacprop.has_query_control expr) ->
          begin match expr.CAst.v.expr with
                | VernacSynPure (VernacUndo n) -> [], false, n
                | _ -> [],false,0
          end
          | _ -> [],false,0 in
        match f acc (id, vcs, ids, tactic, undo) with
        | Stop x -> x
        | Cont acc -> next acc

  let undo_costly_in_batch_mode =
    CWarnings.create ~name:"undo-batch-mode" Pp.(fun v ->
        str "Command" ++ spc() ++ quote (Ppvernac.pr_vernac v) ++
        strbrk (" is not recommended in batch mode. In particular, going back in the document" ^
             " is not efficient in batch mode due to Coq not caching previous states for memory optimization reasons." ^
             " If your use is intentional, you may want to disable this warning and pass" ^
             " the \"-async-proofs-cache force\" option to Coq."))

  let back_tactic n (id,_,_,tactic,undo) =
    let value = (if tactic then 1 else 0) - undo in
    if Int.equal n 0 then Stop id else Cont (n-value)

  let get_proof ~doc id =
    match state_of_id ~doc id with
    | Valid (Some vstate) ->
      Option.map (Vernacstate.LemmaStack.with_top ~f:Declare.Proof.get) vstate.Vernacstate.interp.lemmas
    | _ -> None

  let undo_vernac_classifier v ~doc =
    if not (VCS.is_interactive ()) && (cur_opt()).async_proofs_cache <> Some Force
    then undo_costly_in_batch_mode v;
    try
      match v.CAst.v.expr with
      | VernacSynPure VernacResetInitial ->
          Stateid.initial
      | VernacSynPure (VernacResetName {CAst.v=name}) ->
          let id = VCS.cur_tip () in
          (try
            let oid =
              fold_until (fun b (id,_,label,_,_) ->
                if b then Stop id else Cont (List.mem name label))
              false id in
            oid
          with Not_found ->
            id)
      | VernacSynPure (VernacBack n) ->
          let id = VCS.cur_tip () in
          let oid = fold_until (fun n (id,_,_,_,_) ->
            if Int.equal n 0 then Stop id else Cont (n-1)) n id in
          oid
      | VernacSynPure (VernacUndo n) ->
          let id = VCS.cur_tip () in
          let oid = fold_until back_tactic n id in
          oid
      | VernacSynPure (VernacUndoTo _
        | VernacRestart as e) ->
          let m = match e with VernacUndoTo m -> m | _ -> 0 in
          let id = VCS.cur_tip () in
          let vcs =
            match (VCS.get_info id).vcs_backup with
            | None, _ -> anomaly Pp.(str"Backtrack: tip with no vcs_backup.")
            | Some vcs, _ -> vcs in
          let cb, _ =
            try Vcs_aux.find_proof_at_depth vcs (Vcs_aux.proof_nesting vcs)
            with Failure _ -> raise PG_compat.NoCurrentProof in
          let n = fold_until (fun n (_,vcs,_,_,_) ->
            if List.mem cb (Vcs_.branches vcs) then Cont (n+1) else Stop n)
            0 id in
          let oid = fold_until (fun n (id,_,_,_,_) ->
            if Int.equal n 0 then Stop id else Cont (n-1)) (n-m-1) id in
          oid
      | VernacSynPure VernacAbortAll ->
          let id = VCS.cur_tip () in
          let oid = fold_until (fun () (id,vcs,_,_,_) ->
            match Vcs_.branches vcs with [_] -> Stop id | _ -> Cont ())
            () id in
          oid
      | _ -> anomaly Pp.(str "incorrect VtMeta classification")
    with
    | Not_found ->
       CErrors.user_err
        Pp.(str "Cannot undo.")

  let get_prev_proof ~doc id =
    try
      let np = get_proof ~doc id in
      match np with
      | None -> None
      | Some cp ->
        let rec search did =
          let did = fold_until back_tactic 1 did in
          match get_proof ~doc did with
          | None -> None
          | Some rv ->
            if Evar.Set.equal (Proof.all_goals rv) (Proof.all_goals cp)
            then search did
            else Some rv
        in
        search id
    with Not_found | PG_compat.NoCurrentProof -> None

end (* }}} *)

let get_prev_proof = Backtrack.get_prev_proof
let get_proof = Backtrack.get_proof

let hints = ref Aux_file.empty_aux_file
let set_compilation_hints file =
  hints := Aux_file.load_aux_file_for file

let get_hint_ctx loc =
  let s = Aux_file.get ?loc !hints "context_used" in
  let ids = List.map Names.Id.of_string (Str.split (Str.regexp " ") s) in
  let ids = List.map (fun id -> CAst.make id) ids in
  match ids with
  | [] -> SsEmpty
  | x :: xs ->
    List.fold_left (fun a x -> SsUnion (SsSingl x,a)) (SsSingl x) xs

let get_hint_bp_time proof_name =
  try float_of_string (Aux_file.get !hints proof_name)
  with Not_found -> 1.0

let record_pb_time ?loc proof_name time =
  let proof_build_time = Printf.sprintf "%.3f" time in
  Aux_file.record_in_aux_at ?loc "proof_build_time" proof_build_time;
  if proof_name <> "" then begin
    Aux_file.record_in_aux_at proof_name proof_build_time;
    hints := Aux_file.set !hints proof_name proof_build_time
  end

(****************** proof structure for error recovery ************************)
(******************************************************************************)

type document_node = {
  indentation : int;
  ast : Vernacexpr.vernac_control;
  id : Stateid.t;
}

type document_view = {
  entry_point : document_node;
  prev_node : document_node -> document_node option;
}

type static_block_detection =
  document_view -> static_block_declaration option

type recovery_action = {
  base_state : Stateid.t;
  goals_to_admit : Evar.t list;
  recovery_command : Vernacexpr.vernac_control option;
}

type block_classification = ValidBlock of recovery_action | Leaks

type dynamic_block_error_recovery =
  doc -> static_block_declaration -> block_classification

let proof_block_delimiters = ref []

let register_proof_block_delimiter name static dynamic =
  if List.mem_assoc name !proof_block_delimiters then
    CErrors.user_err Pp.(str "Duplicate block delimiter " ++ str name ++ str ".");
  proof_block_delimiters := (name, (static,dynamic)) :: !proof_block_delimiters

let mk_doc_node id = function
  | { step = SCmd { ctac; cast = { indentation; expr }}; next } when ctac ->
       Some { indentation; ast = expr; id }
  | { step = SSideff (ReplayCommand { indentation; expr }, _); next } ->
       Some { indentation; ast = expr; id }
  | _ -> None
let prev_node { id } =
  let id = (VCS.visit id).next in
  mk_doc_node id (VCS.visit id)
let cur_node id = mk_doc_node id (VCS.visit id)

let is_block_name_enabled name =
  match (cur_opt()).async_proofs_tac_error_resilience with
  | FNone -> false
  | FAll -> true
  | FOnly l -> List.mem name l

let detect_proof_block id name =
  let name = match name with None -> "indent" | Some x -> x in
  if is_block_name_enabled name &&
     (async_proofs_is_master (cur_opt()) || Flags.async_proofs_is_worker ())
  then (
  match cur_node id with
  | None -> ()
  | Some entry_point -> try
      let static, _ = List.assoc name !proof_block_delimiters in
      begin match static { prev_node; entry_point } with
      | None -> ()
      | Some ({ block_start; block_stop } as decl) ->
          VCS.create_proof_block decl name
      end
    with Not_found ->
      CErrors.user_err
        Pp.(str "Unknown proof block delimiter " ++ str name ++ str ".")
  )
(****************************** THE SCHEDULER *********************************)
(******************************************************************************)

(* Unused module warning doesn't understand [module rec] *)
[@@@ocaml.warning "-60"]
module rec ProofTask : sig

  type competence = Stateid.t list
  type task_build_proof = {
    t_exn_info : Stateid.exn_info;
    t_start    : Stateid.t;
    t_stop     : Stateid.t;
    t_drop     : bool;
    t_states   : competence;
    t_assign   : Declare.Proof.closed_proof_output option Future.assignment -> unit;
    t_loc      : Loc.t option;
    t_uuid     : Future.UUID.t;
    t_name     : string }

  type task =
    | BuildProof of task_build_proof
    | States of Stateid.t list

  type request =
  | ReqBuildProof of (Future.UUID.t,VCS.vcs) Stateid.request * bool * competence
  | ReqStates of Stateid.t list

  include AsyncTaskQueue.Task
  with type task := task
   and type competence := competence
   and type request := request

  val build_proof_here :
    doc:doc ->
    ?loc:Loc.t ->
    drop_pt:bool ->
    Stateid.exn_info -> Stateid.t ->
      Declare.Proof.closed_proof_output option Future.computation

end = struct (* {{{ *)

  let forward_feedback msg = !Hooks.forward_feedback msg

  type competence = Stateid.t list
  type task_build_proof = {
    t_exn_info : Stateid.exn_info;
    t_start    : Stateid.t;
    t_stop     : Stateid.t;
    t_drop     : bool;
    t_states   : competence;
    t_assign   : Declare.Proof.closed_proof_output option Future.assignment -> unit;
    t_loc      : Loc.t option;
    t_uuid     : Future.UUID.t;
    t_name     : string }

  type task =
    | BuildProof of task_build_proof
    | States of Stateid.t list

  type worker_status = Fresh | Old of competence

  type request =
  | ReqBuildProof of (Future.UUID.t,VCS.vcs) Stateid.request * bool * competence
  | ReqStates of Stateid.t list

  type error = {
    e_error_at    : Stateid.t;
    e_safe_id     : Stateid.t;
    e_msg         : Pp.t;
    e_loc         : Loc.t option;
    e_safe_states : Stateid.t list }

  type response =
    | RespBuiltProof of Declare.Proof.closed_proof_output option * float
    | RespError of error
    | RespStates of (Stateid.t * State.partial_state) list

  let name = "proof"
  let extra_env () = !async_proofs_workers_extra_env

  let task_match age t =
    match age, t with
    | Fresh, BuildProof { t_states } -> true
    | Old my_states, States l ->
        List.for_all (fun x -> CList.mem_f Stateid.equal x my_states) l
    | _ -> false

  let name_of_task = function
    | BuildProof t -> "proof: " ^ t.t_name
    | States l -> "states: " ^ String.concat "," (List.map Stateid.to_string l)
  let name_of_request = function
    | ReqBuildProof(r,_,_) -> "proof: " ^ r.Stateid.name
    | ReqStates l -> "states: "^String.concat "," (List.map Stateid.to_string l)

  let request_of_task age = function
    | States l -> Some (ReqStates l)
    | BuildProof {
        t_exn_info;t_start;t_stop;t_loc;t_uuid;t_name;t_states;t_drop
      } ->
        assert(age = Fresh);
        try Some (ReqBuildProof ({
          Stateid.exn_info = t_exn_info;
          stop = t_stop;
          document = VCS.slice ~block_start:t_start ~block_stop:t_stop;
          loc = t_loc;
          uuid = t_uuid;
          name = t_name }, t_drop, t_states))
        with VCS.Expired -> None

  let use_response (s : worker_status) t r =
    match s, t, r with
    | Old c, States _, RespStates l ->
        List.iter (fun (id,s) -> State.assign id s) l; `End
    | Fresh, BuildProof { t_assign; t_loc; t_name; t_states; t_drop },
              RespBuiltProof (pl, time) ->
        feedback (InProgress ~-1);
        t_assign (`Val pl);
        record_pb_time ?loc:t_loc t_name time;
        if t_drop then `Stay(t_states,[States t_states])
        else `End
    | Fresh, BuildProof { t_assign; t_loc; t_name; t_states },
            RespError { e_error_at; e_safe_id = valid; e_loc; e_msg; e_safe_states } ->
        feedback (InProgress ~-1);
        let info = match e_loc with
          | Some loc -> Loc.add_loc Exninfo.null loc
          | None -> Exninfo.null
        in
        let info = Stateid.add ~valid info e_error_at in
        let e = (AsyncTaskQueue.RemoteException e_msg, info) in
        t_assign (`Exn e);
        `Stay(t_states,[States e_safe_states])
    | _ -> assert false

  let on_task_cancellation_or_expiration_or_slave_death = function
    | None -> ()
    | Some (States _) -> ()
    | Some (BuildProof { t_start = start; t_assign }) ->
        let s = "Worker dies or task expired" in
        let info = Stateid.add ~valid:start Exninfo.null start in
        let e = (AsyncTaskQueue.RemoteException (Pp.strbrk s), info) in
        t_assign (`Exn e);
        execution_error start (Pp.strbrk s);
        feedback (InProgress ~-1)

  let build_proof_here_fun ~doc ?loc ~drop_pt ~id eop =
    let wall_clock1 = Unix.gettimeofday () in
    Reach.known_state ~doc ~cache:(VCS.is_interactive ()) eop;
    let wall_clock2 = Unix.gettimeofday () in
    Aux_file.record_in_aux_at ?loc "proof_build_time"
      (Printf.sprintf "%.3f" (wall_clock2 -. wall_clock1));
    let p = if drop_pt then None else Some (PG_compat.return_proof ()) in
    if drop_pt then feedback ~id Complete;
    p

  let build_proof_here ~doc ?loc ~drop_pt exn_info eop =
    Future.create ~fix_exn:(Some exn_info) (fun () -> build_proof_here_fun ~doc ?loc ~drop_pt ~id:exn_info.Stateid.id eop)

  let perform_buildp { Stateid.exn_info; stop; document; loc } drop my_states =
    try
      VCS.restore document;
      VCS.print ();
      let proof, time =
        let wall_clock = Unix.gettimeofday () in
        let proof =
          try
            build_proof_here_fun ~doc:dummy_doc (* XXX should be document *)
              ?loc ~drop_pt:drop ~id:exn_info.Stateid.id stop
          with exn ->
            let iexn = Exninfo.capture exn in
            let iexn = State.exn_on exn_info.Stateid.id ~valid:exn_info.Stateid.valid iexn in
            Exninfo.iraise iexn
        in
        proof, Unix.gettimeofday () -. wall_clock in
      (* We typecheck the proof with the kernel (in the worker) to spot
       * the few errors tactics don't catch, like the "fix" tactic building
       * a bad fixpoint *)
      (* STATE: We use the current installed imperative state *)
      let st = State.freeze () in
      let () = match proof with
        | None -> (* drop *) ()
        | Some proof ->
          (* Unfortunately close_future_proof and friends are not pure so we need
             to set the state manually here *)
          State.unfreeze st;
          let pobject =
            PG_compat.close_future_proof ~feedback_id:stop (Future.from_val proof) in

          let st = Vernacstate.freeze_full_state () in
          let opaque = Opaque in
          try
            let _pstate =
              stm_qed_delay_proof ~st ~id:stop
                ~proof:pobject ~loc ~control:[] (Proved (opaque,None)) in
            ()
          with exn ->
            (* If [stm_qed_delay_proof] fails above we need to use the
               exn callback in the same way than build_proof_here;
               actually [fix_exn] there does more more than just
               modifying exn info, it also updates the STM state *)
            let iexn = Exninfo.capture exn in
            let iexn = State.exn_on exn_info.Stateid.id ~valid:exn_info.Stateid.valid iexn in
            Exninfo.iraise iexn
      in
      (* STATE: Restore the state XXX: handle exn *)
      State.unfreeze st;
      RespBuiltProof(proof,time)
    with
    | e when CErrors.noncritical e || e = Stack_overflow ->
        let e, info = Exninfo.capture e in
        (* This can happen if the proof is broken.  The error has also been
         * signalled as a feedback, hence we can silently recover *)
        let e_error_at, e_safe_id = match Stateid.get info with
          | Some (safe, err) -> err, safe
          | None -> Stateid.dummy, Stateid.dummy in
        let e_msg = iprint (e, info) in
        stm_pperr_endline Pp.(fun () -> str "failed with the following exception: " ++ fnl () ++ e_msg);
        let e_safe_states = List.filter State.is_cached_and_valid my_states in
        RespError { e_error_at; e_safe_id; e_msg; e_loc = Loc.get_loc info; e_safe_states }

  let perform_states query =
    if query = [] then [] else
    let is_tac e = match Vernac_classifier.classify_vernac e with
    | VtProofStep _ -> true
    | _ -> false
    in
    let initial =
      let rec aux id =
        try match VCS.visit id with { next } -> aux next
        with VCS.Expired -> id in
      aux (List.hd query) in
    let get_state seen id =
      let prev =
        try
          let { next = prev; step } = VCS.visit id in
          if State.is_cached_and_valid prev && List.mem prev seen
          then Some (prev, State.get_cached prev, step)
          else None
        with VCS.Expired -> None in
      let this =
        if State.is_cached_and_valid id then Some (State.get_cached id) else None in
      match prev, this with
      | _, None -> None
      | Some (prev, o, SCmd { cast = { expr }}), Some n
        when is_tac expr && Vernacstate.Stm.same_env o n -> (* A pure tactic *)
          Some (id, State.ProofOnly (prev, Vernacstate.Stm.pstate n))
      | Some _, Some s ->
        if CDebug.(get_flag misc) then msg_debug (Pp.str "STM: sending back a fat state");
          Some (id, State.Full s)
      | _, Some s -> Some (id, State.Full s) in
    let rec aux seen = function
      | [] -> []
      | id :: rest ->
          match get_state seen id with
          | None -> aux seen rest
          | Some stuff -> stuff :: aux (id :: seen) rest in
    aux [initial] query

  let perform = function
    | ReqBuildProof (bp,drop,states) -> perform_buildp bp drop states
    | ReqStates sl -> RespStates (perform_states sl)

  let on_marshal_error s = function
    | States _ ->
      msg_warning Pp.(strbrk("Marshalling error: "^s^". "^
                             "The system state could not be sent to the master process."))
    | BuildProof { t_exn_info; t_stop; t_assign; t_loc; t_drop = drop_pt } ->
      msg_warning Pp.(strbrk("Marshalling error: "^s^". "^
                             "The system state could not be sent to the worker process. "^
                             "Falling back to local, lazy, evaluation."));
      t_assign(`Comp(fun () -> build_proof_here_fun ~doc:dummy_doc (* XXX should be stored in a closure, it is the same doc that was used to generate the task *) ?loc:t_loc ~drop_pt ~id:t_exn_info.Stateid.id t_stop));
      feedback (InProgress ~-1)

end (* }}} *)

(* Slave processes (if initialized, otherwise local lazy evaluation) *)
and Slaves : sig

  (* (eventually) remote calls *)
  val build_proof
    : doc:doc
    -> ?loc:Loc.t
    -> drop_pt:bool
    -> exn_info:Stateid.exn_info
    -> block_start:Stateid.t
    -> block_stop:Stateid.t
    -> name:string
    -> unit
    -> future_proof * AsyncTaskQueue.cancel_switch

  (* blocking function that waits for the task queue to be empty *)
  val wait_all_done : unit -> unit

  (* initialize the whole machinery (optional) *)
  val init : CoqworkmgrApi.priority -> unit

  type 'a tasks = (('a,VCS.vcs) Stateid.request * bool) list
  val dump_snapshot : unit -> Future.UUID.t tasks

  val cancel_worker : WorkerPool.worker_id -> unit

  val reset_task_queue : unit -> unit

end = struct (* {{{ *)

  module TaskQueue = AsyncTaskQueue.MakeQueue(ProofTask) ()

  let queue = ref None
  let init priority =
    if async_proofs_is_master (cur_opt()) then
      queue := Some (TaskQueue.create (cur_opt()).async_proofs_n_workers priority)
    else
      queue := Some (TaskQueue.create 0 priority)

  let build_proof ~doc ?loc ~drop_pt ~exn_info ~block_start ~block_stop ~name:pname () =
    let cancel_switch = ref false in
    let n_workers = TaskQueue.n_workers (Option.get !queue) in
    if Int.equal n_workers 0 && not (VCS.is_vos_doc ()) then
      ProofTask.build_proof_here ~doc ?loc ~drop_pt exn_info block_stop, cancel_switch
    else
      let f, t_assign = Future.create_delegate ~name:pname (Some exn_info) in
      let t_uuid = Future.uuid f in
      if n_workers > 0 then feedback (InProgress 1);
      let task = ProofTask.(BuildProof {
        t_exn_info = exn_info; t_start = block_start; t_stop = block_stop; t_assign; t_drop = drop_pt;
        t_loc = loc; t_uuid; t_name = pname;
        t_states = VCS.nodes_in_slice ~block_start ~block_stop }) in
      TaskQueue.enqueue_task (Option.get !queue) task ~cancel_switch;
      f, cancel_switch

  let wait_all_done () = TaskQueue.join (Option.get !queue)

  let cancel_worker n = TaskQueue.cancel_worker (Option.get !queue) n

  (* For external users this name is nicer than request *)
  type 'a tasks = (('a,VCS.vcs) Stateid.request * bool) list
  let dump_snapshot () =
    let tasks = TaskQueue.snapshot (Option.get !queue) in
    let reqs =
      CList.map_filter
        ProofTask.(fun x ->
             match request_of_task Fresh x with
             | Some (ReqBuildProof (r, b, _)) -> Some(r, b)
             | _ -> None)
        tasks in
    stm_prerr_endline (fun () -> Printf.sprintf "dumping %d tasks\n" (List.length reqs));
    reqs

  let reset_task_queue () = TaskQueue.clear (Option.get !queue)

end (* }}} *)

and QueryTask : sig

  type task = { t_where : Stateid.t; t_for : Stateid.t ; t_what : aast }
  include AsyncTaskQueue.Task with type task := task

end = struct (* {{{ *)

  type task =
    { t_where : Stateid.t; t_for : Stateid.t ; t_what : aast }

  type request =
    { r_where : Stateid.t ; r_for : Stateid.t ; r_what : aast; r_doc : VCS.vcs }
  type response = unit

  let name = "query"
  let extra_env _ = [||]
  type competence = unit
  type worker_status = Fresh | Old of competence

  let task_match _ _ = true

  let request_of_task _ { t_where; t_what; t_for } =
    try Some {
      r_where = t_where;
      r_for   = t_for;
      r_doc   = VCS.slice ~block_start:t_where ~block_stop:t_where;
      r_what  = t_what }
    with VCS.Expired -> None

  let use_response _ _ _ = `End

  let on_marshal_error _ _ =
    stm_pr_err ("Fatal marshal error in query");
    flush_all (); exit 1

  let on_task_cancellation_or_expiration_or_slave_death _ = ()

  let forward_feedback msg = !Hooks.forward_feedback msg

  let perform { r_where; r_doc; r_what; r_for } =
    VCS.restore r_doc;
    VCS.print ();
    Reach.known_state ~doc:dummy_doc (* XXX should be r_doc *) ~cache:false r_where;
    (* STATE *)
    let st = Vernacstate.freeze_full_state () in
    try
      (* STATE SPEC:
       * - start: r_where
       * - end  : after execution of r_what
       *)
      ignore(stm_vernac_interp r_for st { r_what with verbose = true });
      feedback ~id:r_for Processed
    with e when CErrors.noncritical e ->
      let e,_ as ie = Exninfo.capture e in
      let msg = iprint ie in
      let qf = Result.value ~default:[] (Quickfix.from_exception e) in
      feedback ~id:r_for (Message (Error, None, qf, msg))

  let name_of_task { t_what } = string_of_ppcmds (pr_ast t_what)
  let name_of_request { r_what } = string_of_ppcmds (pr_ast r_what)

end (* }}} *)

and Query : sig

  val init : CoqworkmgrApi.priority -> unit

end = struct (* {{{ *)

  module TaskQueue = AsyncTaskQueue.MakeQueue(QueryTask) ()

  let queue = ref None

  let init priority = queue := Some (TaskQueue.create 0 priority)

end (* }}} *)

(* Runs all transactions needed to reach a state *)
and Reach : sig

  val known_state :
    doc:doc -> ?redefine_qed:bool -> cache:bool ->
      Stateid.t -> unit

end = struct (* {{{ *)

let async_policy () =
  if Attributes.is_universe_polymorphism () then false (* FIXME this makes no sense, it is the default value of the attribute *)
  else if VCS.is_interactive () then
    (async_proofs_is_master (cur_opt()) || (cur_opt()).async_proofs_mode = APonLazy)
  else
    (VCS.is_vos_doc () || (cur_opt()).async_proofs_mode <> APoff)

let delegate name =
     get_hint_bp_time name >= (cur_opt()).async_proofs_delegation_threshold
  || VCS.is_vos_doc ()

type reason =
| Aborted
| Alias
| AlreadyEvaluated
| Doesn'tGuaranteeOpacity
| Immediate
| MutualProofs
| NestedProof
| NoPU_NoHint_NoES
| Policy
| Print
| Transparent
| Unknown

type sync_kind =
| Sync of string * reason
| ASync of Stateid.t * Stateid.t list * string * bool
| MaybeASync of Stateid.t * Stateid.t list * string * bool

let collect_proof keep cur hd brkind id =
 stm_prerr_endline (fun () -> "Collecting proof ending at "^Stateid.to_string id);
 let no_name = "" in
 let name = function
   | [] -> no_name
   | id :: _ -> Names.Id.to_string id in
 let loc = (snd cur).expr.CAst.loc in
 let is_defined_expr = function
   | VernacSynPure (VernacEndProof (Proved (Transparent,_))) -> true
   | _ -> false in
 let is_defined = function
   | _, { expr = e } -> is_defined_expr e.CAst.v.expr
                        && (not (Vernacprop.has_query_control e)) in
 let has_default_proof_using = Option.has_some (Proof_using.get_default_proof_using ()) in
 let proof_using_ast = function
   | VernacSynPure(VernacProof(_,Some _)) -> true
   | VernacSynPure(VernacProof(_,None)) -> has_default_proof_using
   | _ -> false
 in
 let proof_using_ast = function
   | Some (_, v) when proof_using_ast v.expr.CAst.v.expr
                      && (not (Vernacprop.has_query_control v.expr)) -> Some v
   | _ -> None in
 let has_proof_using x = proof_using_ast x <> None in
 let proof_no_using = function
   | VernacSynPure (VernacProof(t,None)) -> if has_default_proof_using then None else t
   | _ -> assert false
 in
 let proof_no_using = function
   | Some (_, v) -> proof_no_using v.expr.CAst.v.expr, v
   | _ -> assert false in
 let has_proof_no_using = function
   | VernacSynPure (VernacProof(_,None)) -> not has_default_proof_using
   | _ -> false
 in
 let has_proof_no_using = function
   | Some (_, v) -> has_proof_no_using v.expr.CAst.v.expr
                    && (not (Vernacprop.has_query_control v.expr))
   | _ -> false in
 let too_complex_to_delegate = function
   VernacSynterp (VernacDeclareModule _
    | VernacDefineModule _
    | VernacDeclareModuleType _
    | VernacInclude _
    | VernacRequire _
    | VernacImport _) -> true
   | ast -> may_pierce_opaque ast in
 let parent = function Some (p, _) -> p | None -> assert false in
 let is_empty = function ASync(_,[],_,_) | MaybeASync(_,[],_,_) -> true | _ -> false in
 let rec collect last accn id =
    let view = VCS.visit id in
    match view.step with
    | (SSideff (ReplayCommand x,_) | SCmd { cast = x })
      when too_complex_to_delegate x.expr.CAst.v.expr ->
       Sync(no_name,Print)
    | SCmd { cast = x } -> collect (Some (id,x)) (id::accn) view.next
    | SSideff (ReplayCommand x,_) -> collect (Some (id,x)) (id::accn) view.next
    (* An Alias could jump everywhere... we hope we can ignore it*)
    | SAlias _ -> Sync (no_name,Alias)
    | SFork((_,_,_,_::_::_), _) ->
        Sync (no_name,MutualProofs)
    | SFork((_,_,Doesn'tGuaranteeOpacity,_), _) ->
        Sync (no_name,Doesn'tGuaranteeOpacity)
    | SFork((_,hd',GuaranteesOpacity,ids), _) when has_proof_using last ->
        assert (VCS.Branch.equal hd hd' || VCS.Branch.equal hd VCS.edit_branch);
        let name = name ids in
        ASync (parent last,accn,name,delegate name)
    | SFork((_, hd', GuaranteesOpacity, ids), _) when
       has_proof_no_using last && not (State.is_cached_and_valid (parent last)) &&
       VCS.is_vos_doc () ->
        assert (VCS.Branch.equal hd hd'||VCS.Branch.equal hd VCS.edit_branch);
        (try
          let name, hint = name ids, get_hint_ctx loc  in
          let t, v = proof_no_using last in
          v.expr <- CAst.map (fun _ -> { control = []; attrs = []; expr = VernacSynPure (VernacProof(t, Some hint))}) v.expr;
          ASync (parent last,accn,name,delegate name)
        with Not_found ->
          let name = name ids in
          MaybeASync (parent last, accn, name, delegate name))
    | SFork((_, hd', GuaranteesOpacity, ids), _) ->
        assert (VCS.Branch.equal hd hd' || VCS.Branch.equal hd VCS.edit_branch);
        let name = name ids in
        MaybeASync (parent last, accn, name, delegate name)
    | SSideff (CherryPickEnv,_) ->
        Sync (no_name,NestedProof)
    | SQed _ -> Sync (no_name,Unknown)
 in
 let make_sync why = function
   | Sync(name,_) -> Sync (name,why)
   | MaybeASync(_,_,name,_) -> Sync (name,why)
   | ASync(_,_,name,_) -> Sync (name,why) in

 let check_policy rc = if async_policy () then rc else make_sync Policy rc in
 let is_vernac_exact = function
   | VernacSynPure (VernacExactProof _) -> true
   | _ -> false
 in
 match cur, (VCS.visit id).step, brkind with
 | (parent, x), SFork _, _ when is_vernac_exact x.expr.CAst.v.expr
                                && (not (Vernacprop.has_query_control x.expr)) ->
     Sync (no_name,Immediate)
 | _, _, { VCS.kind = Edit _ }  -> check_policy (collect (Some cur) [] id)
 | _ ->
     if is_defined cur then Sync (no_name,Transparent)
     else if keep == VtDrop then Sync (no_name,Aborted)
     else
       let rc = collect (Some cur) [] id in
       if is_empty rc then make_sync AlreadyEvaluated rc
       else if (is_vtkeep keep) && (not(State.is_cached_and_valid id))
       then check_policy rc
       else make_sync AlreadyEvaluated rc

let string_of_reason = function
  | Transparent -> "non opaque"
  | AlreadyEvaluated -> "proof already evaluated"
  | Policy -> "policy"
  | NestedProof -> "contains nested proof"
  | Immediate -> "proof term given explicitly"
  | Aborted -> "aborted proof"
  | Doesn'tGuaranteeOpacity -> "not a simple opaque lemma"
  | MutualProofs -> "block of mutually recursive proofs"
  | Alias -> "contains Undo-like command"
  | Print -> "contains Print-like command"
  | NoPU_NoHint_NoES -> "no 'Proof using..', no .aux file, inside a section"
  | Unknown -> "unsupported case"

let log_string s = stm_prerr_debug (fun () -> "STM: " ^ s)
let log_processing_async id name = log_string Printf.(sprintf
  "%s: proof %s: asynch" (Stateid.to_string id) name
)
let log_processing_sync id name reason = log_string Printf.(sprintf
  "%s: proof %s: synch (cause: %s)"
  (Stateid.to_string id) name (string_of_reason reason)
)

let wall_clock_last_fork = ref 0.0

let known_state ~doc ?(redefine_qed=false) ~cache id =

  let error_absorbing_tactic id blockname exn =
    (* We keep the static/dynamic part of block detection separate, since
       the static part could be performed earlier.  As of today there is
       no advantage in doing so since no UI can exploit such piece of info *)
    detect_proof_block id blockname;

    let boxes = VCS.box_of id in
    let valid_boxes = CList.map_filter (function
      | ProofBlock ({ block_stop } as decl, name) when Stateid.equal block_stop id ->
          Some (decl, name)
      | _ -> None) boxes in
    assert(List.length valid_boxes < 2);
    if valid_boxes = [] then Exninfo.iraise exn
    else
      let decl, name = List.hd valid_boxes in
      try
        let _, dynamic_check = List.assoc name !proof_block_delimiters in
        match dynamic_check dummy_doc decl with
        | Leaks -> Exninfo.iraise exn
        | ValidBlock { base_state; goals_to_admit; recovery_command } -> begin
           let tac =
             Proofview.Goal.enter begin fun gl ->
               if CList.mem_f Evar.equal
                 (Proofview.Goal.goal gl) goals_to_admit then
             Proofview.give_up else Proofview.tclUNIT ()
              end in
           match (VCS.get_info base_state).state with
           | FullState { Vernacstate.interp = { lemmas } } ->
               Option.iter PG_compat.unfreeze lemmas;
               PG_compat.with_current_proof (fun _ p ->
                 feedback ~id:id Feedback.AddedAxiom;
                 fst (Proof.solve Goal_select.SelectAll None tac p), ());
               (* STATE SPEC:
                * - start: Modifies the input state adding a proof.
                * - end  : maybe after recovery command.
               *)
               (* STATE: We use an updated state with proof *)
               let st = Vernacstate.freeze_full_state () in
               Option.iter (fun expr -> ignore(stm_vernac_interp id st {
                  verbose = true; expr; indentation = 0;
                  strlen = 0 } ))
               recovery_command
           | _ -> assert false
        end
      with Not_found ->
          CErrors.user_err
            (str "Unknown proof block delimiter " ++ str name ++ str ".")
  in

  (* Absorb tactic errors from f () *)
  let resilient_tactic id blockname f =
    if (cur_opt()).async_proofs_tac_error_resilience = FNone ||
       (async_proofs_is_master (cur_opt()) &&
        (cur_opt()).async_proofs_mode = APoff)
    then f ()
    else
      try f ()
      with e when CErrors.noncritical e ->
        let ie = Exninfo.capture e in
        error_absorbing_tactic id blockname ie in
  (* Absorb errors from f x *)
  let resilient_command f x =
    if not (cur_opt()).async_proofs_cmd_error_resilience ||
       (async_proofs_is_master (cur_opt()) &&
        (cur_opt()).async_proofs_mode = APoff)
    then f x
    else
      try f x
      with e when CErrors.noncritical e -> () in

  (* extract proof_ending in qed case, note that `Abort` and `Proof
     term.` could also fail in this case, however that'd be a bug I do
     believe as proof injection shouldn't happen here. *)
  let extract_pe (x : aast) =
    match x.expr.CAst.v.expr with
    | VernacSynPure (VernacEndProof pe) -> x.expr.CAst.v.control, pe
    | _ -> CErrors.anomaly Pp.(str "Non-qed command classified incorrectly") in

  (* ugly functions to process nested lemmas, i.e. hard to reproduce
   * side effects *)
  let inject_non_pstate (s_synterp,l_synterp,s_interp,l_interp) =
    Summary.Synterp.unfreeze_summaries ~partial:true s_synterp;
    Lib.Synterp.unfreeze l_synterp;
    Summary.Interp.unfreeze_summaries ~partial:true s_interp;
    Lib.Interp.unfreeze l_interp;
    if PG_compat.there_are_pending_proofs () then
      PG_compat.update_sigma_univs (Global.universes ())
  in

  let rec pure_cherry_pick_non_pstate safe_id id =
    State.purify (fun id ->
        stm_prerr_endline (fun () -> "cherry-pick non pstate " ^ Stateid.to_string id);
        reach ~safe_id id;
        let st = Vernacstate.freeze_full_state () in
        Vernacstate.Stm.non_pstate st)
      id

  (* traverses the dag backward from nodes being already calculated *)
  and reach ?safe_id ?(redefine_qed=false) ?(cache=cache) id =
    stm_prerr_endline (fun () -> "reaching: " ^ Stateid.to_string id);
    if not redefine_qed && State.is_cached ~cache id then begin
      !Hooks.state_computed ~doc id ~in_cache:true;
      stm_prerr_endline (fun () -> "reached (cache)");
      State.install_cached id
    end else
    let step, cache_step, feedback_processed =
      let view = VCS.visit id in
      match view.step with
      | SAlias (id,_) -> (fun () ->
            reach view.next; reach id
          ), cache, true
      | SCmd { cast = x; cqueue = SkipQueue } -> (fun () ->
            reach view.next), cache, true
      | SCmd { cast = x; ceff = eff; ctac = true; cblock } -> (fun () ->
            resilient_tactic id cblock (fun () ->
              reach view.next;
              let st = Vernacstate.freeze_full_state () in
              ignore(stm_vernac_interp id st x)
            )
          ), eff || cache, true
      | SCmd { cast = x; ceff = eff } -> (fun () ->
          (match (cur_opt()).async_proofs_mode with
           | APon | APonLazy ->
             resilient_command reach view.next
           | APoff -> reach view.next);
          let st = Vernacstate.freeze_full_state () in
          ignore(stm_vernac_interp id st x)
        ), eff || cache, true
      | SFork ((x,_,_,_), None) -> (fun () ->
            resilient_command reach view.next;
            let st = Vernacstate.freeze_full_state () in
            ignore(stm_vernac_interp id st x);
            wall_clock_last_fork := Unix.gettimeofday ()
          ), true, true
      | SFork ((x,_,_,_), Some prev) -> (fun () -> (* nested proof *)
            reach ~cache:true prev;
            reach view.next;

            (try
               let st = Vernacstate.freeze_full_state () in
               ignore(stm_vernac_interp id st x);
            with e when CErrors.noncritical e ->
              let (e, info) = Exninfo.capture e in
              let info = Stateid.add info ~valid:prev id in
              Exninfo.iraise (e, info));
            wall_clock_last_fork := Unix.gettimeofday ()
          ), true, true
      | SQed ({ qast = x; keep; brinfo; brname } as qed, eop) ->
          let rec aux = function
            | ASync (block_start, nodes, name, delegate) -> (fun () ->
                let keep' = get_vtkeep keep in
                let drop_pt = keep' == VtKeepAxiom in
                let block_stop, exn_info, loc = eop, Stateid. { id; valid = eop }, x.expr.CAst.loc in
                log_processing_async id name;
                VCS.create_proof_task_box nodes ~qed:id ~block_start;
                begin match brinfo, qed.fproof with
                | { VCS.kind = Edit _ }, None -> assert false
                | { VCS.kind = Edit (_,_, okeep, _) }, Some (ofp, cancel) ->
                    assert(redefine_qed = true);
                    if okeep <> keep then
                      msg_warning(strbrk("The command closing the proof changed. "
                        ^"The kernel cannot take this into account and will "
                        ^(if not drop_pt then "not check " else "reject ")
                        ^"the "^(if not drop_pt then "new" else "incomplete")
                        ^" proof. Reprocess the command declaring "
                        ^"the proof's statement to avoid that."));
                    let fp, cancel =
                      Slaves.build_proof ~doc
                        ?loc ~drop_pt ~exn_info ~block_start ~block_stop ~name () in
                    Future.replace (Option.get ofp) fp;
                    qed.fproof <- Some (Some fp, cancel);
                    (* We don't generate a new state, but we still need
                     * to install the right one *)
                    State.install_cached id
                | { VCS.kind = Proof _ }, Some _ -> assert false
                | { VCS.kind = Proof _ }, None ->
                    reach ~cache:true block_start;
                    let fp, cancel =
                      if delegate then
                        Slaves.build_proof ~doc
                          ?loc ~drop_pt ~exn_info ~block_start ~block_stop ~name ()
                      else
                        ProofTask.build_proof_here ~doc ?loc
                          ~drop_pt exn_info block_stop, ref false
                    in
                    qed.fproof <- Some (Some fp, cancel);
                    let () = match keep' with
                      | VtKeepAxiom | VtKeepOpaque -> ()
                      | VtKeepDefined ->
                        CErrors.anomaly (Pp.str "Cannot delegate transparent proofs, this is a bug in the STM.")
                    in
                    let fp' = Future.chain fp (function
                        | Some p -> p
                        | None ->
                          CErrors.anomaly Pp.(str "Attempting to force admitted proof contents."))
                    in
                    let proof =
                      PG_compat.close_future_proof ~feedback_id:id fp' in
                    if not delegate then ignore(Future.compute fp);
                    reach view.next;
                    let st = Vernacstate.freeze_full_state () in
                    let control, pe = extract_pe x in
                    ignore(stm_qed_delay_proof ~id ~st ~proof ~loc ~control pe);
                    feedback ~id:id Incomplete
                | { VCS.kind = Master }, _ -> assert false
                end;
                PG_compat.discard_all ()
              ), not redefine_qed, true
          | Sync (name, Immediate) -> (fun () ->
                reach eop;
                let st = Vernacstate.freeze_full_state () in
                ignore(stm_vernac_interp id st x);
                PG_compat.discard_all ()
              ), true, true
          | Sync (name, reason) -> (fun () ->
                log_processing_sync id name reason;
                reach eop;
                let wall_clock = Unix.gettimeofday () in
                let loc = x.expr.CAst.loc in
                record_pb_time name ?loc (wall_clock -. !wall_clock_last_fork);
                let proof =
                  match keep with
                  | VtDrop -> None
                  | VtKeep VtKeepAxiom ->
                      qed.fproof <- Some (None, ref false); None
                  | VtKeep opaque ->
                    let opaque = match opaque with
                      | VtKeepOpaque -> Opaque | VtKeepDefined -> Transparent
                      | VtKeepAxiom -> assert false
                    in
                    try Some (PG_compat.close_proof ~opaque ~keep_body_ucst_separate:false)
                    with exn ->
                      let iexn = Exninfo.capture exn in
                      Exninfo.iraise (State.exn_on id ~valid:eop iexn)
                in
                if keep <> VtKeep VtKeepAxiom then
                  reach view.next;
                let wall_clock2 = Unix.gettimeofday () in
                let st = Vernacstate.freeze_full_state () in
                let _st = match proof with
                  | None -> stm_vernac_interp id st x
                  | Some proof ->
                    let control, pe = extract_pe x in
                    { st with interp = stm_qed_delay_proof ~id ~st ~proof ~loc ~control pe }
                in
                let wall_clock3 = Unix.gettimeofday () in
                Aux_file.record_in_aux_at ?loc:x.expr.CAst.loc "proof_check_time"
                  (Printf.sprintf "%.3f" (wall_clock3 -. wall_clock2));
                PG_compat.discard_all ()
              ), true, true
          | MaybeASync (start, nodes, name, delegate) -> (fun () ->
                reach ~cache:true start;
                if CList.is_empty (Environ.named_context (Global.env ())) (* no sections *)
                   || PG_compat.get_pstate () |> (* #[using] attribute *)
                        Option.cata (fun x -> Option.has_some (Declare.Proof.get_used_variables x)) false
                then Util.pi1 (aux (ASync (start, nodes, name, delegate))) ()
                else Util.pi1 (aux (Sync (name, NoPU_NoHint_NoES))) ()
              ), not redefine_qed, true
          in
          aux (collect_proof keep (view.next, x) brname brinfo eop)
      | SSideff (ReplayCommand x,_) -> (fun () ->
            reach view.next;
            let st = Vernacstate.freeze_full_state () in
            ignore(stm_vernac_interp id st x)
          ), cache, true
      | SSideff (CherryPickEnv, origin) -> (fun () ->
            reach view.next;
            inject_non_pstate (pure_cherry_pick_non_pstate view.next origin);
          ), cache, true
    in
    let cache_step =
      (cur_opt()).async_proofs_cache = Some Force || cache_step
    in
    State.define ~doc ?safe_id
      ~cache:cache_step ~redefine:redefine_qed ~feedback_processed step id;
    stm_prerr_endline (fun () -> "reached: "^ Stateid.to_string id) in
  reach ~redefine_qed id

end (* }}} *)
[@@@ocaml.warning "+60"]

(********************************* STM API ************************************)
(******************************************************************************)

(** STM initialization options: *)

type stm_init_options =
  { doc_type : stm_doc_type
  (** The STM does set some internal flags differently depending on
     the specified [doc_type]. This distinction should disappear at
     some some point. *)

  ; injections : Coqargs.injection_command list
  (** Injects Require and Set/Unset commands before the initial
     state is ready *)

  }

let init_process stm_flags =
  Spawned.init_channels ();
  set_cur_opt stm_flags;
  CoqworkmgrApi.(init stm_flags.AsyncOpts.async_proofs_worker_priority);
  if (cur_opt()).async_proofs_mode = APon then Control.enable_thread_delay := true;
  if !Flags.async_proofs_worker_id = "master" && (cur_opt()).async_proofs_n_tacworkers > 0 then
    Partac.enable_par ~nworkers:(cur_opt()).async_proofs_n_tacworkers

let init_core () =
  State.register_root_state ()

let new_doc { doc_type ; injections } =

  (* We must reset the whole state before creating a document! *)
  State.restore_root_state ();

  let doc =
    let ps = Pcoq.freeze () in
    VCS.init doc_type Stateid.initial ps
  in

  Safe_typing.allow_delayed_constants := (cur_opt()).async_proofs_mode <> APoff;

  let top =
    match doc_type with
    | Interactive top -> Coqargs.dirpath_of_top top

    | VoDoc f ->
      let ldir = Coqargs.(dirpath_of_top (TopPhysical f)) in
      VCS.set_ldir ldir;
      set_compilation_hints f;
      ldir

    | VosDoc f ->
      let ldir = Coqargs.(dirpath_of_top (TopPhysical f)) in
      VCS.set_ldir ldir;
      set_compilation_hints f;
      ldir
    in

  (* Start this library and import initial libraries. *)
  let intern = Vernacinterp.fs_intern in
  Coqinit.start_library ~intern ~top injections;

  (* We record the state at this point! *)
  State.define ~doc ~cache:true ~redefine:true (fun () -> ()) Stateid.initial;
  Backtrack.record ();
  Slaves.init (cur_opt()).async_proofs_worker_priority;
  if async_proofs_is_master (cur_opt()) then begin
    stm_prerr_endline (fun () -> "Initializing workers");
    Query.init (cur_opt()).async_proofs_worker_priority;
    let opts = match (cur_opt()).async_proofs_private_flags with
      | None -> []
      | Some s -> Str.split_delim (Str.regexp ",") s in
    begin try
      let env_opt = Str.regexp "^extra-env=" in
      let env = List.find (fun s -> Str.string_match env_opt s 0) opts in
      async_proofs_workers_extra_env := Array.of_list
        (Str.split_delim (Str.regexp ";") (Str.replace_first env_opt "" env))
    with Not_found -> () end;
  end;
  doc, VCS.cur_tip ()

let observe ~doc id =
  !Hooks.sentence_exec id;
  let vcs = VCS.backup () in
  try
    Reach.known_state ~doc ~cache:(VCS.is_interactive ()) id;
    VCS.print ()
  with e ->
    let e = Exninfo.capture e in
    VCS.print ();
    VCS.restore vcs;
    Exninfo.iraise e

let finish ~doc =
  let head = VCS.current_branch () in
  let () = observe ~doc (VCS.get_branch_pos head) in
  let tip = VCS.cur_tip () in
  if not (State.is_cached ~cache:true tip) then
    CErrors.anomaly Pp.(str "Stm.finish: tip not cached");
  VCS.print ();
  State.get_cached tip

let wait ~doc =
  let () = observe ~doc (VCS.get_branch_pos VCS.Branch.master) in
  Slaves.wait_all_done ();
  VCS.print ()

let rec join_admitted_proofs id =
  if Stateid.equal id Stateid.initial then () else
  let view = VCS.visit id in
  match view.step with
  | SQed ({ keep = VtKeep VtKeepAxiom; fproof = Some (fp,_) },_) ->
       Option.iter (fun fp -> ignore(Future.force fp)) fp;
       join_admitted_proofs view.next
  | _ -> join_admitted_proofs view.next

(* Error resiliency may have tolerated some broken commands *)
let rec check_no_err_states ~doc visited id =
  let open Stateid in
  if Set.mem id visited then visited else
  match state_of_id ~doc id with
  | Error e -> raise e
  | _ ->
     let view = VCS.visit id in
     match view.step with
     | SQed(_,id) ->
         let visited = check_no_err_states ~doc (Set.add id visited) id in
         check_no_err_states ~doc visited view.next
     | _ -> check_no_err_states ~doc (Set.add id visited) view.next

let join ~doc =
  let () = wait ~doc in
  stm_prerr_endline (fun () -> "Joining the environment");
  let () = Opaques.Summary.join () in
  stm_prerr_endline (fun () -> "Joining Admitted proofs");
  join_admitted_proofs (VCS.get_branch_pos VCS.Branch.master);
  stm_prerr_endline (fun () -> "Checking no error states");
  ignore(check_no_err_states ~doc (Stateid.Set.singleton Stateid.initial)
    (VCS.get_branch_pos VCS.Branch.master));
  let tip = VCS.cur_tip () in
  if not (State.is_cached ~cache:true tip) then
    CErrors.anomaly Pp.(str "Stm.join: tip not cached");
  VCS.print ()

type branch_result = Ok | Unfocus of Stateid.t

let merge_proof_branch ~valid ?id qast keep brname =
  let brinfo = VCS.get_branch brname in
  let qed fproof = { qast; keep; brname; brinfo; fproof } in
  match brinfo with
  | { VCS.kind = Proof _ } ->
      VCS.checkout VCS.Branch.master;
      let id = VCS.new_node ?id None () in
      let parsing = Option.get @@ VCS.get_parsing_state (VCS.cur_tip ()) in
      VCS.merge id ~ours:(Qed (qed None)) brname;
      VCS.set_parsing_state id parsing;
      VCS.delete_branch brname;
      VCS.propagate_qed ();
      Ok
  | { VCS.kind = Edit (qed_id, master_id, _,_) } ->
      let ofp =
        match VCS.visit qed_id with
        | { step = SQed ({ fproof }, _) } -> fproof
        | _ -> assert false in
      VCS.rewrite_merge qed_id ~ours:(Qed (qed ofp)) ~at:master_id brname;
      VCS.delete_branch brname;
      VCS.gc ();
      let _st : unit = Reach.known_state ~doc:dummy_doc (* XXX should be taken in input *) ~redefine_qed:true ~cache:false qed_id in
      VCS.checkout VCS.Branch.master;
      Unfocus qed_id
  | { VCS.kind = Master } ->
       Exninfo.iraise (State.exn_on ~valid Stateid.dummy (PG_compat.NoCurrentProof, Exninfo.null))

(* When tty is true, this code also does some of the job of the user interface:
   jump back to a state that is valid *)
let handle_failure (e, info) vcs =
  VCS.restore vcs;
  VCS.print ();
  Exninfo.iraise (e, info)

let snapshot_vos ~doc ~output_native_objects ldir long_f_dot_vo =
  let _ : Vernacstate.t = finish ~doc in
  if List.length (VCS.branches ()) > 1 then
    CErrors.user_err (str"Cannot dump a vos with open proofs.");
  (* LATER: when create_vos is true, it could be more efficient to not allocate the futures; but for now it seems useful for synchronization of the workers,
  below, [snapshot] gets computed even if [create_vos] is true. *)
  let tasks = Slaves.dump_snapshot() in
  let except = List.fold_left (fun e (r,_) ->
     Future.UUIDSet.add r.Stateid.uuid e) Future.UUIDSet.empty tasks in
  let todo_proofs = Library.ProofsTodoSomeEmpty except in
  Library.save_library_to todo_proofs ~output_native_objects ldir long_f_dot_vo

let reset_task_queue = Slaves.reset_task_queue

(* Document building *)

(* We process a meta command found in the document *)
let process_back_meta_command ~newtip ~head oid aast =
    let valid = VCS.get_branch_pos head in
    let old_parsing = Option.get @@ VCS.get_parsing_state oid in

    (* Merge in and discard all the branches currently open that were not open in `oid` *)
    let { mine; others } = Backtrack.branches_of oid in
    List.iter (fun branch ->
        if not (List.mem_assoc branch (mine::others)) then
          ignore(merge_proof_branch ~valid aast VtDrop branch))
      (VCS.branches ());

    (* We add a node on top of every branch, to represent state aliasing *)
    VCS.checkout_shallowest_proof_branch ();
    let head = VCS.current_branch () in
    List.iter (fun b ->
        VCS.checkout b;
        let id = if (VCS.Branch.equal b head) then Some newtip else None in
        let proof_mode = VCS.get_proof_mode @@ VCS.cur_tip () in
        let id = VCS.new_node ?id proof_mode () in
        VCS.commit id (Alias (oid,aast));
        VCS.set_parsing_state id old_parsing)
      (VCS.branches ());
    VCS.checkout_shallowest_proof_branch ();
    Backtrack.record (); Ok

let { Goptions.get = get_allow_nested_proofs } =
  Goptions.declare_bool_option_and_ref
    ~key:Vernac_classifier.stm_allow_nested_proofs_option_name
    ~value:false
    ()

(** [process_transaction] adds a node in the document *)
let process_transaction ~doc ?(newtip=Stateid.fresh ()) x c =
  let { verbose; expr } = x in
  stm_pperr_endline (fun () -> str "{{{ processing: " ++ pr_ast x);
  let vcs = VCS.backup () in
  try
    let head = VCS.current_branch () in
    VCS.checkout head;
    let head_parsing =
      Option.get @@ VCS.(get_parsing_state (get_branch_pos head)) in
    let proof_mode = VCS.(get_proof_mode (get_branch_pos head)) in
    let rc = begin
      stm_prerr_endline (fun () ->
        "  classified as: " ^ Vernac_classifier.string_of_vernac_classification c);
      match c with
      (* Meta *)
      | VtMeta ->
        let id = Backtrack.undo_vernac_classifier expr ~doc in
        process_back_meta_command ~newtip ~head id x

      (* Query *)
      | VtQuery ->
          let id = VCS.new_node ~id:newtip proof_mode () in
          let queue =
            if VCS.is_vos_doc () &&
               VCS.((get_branch head).kind = Master) &&
               may_pierce_opaque x.expr.CAst.v.expr
            then SkipQueue
            else MainQueue in
          VCS.commit id (mkTransCmd x [] false queue);
          VCS.set_parsing_state id head_parsing;
          Backtrack.record (); Ok

      (* Proof *)
      | VtStartProof (guarantee, names) ->

         if not (get_allow_nested_proofs ()) && VCS.proof_nesting () > 0 then
          "Nested proofs are discouraged and not allowed by default. \
           This error probably means that you forgot to close the last \"Proof.\" with \"Qed.\" or \"Defined.\". \
           If you really intended to use nested proofs, you can do so by turning the \"Nested Proofs Allowed\" flag on."
           |> Pp.strbrk
           |> (fun s -> (UserError s, Exninfo.null))
           |> State.exn_on ~valid:Stateid.dummy newtip
           |> Exninfo.iraise
         else

          let proof_mode = Some (Synterp.get_default_proof_mode ()) in
          let id = VCS.new_node ~id:newtip proof_mode () in
          let bname = VCS.mk_branch_name x in
          VCS.checkout VCS.Branch.master;
          if VCS.Branch.equal head VCS.Branch.master then begin
            VCS.commit id (Fork (x, bname, guarantee, names));
            VCS.branch bname (Proof (VCS.proof_nesting () + 1))
          end else begin
            VCS.branch bname (Proof (VCS.proof_nesting () + 1));
            VCS.merge id ~ours:(Fork (x, bname, guarantee, names)) head
          end;
          VCS.set_parsing_state id head_parsing;
          Backtrack.record (); Ok

      | VtProofStep { proof_block_detection = cblock } ->
          let id = VCS.new_node ~id:newtip proof_mode () in
          let queue = MainQueue in
          VCS.commit id (mkTransTac x cblock queue);
          (* Static proof block detection delayed until an error really occurs.
             If/when and UI will make something useful with this piece of info,
             detection should occur here.
          detect_proof_block id cblock; *)
          VCS.set_parsing_state id head_parsing;
          Backtrack.record (); Ok

      | VtQed keep ->
          let valid = VCS.get_branch_pos head in
          let rc =
            merge_proof_branch ~valid ~id:newtip x keep head in
          VCS.checkout_shallowest_proof_branch ();
          Backtrack.record ();
          rc

      (* Side effect in a (still open) proof is replayed on all branches*)
      | VtSideff (l, w) ->
          let id = VCS.new_node ~id:newtip proof_mode () in
          let new_ids =
            match (VCS.get_branch head).VCS.kind with
            | Edit _ -> VCS.commit id (mkTransCmd x l true MainQueue); []
            | Master -> VCS.commit id (mkTransCmd x l false MainQueue); []
            | Proof _ ->
              VCS.checkout VCS.Branch.master;
              VCS.commit id (mkTransCmd x l true MainQueue);
              (* We can't replay a Definition since universes may be differently
               * inferred.  This holds in Coq >= 8.5 *)
              let action = match x.expr.CAst.v.expr with
                | VernacSynPure (VernacDefinition(_, _, DefineBody _)) -> CherryPickEnv
                | _ -> ReplayCommand x in
              VCS.propagate_sideff ~action
          in
          VCS.checkout_shallowest_proof_branch ();
          Backtrack.record ();
          let parsing_state =
            begin match w with
              | VtNow ->
                (* We need to execute to get the new parsing state *)
                let () = observe ~doc:dummy_doc (VCS.get_branch_pos (VCS.current_branch ())) in
                let parsing = Pcoq.freeze () in
                (* If execution has not been put in cache, we need to save the parsing state *)
                if (VCS.get_info id).state == EmptyState then VCS.set_parsing_state id parsing;
                parsing
              | VtLater -> VCS.set_parsing_state id head_parsing; head_parsing
            end
          in
          (* We save the parsing state on non-master branches *)
          List.iter (fun id ->
              if (VCS.get_info id).state == EmptyState then
              VCS.set_parsing_state id parsing_state) new_ids;
          Ok

      | VtProofMode proof_mode ->
        let id = VCS.new_node ~id:newtip (Some proof_mode) () in
        VCS.commit id (mkTransCmd x [] false MainQueue);
        VCS.set_parsing_state id head_parsing;
        Backtrack.record (); Ok

    end in
    let pr_rc rc = match rc with
      | Ok -> Pp.(seq [str "newtip ("; str (Stateid.to_string (VCS.cur_tip ())); str ")"])
      | _   -> Pp.(str "unfocus")
    in
    stm_pperr_endline (fun () -> str "processed with " ++ pr_rc rc ++ str " }}}");
    VCS.print ();
    rc
  with e ->
    let e = Exninfo.capture e in
    handle_failure e vcs

let get_ast ~doc id =
  match (VCS.visit id).step with
  | SCmd { cast = { expr } }
  | SFork (({ expr }, _, _, _), _)
  | SSideff ((ReplayCommand { expr }) , _)
  | SQed ({ qast = { expr } }, _) ->
    Some expr
  | SAlias _ | SSideff (CherryPickEnv, _) -> None

let stop_worker n = Slaves.cancel_worker n

let parse_sentence ~doc sid ~entry pa =
  let ps = Option.get @@ VCS.get_parsing_state sid in
  let proof_mode = VCS.get_proof_mode sid in
  Pcoq.unfreeze ps;
  Pcoq.Entry.parse (entry proof_mode) pa

(* You may need to know the len + indentation of previous command to compute
 * the indentation of the current one.
 *  Eg.   foo. bar.
 * Here bar is indented of the indentation of foo + its strlen (4) *)
let ind_len_loc_of_id sid =
  if Stateid.equal sid Stateid.initial then None
  else match (VCS.visit sid).step with
  | SCmd { ctac = true; cast = { indentation; strlen; expr } } ->
    Some (indentation, strlen, expr.CAst.loc)
  | _ -> None

(* the indentation logic works like this: if the beginning of the
   command is different than the start we are in a new line, thus
   indentation follows from the starting position. Otherwise, we use
   the previous one plus the offset.

   Note, this could maybe improved by handling more cases in
   compute_indentation. *)

let compute_indentation ?loc sid = Option.cata (fun loc ->
  let open Loc              in
  (* The effective length is the length on the last line *)
  let len = loc.ep - loc.bp in
  let prev_indent = match ind_len_loc_of_id sid with
    | None         -> 0
    | Some (i,l,p) -> i + l
  in
  (* Now if the line has not changed, the need to add the previous indent *)
  let eff_indent = loc.bp - loc.bol_pos in
  if loc.bol_pos = 0 then
    eff_indent + prev_indent, len
  else
    eff_indent, len
  ) (0, 0) loc

type add_focus = NewAddTip | Unfocus of Stateid.t

let add ~doc ~ontop ?newtip verb ast =
  !Hooks.document_add ast ontop;
  let loc = ast.CAst.loc in
  let cur_tip = VCS.cur_tip () in
  if not (Stateid.equal ontop cur_tip) then
    user_err ?loc
      (str "Stm.add called for a different state (" ++ str (Stateid.to_string ontop) ++
       str ") than the tip: " ++ str (Stateid.to_string cur_tip) ++ str "." ++ fnl () ++
       str "This is not supported yet, sorry.");
  let indentation, strlen = compute_indentation ?loc ontop in
  (* XXX: Classifiy vernac should be moved inside process transaction *)
  let clas = Vernac_classifier.classify_vernac ast in
  let aast = { verbose = verb; indentation; strlen; expr = ast } in
  match process_transaction ~doc ?newtip aast clas with
  | Ok -> doc, VCS.cur_tip (), NewAddTip
  | Unfocus qed_id -> doc, qed_id, Unfocus (VCS.cur_tip ())

type focus = {
  start : Stateid.t;
  stop : Stateid.t;
  tip : Stateid.t
}

type edit_focus = NewTip | Focus of focus

let query ~doc ~at ~route s =
  State.purify (fun s ->
    if Stateid.equal at Stateid.dummy then ignore(finish ~doc:dummy_doc)
    else Reach.known_state ~doc ~cache:true at;
      let rec loop () =
        match parse_sentence ~doc at ~entry:Pvernac.main_entry s with
        | None -> ()
        | Some ast ->
          let loc = ast.CAst.loc in
          let indentation, strlen = compute_indentation ?loc at in
          let st = State.get_cached at in
          let aast = {
            verbose = true; indentation; strlen;
            expr = ast } in
          ignore(stm_vernac_interp ~route at st aast);
          loop ()
      in
      loop ()
  )
  s

let edit_at ~doc id =
  assert (VCS.is_interactive());
  !Hooks.document_edit id;
  if Stateid.equal id Stateid.dummy then anomaly(str"edit_at dummy.") else
  let vcs = VCS.backup () in
  let on_cur_branch id =
    let rec aux cur =
      match VCS.visit cur with
      | { step = SFork _ } -> false
      | { next } -> if id = cur then true else aux next in
    aux (VCS.get_branch_pos (VCS.current_branch ())) in
  let rec is_pure_aux id =
    let view = VCS.visit id in
    match view.step with
    | SCmd _ -> is_pure_aux view.next
    | SFork _ -> true
    | _ -> false in
  let is_pure id =
    match (VCS.visit id).step with
    | SQed (_,last_step) -> is_pure_aux last_step
    | _ -> assert false
  in
  let is_ancestor_of_cur_branch id =
    Stateid.Set.mem id
      (VCS.reachable (VCS.get_branch_pos (VCS.current_branch ()))) in
  let has_failed qed_id =
    match VCS.visit qed_id with
    | { step = SQed ({ fproof = Some (Some fp,_) }, _) } -> Future.is_exn fp
    | _ -> false in
  let rec master_for_br root tip =
      if Stateid.equal tip Stateid.initial then tip else
      match VCS.visit tip with
      | { step = (SFork _ | SQed _) } -> tip
      | { step = SSideff (ReplayCommand _,id) } -> id
      | { step = SSideff _ } -> tip
      | { next } -> master_for_br root next in
  let reopen_branch start at_id qed_id tip old_branch =
    let master_id, cancel_switch, keep =
      (* Hum, this should be the real start_id in the cluster and not next *)
      match VCS.visit qed_id with
      | { step = SQed ({ fproof = Some (_,cs); keep },_) } -> start, cs, keep
      | _ -> anomaly (str "ProofTask not ending with Qed.") in
    VCS.branch ~root:master_id ~pos:id
      VCS.edit_branch (Edit (qed_id, master_id, keep, old_branch));
    VCS.delete_boxes_of id;
    cancel_switch := true;
    Reach.known_state ~doc ~cache:(VCS.is_interactive ()) id;
    VCS.checkout_shallowest_proof_branch ();
    Focus { stop = qed_id; start = master_id; tip } in
  let no_edit = function
   | Edit (_,_,_,_) -> Proof 1
   | x -> x in
  let backto id bn =
    List.iter VCS.delete_branch (VCS.branches ());
    let ancestors = VCS.reachable id in
    let { mine = brname, brinfo; others } = Backtrack.branches_of id in
    List.iter (fun (name,{ VCS.kind = k; root; pos }) ->
      if not(VCS.Branch.equal name VCS.Branch.master) &&
         Stateid.Set.mem root ancestors then
        VCS.branch ~root ~pos name k)
      others;
    VCS.reset_branch VCS.Branch.master (master_for_br brinfo.VCS.root id);
    VCS.branch ~root:brinfo.VCS.root ~pos:brinfo.VCS.pos
      (Option.default brname bn)
      (no_edit brinfo.VCS.kind);
    VCS.delete_boxes_of id;
    VCS.gc ();
    VCS.print ();
    Reach.known_state ~doc ~cache:(VCS.is_interactive ()) id;
    VCS.checkout_shallowest_proof_branch ();
    NewTip in
  try
    let rc =
      let focused = List.exists ((=) VCS.edit_branch) (VCS.branches ()) in
      let branch_info =
        match snd (VCS.get_info id).vcs_backup with
        | Some{ mine = bn, { VCS.kind = Proof _ }} -> Some bn
        | Some{ mine = _, { VCS.kind = Edit(_,_,_,bn) }} -> Some bn
        | _ -> None in
      match focused, VCS.proof_task_box_of id, branch_info with
      | _, Some _, None -> assert false
      | false, Some { qed = qed_id ; lemma = start }, Some bn ->
          let tip = VCS.cur_tip () in
          if has_failed qed_id && is_pure qed_id && not (cur_opt()).async_proofs_never_reopen_branch
          then reopen_branch start id qed_id tip bn
          else backto id (Some bn)
      | true, Some { qed = qed_id }, Some bn ->
          if on_cur_branch id then begin
            assert false
          end else if is_ancestor_of_cur_branch id then begin
            backto id (Some bn)
          end else begin
            anomaly(str"Cannot leave an Edit branch open.")
          end
      | true, None, _ ->
          if on_cur_branch id then begin
            VCS.reset_branch (VCS.current_branch ()) id;
            Reach.known_state ~doc ~cache:(VCS.is_interactive ()) id;
            VCS.checkout_shallowest_proof_branch ();
            NewTip
          end else if is_ancestor_of_cur_branch id then begin
            backto id None
          end else begin
            anomaly(str"Cannot leave an Edit branch open.")
          end
      | false, None, Some bn -> backto id (Some bn)
      | false, None, None -> backto id None
    in
    VCS.print ();
    doc, rc
  with
  | Vcs_aux.Expired -> user_err Pp.(str "Unknown state " ++ Stateid.print id ++ str".")
  | e ->
    let (e, info) = Exninfo.capture e in
    match Stateid.get info with
    | None ->
        VCS.print ();
        anomaly (str ("edit_at "^Stateid.to_string id^": ") ++
          CErrors.print_no_report e ++ str ".")
    | Some (_, id) ->
        stm_prerr_endline (fun () -> "Failed at state " ^ Stateid.to_string id);
        VCS.restore vcs;
        VCS.print ();
        Exninfo.iraise (e, info)

let get_current_state ~doc = VCS.cur_tip ()
let get_ldir ~doc = VCS.get_ldir ()

let get_doc did = dummy_doc

(*********************** TTY API (PG, coqtop, coqc) ***************************)
(******************************************************************************)

let current_proof_depth ~doc =
  let head = VCS.current_branch () in
  match VCS.get_branch head with
  | { VCS.kind = Master } -> 0
  | { VCS.pos = cur; VCS.kind = (Proof _ | Edit _); VCS.root = root } ->
      let rec distance root =
        if Stateid.equal cur root then 0
        else 1 + distance (VCS.visit cur).next in
      distance cur

let unmangle n =
  let n = VCS.Branch.to_string n in
  let idx = String.index n '_' + 1 in
  Names.Id.of_string (String.sub n idx (String.length n - idx))

let proofname b = match VCS.get_branch b with
  | { VCS.kind = (Proof _| Edit _) } -> Some b
  | _ -> None

let get_all_proof_names ~doc =
  List.map unmangle (CList.map_filter proofname (VCS.branches ()))

(* Export hooks *)
let state_computed_hook v = Hooks.state_computed := v
let state_ready_hook v = Hooks.state_ready := v
let forward_feedback_hook v = Hooks.forward_feedback := v
let unreachable_state_hook v = Hooks.unreachable_state := v
let document_add_hook v = Hooks.document_add := v
let document_edit_hook v = Hooks.document_edit := v
let sentence_exec_hook v = Hooks.sentence_exec := v

type document = VCS.vcs
let backup () = VCS.backup ()
let restore d = VCS.restore d


(* vim:set foldmethod=marker: *)
