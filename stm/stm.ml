(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* enable in case of stm problems  *)
let stm_debug = false

let stm_pr_err s  = Printf.eprintf "%s] %s\n"     (System.process_id ()) s; flush stderr
let stm_pp_err pp = Format.eprintf "%s] @[%a@]\n" (System.process_id ()) Pp.pp_with pp; flush stderr

let stm_prerr_endline s = if stm_debug then begin stm_pr_err (s ()) end else ()
let stm_pperr_endline s = if stm_debug then begin stm_pp_err (s ()) end else ()

let stm_prerr_debug   s = if !Flags.debug then begin stm_pr_err (s ()) end else ()

open Pp
open CErrors
open Feedback
open Vernacexpr
open Vernac_classifier

let execution_error ?loc state_id msg =
    feedback ~id:state_id
      (Message (Error, loc, msg))

module Hooks = struct

let state_computed, state_computed_hook = Hook.make
 ~default:(fun state_id ~in_cache ->
    feedback ~id:state_id Processed) ()

let state_ready, state_ready_hook = Hook.make
 ~default:(fun state_id -> ()) ()

let forward_feedback, forward_feedback_hook = 
  let m = Mutex.create () in
  Hook.make ~default:(function
    | { id = id; route; contents } ->
        try Mutex.lock m; feedback ~id:id ~route contents; Mutex.unlock m
        with e -> Mutex.unlock m; raise e) ()

let unreachable_state, unreachable_state_hook = Hook.make
 ~default:(fun _ _ -> ()) ()

include Hook

(* enables:  Hooks.(call foo args) *)
let call = get

let call_process_error_once =
  let processed : unit Exninfo.t = Exninfo.make () in
  fun (_, info as ei) ->
    match Exninfo.get info processed with
    | Some _ -> ei
    | None ->
        let e, info = ExplainErr.process_vernac_interp_error ei in
        let info = Exninfo.add info processed () in
        e, info

end

(* During interactive use we cache more states so that Undoing is fast *)
let interactive () =
  if !Flags.ide_slave || !Flags.print_emacs || not !Flags.batch_mode then `Yes
  else `No

let async_proofs_workers_extra_env = ref [||]

type aast = {
  verbose : bool;
  loc : Loc.t option;
  indentation : int;
  strlen : int;
  mutable expr : vernac_expr; (* mutable: Proof using hinted by aux file *)
}
let pr_ast { expr; indentation } = Pp.(int indentation ++ str " " ++ Ppvernac.pr_vernac expr)

let default_proof_mode () = Proof_global.get_default_proof_mode_name ()

(* Commands piercing opaque *)
let may_pierce_opaque = function
  | { expr = VernacPrint _ } -> true
  | { expr = VernacExtend (("Extraction",_), _) } -> true
  | { expr = VernacExtend (("SeparateExtraction",_), _) } -> true
  | { expr = VernacExtend (("ExtractionLibrary",_), _) } -> true
  | { expr = VernacExtend (("RecursiveExtractionLibrary",_), _) } -> true
  | { expr = VernacExtend (("ExtractionConstant",_), _) } -> true
  | { expr = VernacExtend (("ExtractionInlinedConstant",_), _) } -> true
  | { expr = VernacExtend (("ExtractionInductive",_), _) } -> true
  | _ -> false

let update_global_env () =
  if Proof_global.there_are_pending_proofs () then
    Proof_global.update_global_env ()

module Vcs_ = Vcs.Make(Stateid.Self)
type future_proof = Proof_global.closed_proof_output Future.computation
type proof_mode = string
type depth = int
type cancel_switch = bool ref
type branch_type =
  [ `Master
  | `Proof of proof_mode * depth
  | `Edit of
      proof_mode * Stateid.t * Stateid.t  * vernac_qed_type * Vcs_.Branch.t ]
(* TODO 8.7 : split commands and tactics, since this type is too messy now *)
type cmd_t = {
  ctac : bool; (* is a tactic *)
  ceff : bool; (* is a side-effecting command in the middle of a proof *)
  cast : aast;
  cids : Names.Id.t list;
  cblock : proof_block_name option;
  cqueue : [ `MainQueue
           | `TacQueue of solving_tac * anon_abstracting_tac * cancel_switch
           | `QueryQueue of cancel_switch
           | `SkipQueue ] }
type fork_t = aast * Vcs_.Branch.t * Vernacexpr.opacity_guarantee * Names.Id.t list
type qed_t = {
  qast : aast;
  keep : vernac_qed_type;
  mutable fproof : (future_proof * cancel_switch) option;
  brname : Vcs_.Branch.t;
  brinfo : branch_type Vcs_.branch_info
}
type seff_t = aast option
type alias_t = Stateid.t * aast
type transaction =
  | Cmd    of cmd_t
  | Fork   of fork_t
  | Qed    of qed_t
  | Sideff of seff_t
  | Alias  of alias_t
  | Noop
type step =
  [ `Cmd    of cmd_t
  | `Fork   of fork_t * Stateid.t option
  | `Qed    of qed_t * Stateid.t
  | `Sideff of [ `Ast of aast * Stateid.t | `Id of Stateid.t ]
  | `Alias  of alias_t ]
type visit = { step : step; next : Stateid.t }

let mkTransTac cast cblock cqueue =
  Cmd { ctac = true; cast; cblock; cqueue; cids = []; ceff = false }
let mkTransCmd cast cids ceff cqueue =
  Cmd { ctac = false; cast; cblock = None; cqueue; cids; ceff }

(* Parts of the system state that are morally part of the proof state *)
let summary_pstate = [ Evarutil.meta_counter_summary_name;
                       Evd.evar_counter_summary_name;
                       "program-tcc-table" ]
type cached_state =
  | Empty
  | Error of Exninfo.iexn
  | Valid of state
and state = { (* TODO: inline records in OCaml 4.03 *)
  system : States.state;       (* summary + libstack *)
  proof : Proof_global.state;  (* proof state *)
  shallow : bool               (* is the state trimmed down (libstack) *)
}
type branch = Vcs_.Branch.t * branch_type Vcs_.branch_info
type backup = { mine : branch; others : branch list }
type 'vcs state_info = { (* TODO: Make this record private to VCS *)
  mutable n_reached : int;      (* debug cache: how many times was computed *)
  mutable n_goals : int;        (* open goals: indentation *)
  mutable state : cached_state; (* state value *)
  mutable vcs_backup : 'vcs option * backup option;
}
let default_info () =
  { n_reached = 0; n_goals = 0; state = Empty; vcs_backup = None,None }

module DynBlockData : Dyn.S = Dyn.Make(struct end)

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

  val proof_nesting : (branch_type, 't,'i,'c) Vcs_.t -> int
  val find_proof_at_depth :
          (branch_type, 't, 'i,'c) Vcs_.t -> int ->
      Vcs_.Branch.t * branch_type Vcs_.branch_info
  exception Expired
  val visit : (branch_type, transaction,'i,'c) Vcs_.t -> Vcs_.Dag.node -> visit

end = struct (* {{{ *)

  let proof_nesting vcs =
    List.fold_left max 0
      (CList.map_filter
        (function
         | { Vcs_.kind = `Proof (_,n) } -> Some n
         | { Vcs_.kind = `Edit _ } -> Some 1
         | _ -> None)
        (List.map (Vcs_.get_branch vcs) (Vcs_.branches vcs)))

  let find_proof_at_depth vcs pl =
    try List.find (function
          | _, { Vcs_.kind = `Proof(m, n) } -> Int.equal n pl
          | _, { Vcs_.kind = `Edit _ } -> anomaly(Pp.str "find_proof_at_depth")
          | _ -> false)
        (List.map (fun h -> h, Vcs_.get_branch vcs h) (Vcs_.branches vcs))
    with Not_found -> failwith "find_proof_at_depth"

  exception Expired
  let visit vcs id =
    if Stateid.equal id Stateid.initial then
      anomaly(Pp.str "Visiting the initial state id")
    else if Stateid.equal id Stateid.dummy then
      anomaly(Pp.str "Visiting the dummy state id")
    else
    try
      match Vcs_.Dag.from_node (Vcs_.dag vcs) id with
      | [n, Cmd x] -> { step = `Cmd x; next = n }
      | [n, Alias x] -> { step = `Alias x; next = n }
      | [n, Fork x] -> { step = `Fork (x,None); next = n }
      | [n, Fork x; p, Noop] -> { step = `Fork (x,Some p); next = n }
      | [p, Noop; n, Fork x] -> { step = `Fork (x,Some p); next = n }
      | [n, Qed x; p, Noop]
      | [p, Noop; n, Qed x] -> { step = `Qed (x,p); next = n }
      | [n, Sideff None; p, Noop]
      | [p, Noop; n, Sideff None]-> { step = `Sideff (`Id p); next = n }
      | [n, Sideff (Some x); p, Noop]
      | [p, Noop; n, Sideff (Some x)]-> { step = `Sideff(`Ast (x,p)); next = n }
      | [n, Sideff (Some x)]-> {step = `Sideff(`Ast (x,Stateid.dummy)); next=n}
      | _ -> anomaly (Pp.str ("Malformed VCS at node "^Stateid.to_string id))
    with Not_found -> raise Expired

end (* }}} *)

(*************************** THE DOCUMENT *************************************)
(******************************************************************************)

(* Imperative wrap around VCS to obtain _the_ VCS that is the
 * representation of the document Coq is currently processing *)
module VCS : sig

  exception Expired

  module Branch : (module type of Vcs_.Branch with type t = Vcs_.Branch.t)
  type id = Stateid.t
  type 'branch_type branch_info = 'branch_type Vcs_.branch_info = {
    kind : [> `Master] as 'branch_type;
    root : id;
    pos  : id;
  }

  type vcs = (branch_type, transaction, vcs state_info, box) Vcs_.t

  val init : id -> unit

  val current_branch : unit -> Branch.t
  val checkout : Branch.t -> unit
  val branches : unit -> Branch.t list
  val get_branch : Branch.t -> branch_type branch_info
  val get_branch_pos : Branch.t -> id
  val new_node : ?id:Stateid.t -> unit -> id
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

  val get_info : id -> vcs state_info
  val reached : id -> unit
  val goals : id -> int -> unit
  val set_state : id -> cached_state -> unit
  val get_state : id -> cached_state

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
  val propagate_sideff : replay:aast option -> unit

  val gc : unit -> unit

  val visit : id -> visit

  val print : ?now:bool -> unit -> unit

  val backup : unit -> vcs
  val restore : vcs -> unit

end = struct (* {{{ *)

  include Vcs_
  exception Expired = Vcs_aux.Expired

  open Printf

  let print_dag vcs () =

    (* Due to threading, be wary that this will be called from the
       toplevel with we_are_parsing set to true, as indeed, the
       toplevel is waiting for input . What a race! XD

       In case you are hitting the race enable stm_debug.
    *)
    if stm_debug then Flags.we_are_parsing := false;

    let fname =
      "stm_" ^ Str.global_replace (Str.regexp " ") "_" (System.process_id ()) in
    let string_of_transaction = function
      | Cmd { cast = t } | Fork (t, _,_,_) ->
          (try Pp.string_of_ppcmds (pr_ast t) with _ -> "ERR")
      | Sideff (Some t) ->
          sprintf "Sideff(%s)"
            (try Pp.string_of_ppcmds (pr_ast t) with _ -> "ERR")
      | Sideff None -> "EnvChange"
      | Noop -> " "
      | Alias (id,_) -> sprintf "Alias(%s)" (Stateid.to_string id)
      | Qed { qast } -> Pp.string_of_ppcmds (pr_ast qast) in
    let is_green id = 
      match get_info vcs id with
      | Some { state = Valid _ } -> true
      | _ -> false in
    let is_red id =
      match get_info vcs id with
      | Some { state = Error _ } -> true
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

  type vcs = (branch_type, transaction, vcs state_info, box) t
  let vcs : vcs ref = ref (empty Stateid.dummy)

  let init id =
    vcs := empty id;
    vcs := set_info !vcs id (default_info ())

  let current_branch () = current_branch !vcs

  let checkout head = vcs := checkout !vcs head
  let branches () = branches !vcs
  let get_branch head = get_branch !vcs head
  let get_branch_pos head = (get_branch head).pos
  let new_node ?(id=Stateid.fresh ()) () =
    assert(Vcs_.get_info !vcs id = None);
    vcs := set_info !vcs id (default_info ());
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
    (match x with
    | VernacDefinition (_,((_,i),_),_) -> Names.string_of_id i
    | VernacStartTheoremProof (_,[Some ((_,i),_),_],_) -> Names.string_of_id i
    | _ -> "branch")
  let edit_branch = Branch.make "edit"
  let branch ?root ?pos name kind = vcs := branch !vcs ?root ?pos name kind
  let get_info id =
    match get_info !vcs id with
    | Some x -> x
    | None -> raise Vcs_aux.Expired
  let set_state id s =
    (get_info id).state <- s;
    if Flags.async_proofs_is_master () then Hooks.(call state_ready id)
  let get_state id = (get_info id).state
  let reached id =
    let info = get_info id in
    info.n_reached <- info.n_reached + 1
  let goals id n = (get_info id).n_goals <- n
  let cur_tip () = get_branch_pos (current_branch ())

  let proof_nesting () = Vcs_aux.proof_nesting !vcs

  let checkout_shallowest_proof_branch () =
    if List.mem edit_branch (Vcs_.branches !vcs) then begin
      checkout edit_branch;
      match get_branch edit_branch with
      | { kind = `Edit (mode, _,_,_,_) } -> Proof_global.activate_proof_mode mode
      | _ -> assert false
    end else
      let pl = proof_nesting () in
      try
        let branch, mode = match Vcs_aux.find_proof_at_depth !vcs pl with
          | h, { Vcs_.kind = `Proof (m, _) } -> h, m | _ -> assert false in
        checkout branch;
        stm_prerr_endline (fun () -> "mode:" ^ mode);
        Proof_global.activate_proof_mode mode
      with Failure _ ->
        checkout Branch.master;
        Proof_global.disactivate_current_proof_mode ()

  (* copies the transaction on every open branch *)
  let propagate_sideff ~replay:t =
    List.iter (fun b ->
      checkout b;
      let id = new_node () in
      merge id ~ours:(Sideff t) ~into:b Branch.master)
    (List.filter (fun b -> not (Branch.equal b Branch.master)) (branches ()))
  
  let visit id = Vcs_aux.visit !vcs id

  let nodes_in_slice ~block_start ~block_stop =
    let rec aux id =
      if Stateid.equal id block_start then [] else
      match visit id with
      | { next = n; step = `Cmd x } -> (id,Cmd x) :: aux n
      | { next = n; step = `Alias x } -> (id,Alias x) :: aux n
      | { next = n; step = `Sideff (`Ast (x,_)) } ->
           (id,Sideff (Some x)) :: aux n
      | _ -> anomaly Pp.(str("Cannot slice from "^ Stateid.to_string block_start ^
                         " to "^Stateid.to_string block_stop))
    in aux block_stop

  let slice ~block_start ~block_stop =
    let l = nodes_in_slice ~block_start ~block_stop in
    let copy_info v id =
      Vcs_.set_info v id
        { (get_info id) with state = Empty; vcs_backup = None,None } in
    let copy_info_w_state v id =
      Vcs_.set_info v id { (get_info id) with vcs_backup = None,None } in
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
    assert (match (get_info block_start).state with Valid _ -> true | _ -> false);
    (* We put in the new dag the most recent state known to master *)
    let rec fill id =
      match (get_info id).state with
      | Empty | Error _ -> fill (Vcs_aux.visit v id).next
      | Valid _ -> copy_info_w_state v id in
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
    if not (topo_invariant l) then anomaly Pp.(str "overlapping boxes");
    vcs := create_property !vcs l (ProofTask { qed; lemma })
  let create_proof_block ({ block_start; block_stop} as decl) name =
    let l = nodes_in_slice ~block_start ~block_stop in
    if not (topo_invariant l) then anomaly Pp.(str "overlapping boxes");
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
    | _ -> anomaly Pp.(str "node with more than 1 proof task box")

  let gc () =
    let old_vcs = !vcs in
    let new_vcs, erased_nodes = gc old_vcs in
    Stateid.Set.iter (fun id ->
        match (Vcs_aux.visit old_vcs id).step with
        | `Qed ({ fproof = Some (_, cancel_switch) }, _)
        | `Cmd { cqueue = `TacQueue (_,_,cancel_switch) }
        | `Cmd { cqueue = `QueryQueue cancel_switch } ->
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
      Mutex.lock m;
      job := Some j;
      Condition.signal c;
      Mutex.unlock m

    let get_last_job () =
      Mutex.lock m;
      while Option.is_empty !job do Condition.wait c m; done;
      match !job with
      | None -> assert false
      | Some x -> job := None; Mutex.unlock m; x

    let run_command () =
      try while true do get_last_job () () done
      with e -> () (* No failure *)

    let command ~now job =
      if now then job ()
      else begin
        set_last_job job;
        if Option.is_empty !worker then
          worker := Some (Thread.create run_command ())
      end

  end

  let print ?(now=false) () =
    if not !Flags.debug && not now then () else NB.command ~now (print_dag !vcs)

  let backup () = !vcs
  let restore v = vcs := v

end (* }}} *)

let state_of_id id =
  try match (VCS.get_info id).state with
    | Valid s -> `Valid (Some s)
    | Error (e,_) -> `Error e
    | Empty -> `Valid None
  with VCS.Expired -> `Expired


(****** A cache: fills in the nodes of the VCS document with their value ******)
module State : sig
  
  (** The function is from unit, so it uses the current state to define
      a new one.  I.e. one may been to install the right state before
      defining a new one.
      Warning: an optimization in installed_cached requires that state
      modifying functions are always executed using this wrapper. *)
  val define :
    ?safe_id:Stateid.t ->
    ?redefine:bool -> ?cache:Summary.marshallable ->
    ?feedback_processed:bool -> (unit -> unit) -> Stateid.t -> unit
  val fix_exn_ref : (Exninfo.iexn -> Exninfo.iexn) ref

  val install_cached : Stateid.t -> unit
  val is_cached : ?cache:Summary.marshallable -> Stateid.t -> bool
  val is_cached_and_valid : ?cache:Summary.marshallable -> Stateid.t -> bool


  val exn_on : Stateid.t -> valid:Stateid.t -> Exninfo.iexn -> Exninfo.iexn
  (* to send states across worker/master *)
  type frozen_state
  val get_cached : Stateid.t -> frozen_state
  val same_env : frozen_state -> frozen_state -> bool

  type proof_part
  type partial_state =
    [ `Full of frozen_state
    | `Proof of Stateid.t * proof_part ]
  val proof_part_of_frozen : frozen_state -> proof_part
  val assign : Stateid.t -> partial_state -> unit

  (* Only for internal use to catch problems in parse_sentence, should
     be removed in the state handling refactoring.  *)
  val cur_id : Stateid.t ref
end = struct (* {{{ *)

  (* cur_id holds Stateid.dummy in case the last attempt to define a state
   * failed, so the global state may contain garbage *)
  let cur_id = ref Stateid.dummy
  let fix_exn_ref = ref (fun x -> x)

  (* helpers *)
  let freeze_global_state marshallable =
    { system = States.freeze ~marshallable;
      proof = Proof_global.freeze ~marshallable;
      shallow = (marshallable = `Shallow) }
  let unfreeze_global_state { system; proof } =
    States.unfreeze system; Proof_global.unfreeze proof

  (* hack to make futures functional *)
  let () = Future.set_freeze
    (fun () -> Obj.magic (freeze_global_state `No, !cur_id))
    (fun t -> let s,i = Obj.magic t in unfreeze_global_state s; cur_id := i)
  
  type frozen_state = state
  type proof_part =
    Proof_global.state * Summary.frozen_bits (* only meta counters *)
  type partial_state =
    [ `Full of frozen_state
    | `Proof of Stateid.t * proof_part ]
  let proof_part_of_frozen { proof; system } =
    proof,
    Summary.project_summary (States.summary_of_state system) summary_pstate

  let freeze marshallable id =
    VCS.set_state id (Valid (freeze_global_state marshallable))
  let freeze_invalid id iexn = VCS.set_state id (Error iexn)

  let is_cached ?(cache=`No) id only_valid =
    if Stateid.equal id !cur_id then
      try match VCS.get_info id with
        | { state = Empty } when cache = `Yes -> freeze `No id; true
        | { state = Empty } when cache = `Shallow -> freeze `Shallow id; true
        | _ -> true
      with VCS.Expired -> false
    else
      try match VCS.get_info id with
        | { state = Empty } -> false
        | { state = Valid _ } -> true
        | { state = Error _ } -> not only_valid
      with VCS.Expired -> false

  let is_cached_and_valid ?cache id = is_cached ?cache id true
  let is_cached ?cache id = is_cached ?cache id false

  let install_cached id =
    match VCS.get_info id with
    | { state = Valid s } ->
         if Stateid.equal id !cur_id then () (* optimization *)
         else begin unfreeze_global_state s; cur_id := id end
    | { state = Error ie } -> cur_id := id; Exninfo.iraise ie 
    | _ ->
        (* coqc has a 1 slot cache and only for valid states *)
        if interactive () = `No && Stateid.equal id !cur_id then ()
        else anomaly Pp.(str "installing a non cached state")

  let get_cached id =
    try match VCS.get_info id with
    | { state = Valid s } -> s
    | _ -> anomaly Pp.(str "not a cached state")
    with VCS.Expired -> anomaly Pp.(str "not a cached state (expired)")

  let assign id what =
    if VCS.get_state id <> Empty then () else
    try match what with
    | `Full s ->
         let s =
           try
            let prev = (VCS.visit id).next in
            if is_cached_and_valid prev
            then { s with proof = 
              Proof_global.copy_terminators
                ~src:(get_cached prev).proof ~tgt:s.proof }
            else s
           with VCS.Expired -> s in
         VCS.set_state id (Valid s)
    | `Proof(ontop,(pstate,counters)) ->
         if is_cached_and_valid ontop then
           let s = get_cached ontop in
           let s = { s with proof =
             Proof_global.copy_terminators ~src:s.proof ~tgt:pstate } in
           let s = { s with system =
             States.replace_summary s.system
               (Summary.surgery_summary
                 (States.summary_of_state s.system)
               counters) } in
           VCS.set_state id (Valid s)
    with VCS.Expired -> ()

  let exn_on id ~valid (e, info) =
    match Stateid.get info with
    | Some _ -> (e, info)
    | None ->
        let loc = Loc.get_loc info in
        let (e, info) = Hooks.(call_process_error_once (e, info)) in
        execution_error ?loc id (iprint (e, info));
        (e, Stateid.add info ~valid id)

  let same_env { system = s1 } { system = s2 } =
    let s1 = States.summary_of_state s1 in
    let e1 = Summary.project_summary s1 [Global.global_env_summary_name] in
    let s2 = States.summary_of_state s2 in
    let e2 = Summary.project_summary s2 [Global.global_env_summary_name] in
    Summary.pointer_equal e1 e2

  let define ?safe_id ?(redefine=false) ?(cache=`No) ?(feedback_processed=true)
        f id
  =
    feedback ~id:id (ProcessingIn !Flags.async_proofs_worker_id);
    let str_id = Stateid.to_string id in
    if is_cached id && not redefine then
      anomaly Pp.(str"defining state "++str str_id++str" twice");
    try
      stm_prerr_endline (fun () -> "defining "^str_id^" (cache="^
        if cache = `Yes then "Y)" else if cache = `Shallow then "S)" else "N)");
      let good_id = match safe_id with None -> !cur_id | Some id -> id in
      fix_exn_ref := exn_on id ~valid:good_id;
      f ();
      fix_exn_ref := (fun x -> x);
      if cache = `Yes then freeze `No id
      else if cache = `Shallow then freeze `Shallow id;
      stm_prerr_endline (fun () -> "setting cur id to "^str_id);
      cur_id := id;
      if feedback_processed then
        Hooks.(call state_computed id ~in_cache:false);
      VCS.reached id;
      if Proof_global.there_are_pending_proofs () then
        VCS.goals id (Proof_global.get_open_goals ())
    with e ->
      let (e, info) = CErrors.push e in
      let good_id = !cur_id in
      cur_id := Stateid.dummy;
      VCS.reached id;
      let ie =
        match Stateid.get info, safe_id with
        | None, None -> (exn_on id ~valid:good_id (e, info))
        | None, Some good_id -> (exn_on id ~valid:good_id (e, info))
        | Some _, None -> (e, info)
        | Some (_,at), Some id -> (e, Stateid.add info ~valid:id at) in
      if cache = `Yes || cache = `Shallow then freeze_invalid id ie;
      Hooks.(call unreachable_state id ie);
      Exninfo.iraise ie

end (* }}} *)

(* indentation code for Show Script, initially contributed
 * by D. de Rauglaudre. Should be moved away.
 *)

module ShowScript = struct

let indent_script_item ((ng1,ngl1),nl,beginend,ppl) (cmd,ng) =
  (* ng1 : number of goals remaining at the current level (before cmd)
     ngl1 : stack of previous levels with their remaining goals
     ng : number of goals after the execution of cmd
     beginend : special indentation stack for { } *)
  let ngprev = List.fold_left (+) ng1 ngl1 in
  let new_ngl =
    if ng > ngprev then
      (* We've branched *)
      (ng - ngprev + 1, ng1 - 1 :: ngl1)
    else if ng < ngprev then
      (* A subgoal have been solved. Let's compute the new current level
	 by discarding all levels with 0 remaining goals. *)
      let rec loop = function
	| (0, ng2::ngl2) -> loop (ng2,ngl2)
	| p -> p
      in loop (ng1-1, ngl1)
    else
      (* Standard case, same goal number as before *)
      (ng1, ngl1)
  in
  (* When a subgoal have been solved, separate this block by an empty line *)
  let new_nl = (ng < ngprev)
  in
  (* Indentation depth *)
  let ind = List.length ngl1
  in
  (* Some special handling of bullets and { }, to get a nicer display *)
  let pred n = max 0 (n-1) in
  let ind, nl, new_beginend = match cmd with
    | VernacSubproof _ -> pred ind, nl, (pred ind)::beginend
    | VernacEndSubproof -> List.hd beginend, false, List.tl beginend
    | VernacBullet _ -> pred ind, nl, beginend
    | _ -> ind, nl, beginend
  in
  let pp = Pp.(
    (if nl then fnl () else mt ()) ++
    (hov (ind+1) (str (String.make ind ' ') ++ Ppvernac.pr_vernac cmd)))
  in
  (new_ngl, new_nl, new_beginend, pp :: ppl)

let get_script prf =
  let branch, test =
    match prf with
    | None -> VCS.Branch.master, fun _ -> true
    | Some name -> VCS.current_branch (),fun nl -> nl=[] || List.mem name nl in
  let rec find acc id =
    if Stateid.equal id Stateid.initial ||
       Stateid.equal id Stateid.dummy then acc else
    let view = VCS.visit id in
    match view.step with
    | `Fork((_,_,_,ns), _) when test ns -> acc
    | `Qed (qed, proof) -> find [qed.qast.expr, (VCS.get_info id).n_goals] proof
    | `Sideff (`Ast (x,_)) ->
         find ((x.expr, (VCS.get_info id).n_goals)::acc) view.next
    | `Sideff (`Id id)  -> find acc id
    | `Cmd {cast = x; ctac} when ctac -> (* skip non-tactics *)
         find ((x.expr, (VCS.get_info id).n_goals)::acc) view.next 
    | `Cmd _ -> find acc view.next
    | `Alias (id,_) -> find acc id
    | `Fork _ -> find acc view.next
    in
  find [] (VCS.get_branch_pos branch)

let show_script ?proof () =
  try
    let prf =
      try match proof with
      | None -> Some (Pfedit.get_current_proof_name ())
      | Some (p,_) -> Some (p.Proof_global.id)
      with Proof_global.NoCurrentProof -> None
    in
    let cmds = get_script prf in
    let _,_,_,indented_cmds =
      List.fold_left indent_script_item ((1,[]),false,[],[]) cmds
    in
    let indented_cmds = List.rev (indented_cmds) in
    msg_notice Pp.(v 0 (prlist_with_sep fnl (fun x -> x) indented_cmds))
  with Vcs_aux.Expired -> ()

end

(* Wrapper for Vernacentries.interp to set the feedback id *)
(* It is currently called 19 times, this number should be certainly
   reduced... *)
let stm_vernac_interp ?proof id ?route { verbose; loc; expr } =
  (* The Stm will gain the capability to interpret commmads affecting
     the whole document state, such as backtrack, etc... so we start
     to design the stm command interpreter now *)
  set_id_for_feedback ?route id;
  Aux_file.record_in_aux_set_at ?loc ();
  (* We need to check if a command should be filtered from
   * vernac_entries, as it cannot handle it. This should go away in
   * future refactorings.
   *)
  let rec is_filtered_command = function
  | VernacResetName _ | VernacResetInitial | VernacBack _
  | VernacBackTo _ | VernacRestart | VernacUndo _ | VernacUndoTo _
  | VernacBacktrack _ | VernacAbortAll | VernacAbort _ -> true
  | VernacTime (_,e) | VernacTimeout (_,e) | VernacRedirect (_,(_,e)) -> is_filtered_command e
  | _ -> false
  in
  let aux_interp cmd =
  if is_filtered_command cmd then
    stm_pperr_endline Pp.(fun () -> str "ignoring " ++ Ppvernac.pr_vernac expr)
  else match cmd with
  | VernacShow ShowScript -> ShowScript.show_script ()
  | expr ->
    stm_pperr_endline Pp.(fun () -> str "interpreting " ++ Ppvernac.pr_vernac expr);
    try Vernacentries.interp ?verbosely:(Some verbose) ?proof (Loc.tag ?loc expr)
    with e ->
      let e = CErrors.push e in
      Exninfo.iraise Hooks.(call_process_error_once e)
  in aux_interp expr

(****************************** CRUFT *****************************************)
(******************************************************************************)

(* The backtrack module simulates the classic behavior of a linear document *)
module Backtrack : sig

  val record : unit -> unit
  val backto : Stateid.t -> unit

  (* we could navigate the dag, but this ways easy *)
  val branches_of : Stateid.t -> backup

  (* To be installed during initialization *)
  val undo_vernac_classifier : vernac_expr -> vernac_classification

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

  let backto oid =
    let info = VCS.get_info oid in
    match info.vcs_backup with
    | None, _ ->
       anomaly Pp.(str"Backtrack.backto "++str(Stateid.to_string oid)++
               str": a state with no vcs_backup")
    | Some vcs, _ -> VCS.restore vcs

  let branches_of id =
    let info = VCS.get_info id in
    match info.vcs_backup with
    | _, None ->
       anomaly Pp.(str"Backtrack.branches_of "++str(Stateid.to_string id)++
                   str": a state with no vcs_backup")
    | _, Some x -> x

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
          | { step = `Fork ((_,_,_,l),_) } -> l, false,0
          | { step = `Cmd { cids = l; ctac } } -> l, ctac,0
          | { step = `Alias (_,{ expr = VernacUndo n}) } -> [], false, n
          | _ -> [],false,0 in
        match f acc (id, vcs, ids, tactic, undo) with
        | `Stop x -> x
        | `Cont acc -> next acc
 
  let undo_vernac_classifier v =
    try
      match v with
      | VernacResetInitial ->
          VtStm (VtBack Stateid.initial, true), VtNow
      | VernacResetName (_,name) ->
          let id = VCS.get_branch_pos (VCS.current_branch ()) in
          (try
            let oid =
              fold_until (fun b (id,_,label,_,_) ->
                if b then `Stop id else `Cont (List.mem name label))
              false id in
            VtStm (VtBack oid, true), VtNow
          with Not_found ->
            VtStm (VtBack id, true), VtNow)
      | VernacBack n ->
          let id = VCS.get_branch_pos (VCS.current_branch ()) in
          let oid = fold_until (fun n (id,_,_,_,_) ->
            if Int.equal n 0 then `Stop id else `Cont (n-1)) n id in
          VtStm (VtBack oid, true), VtNow
      | VernacUndo n ->
          let id = VCS.get_branch_pos (VCS.current_branch ()) in
          let oid = fold_until (fun n (id,_,_,tactic,undo) ->
            let value = (if tactic then 1 else 0) - undo in
            if Int.equal n 0 then `Stop id else `Cont (n-value)) n id in
          VtStm (VtBack oid, true), VtLater
      | VernacUndoTo _
      | VernacRestart as e ->
          let m = match e with VernacUndoTo m -> m | _ -> 0 in
          let id = VCS.get_branch_pos (VCS.current_branch ()) in
          let vcs =
            match (VCS.get_info id).vcs_backup with 
            | None, _ -> anomaly Pp.(str"Backtrack: tip with no vcs_backup")
            | Some vcs, _ -> vcs in
          let cb, _ =
            try Vcs_aux.find_proof_at_depth vcs (Vcs_aux.proof_nesting vcs)
            with Failure _ -> raise Proof_global.NoCurrentProof in
          let n = fold_until (fun n (_,vcs,_,_,_) ->
            if List.mem cb (Vcs_.branches vcs) then `Cont (n+1) else `Stop n)
            0 id in
          let oid = fold_until (fun n (id,_,_,_,_) ->
            if Int.equal n 0 then `Stop id else `Cont (n-1)) (n-m-1) id in
          VtStm (VtBack oid, true), VtLater
      | VernacAbortAll ->
          let id = VCS.get_branch_pos (VCS.current_branch ()) in
          let oid = fold_until (fun () (id,vcs,_,_,_) ->
            match Vcs_.branches vcs with [_] -> `Stop id | _ -> `Cont ())
            () id in
          VtStm (VtBack oid, true), VtLater
      | VernacBacktrack (id,_,_)
      | VernacBackTo id ->
          VtStm (VtBack (Stateid.of_int id), not !Flags.print_emacs), VtNow
      | _ -> VtUnknown, VtNow
    with
    | Not_found ->
       CErrors.user_err ~hdr:"undo_vernac_classifier"
        Pp.(str "Cannot undo")

end (* }}} *)

let hints = ref Aux_file.empty_aux_file
let set_compilation_hints file =
  hints := Aux_file.load_aux_file_for file
let get_hint_ctx loc =
  let s = Aux_file.get ?loc !hints "context_used" in
  match Str.split (Str.regexp ";") s with
  | ids :: _ ->
      let ids = List.map Names.Id.of_string (Str.split (Str.regexp " ") ids) in
      let ids = List.map (fun id -> Loc.tag id) ids in
      begin match ids with
      | [] -> SsEmpty
      | x :: xs ->
          List.fold_left (fun a x -> SsUnion (SsSingl x,a)) (SsSingl x) xs
      end
  | _ -> raise Not_found

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
 
exception RemoteException of Pp.std_ppcmds
let _ = CErrors.register_handler (function
  | RemoteException ppcmd -> ppcmd
  | _ -> raise Unhandled)

(****************** proof structure for error recovery ************************)
(******************************************************************************)

type document_node = {
  indentation : int;
  ast : Vernacexpr.vernac_expr;
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
  goals_to_admit : Goal.goal list;
  recovery_command : Vernacexpr.vernac_expr option;
}

type dynamic_block_error_recovery =
  static_block_declaration -> [ `ValidBlock of recovery_action | `Leaks ]

let proof_block_delimiters = ref []

let register_proof_block_delimiter name static dynamic =
  if List.mem_assoc name !proof_block_delimiters then
    CErrors.user_err ~hdr:"STM" Pp.(str "Duplicate block delimiter " ++ str name);
  proof_block_delimiters := (name, (static,dynamic)) :: !proof_block_delimiters

let mk_doc_node id = function
  | { step = `Cmd { ctac; cast = { indentation; expr }}; next } when ctac ->
       Some { indentation; ast = expr; id }
  | { step = `Sideff (`Ast ({ indentation; expr }, _)); next } ->
       Some { indentation; ast = expr; id }
  | _ -> None
let prev_node { id } =
  let id = (VCS.visit id).next in
  mk_doc_node id (VCS.visit id)
let cur_node id = mk_doc_node id (VCS.visit id)

let is_block_name_enabled name =
  match !Flags.async_proofs_tac_error_resilience with
  | `None -> false
  | `All -> true
  | `Only l -> List.mem name l

let detect_proof_block id name =
  let name = match name with None -> "indent" | Some x -> x in   
  if is_block_name_enabled name &&
     (Flags.async_proofs_is_master () || Flags.async_proofs_is_worker ())
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
      CErrors.user_err ~hdr:"STM"
        Pp.(str "Unknown proof block delimiter " ++ str name)
  )
(****************************** THE SCHEDULER *********************************)
(******************************************************************************)

(* Unused module warning doesn't understand [module rec] *)
[@@@ocaml.warning "-60"]
module rec ProofTask : sig
 
  type competence = Stateid.t list
  type task_build_proof = {
    t_exn_info : Stateid.t * Stateid.t;
    t_start    : Stateid.t;
    t_stop     : Stateid.t;
    t_drop     : bool;
    t_states   : competence;
    t_assign   : Proof_global.closed_proof_output Future.assignement -> unit;
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
  and  type competence := competence
  and  type request := request

  val build_proof_here :
    ?loc:Loc.t ->
    drop_pt:bool ->
    Stateid.t * Stateid.t -> Stateid.t ->
      Proof_global.closed_proof_output Future.computation

  (* If set, only tasks overlapping with this list are processed *)
  val set_perspective : Stateid.t list -> unit  

end = struct (* {{{ *)

  let forward_feedback msg = Hooks.(call forward_feedback msg)

  type competence = Stateid.t list
  type task_build_proof = {
    t_exn_info : Stateid.t * Stateid.t;
    t_start    : Stateid.t;
    t_stop     : Stateid.t;
    t_drop     : bool;
    t_states   : competence;
    t_assign   : Proof_global.closed_proof_output Future.assignement -> unit;
    t_loc      : Loc.t option;
    t_uuid     : Future.UUID.t;
    t_name     : string }

  type task =
    | BuildProof of task_build_proof
    | States of Stateid.t list

  type request =
  | ReqBuildProof of (Future.UUID.t,VCS.vcs) Stateid.request * bool * competence
  | ReqStates of Stateid.t list
  
  type error = {
    e_error_at    : Stateid.t;
    e_safe_id     : Stateid.t;
    e_msg         : Pp.std_ppcmds;
    e_safe_states : Stateid.t list }

  type response =
    | RespBuiltProof of Proof_global.closed_proof_output * float
    | RespError of error
    | RespStates of (Stateid.t * State.partial_state) list

  let name = ref "proofworker"
  let extra_env () = !async_proofs_workers_extra_env

  let perspective = ref []
  let set_perspective l = perspective := l

  let task_match age t =
    match age, t with
    | `Fresh, BuildProof { t_states } ->
        not !Flags.async_proofs_full ||
        List.exists (fun x -> CList.mem_f Stateid.equal x !perspective) t_states
    | `Old my_states, States l ->
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
        assert(age = `Fresh);
        try Some (ReqBuildProof ({
          Stateid.exn_info = t_exn_info;
          stop = t_stop;
          document = VCS.slice ~block_start:t_start ~block_stop:t_stop;
          loc = t_loc;
          uuid = t_uuid;
          name = t_name }, t_drop, t_states))
        with VCS.Expired -> None

  let use_response (s : competence AsyncTaskQueue.worker_status) t r =
    match s, t, r with
    | `Old c, States _, RespStates l ->
        List.iter (fun (id,s) -> State.assign id s) l; `End
    | `Fresh, BuildProof { t_assign; t_loc; t_name; t_states; t_drop },
              RespBuiltProof (pl, time) ->
        feedback (InProgress ~-1);
        t_assign (`Val pl);
        record_pb_time ?loc:t_loc t_name time;
        if !Flags.async_proofs_full || t_drop
        then `Stay(t_states,[States t_states])
        else `End
    | `Fresh, BuildProof { t_assign; t_loc; t_name; t_states },
            RespError { e_error_at; e_safe_id = valid; e_msg; e_safe_states } ->
        feedback (InProgress ~-1);
        let info = Stateid.add ~valid Exninfo.null e_error_at in
        let e = (RemoteException e_msg, info) in
        t_assign (`Exn e);
        `Stay(t_states,[States e_safe_states])
    | _ -> assert false

  let on_task_cancellation_or_expiration_or_slave_death = function
    | None -> ()
    | Some (States _) -> ()
    | Some (BuildProof { t_start = start; t_assign }) ->
        let s = "Worker dies or task expired" in
        let info = Stateid.add ~valid:start Exninfo.null start in
        let e = (RemoteException (Pp.strbrk s), info) in
        t_assign (`Exn e);
        execution_error start (Pp.strbrk s);
        feedback (InProgress ~-1)

  let build_proof_here ?loc ~drop_pt (id,valid) eop =
    Future.create (State.exn_on id ~valid) (fun () ->
      let wall_clock1 = Unix.gettimeofday () in
      if !Flags.batch_mode then Reach.known_state ~cache:`No eop
      else Reach.known_state ~cache:`Shallow eop;
      let wall_clock2 = Unix.gettimeofday () in
      Aux_file.record_in_aux_at ?loc "proof_build_time"
        (Printf.sprintf "%.3f" (wall_clock2 -. wall_clock1));
      let p = Proof_global.return_proof ~allow_partial:drop_pt () in
      if drop_pt then feedback ~id Complete;
      p)

  let perform_buildp { Stateid.exn_info; stop; document; loc } drop my_states =
    try
      VCS.restore document;
      VCS.print ();
      let proof, future_proof, time =
        let wall_clock = Unix.gettimeofday () in
        let fp = build_proof_here ?loc ~drop_pt:drop exn_info stop in
        let proof = Future.force fp in
        proof, fp, Unix.gettimeofday () -. wall_clock in
      (* We typecheck the proof with the kernel (in the worker) to spot
       * the few errors tactics don't catch, like the "fix" tactic building
       * a bad fixpoint *)
      let fix_exn = Future.fix_exn_of future_proof in
      if not drop then begin
        let checked_proof = Future.chain ~pure:false future_proof (fun p ->
          let pobject, _ =
            Proof_global.close_future_proof ~feedback_id:stop (Future.from_val ~fix_exn p) in
          let terminator = (* The one sent by master is an InvalidKey *)
            Lemmas.(standard_proof_terminator [] (mk_hook (fun _ _ -> ()))) in
          stm_vernac_interp stop
            ~proof:(pobject, terminator)
            { verbose = false; loc; indentation = 0; strlen = 0;
              expr = (VernacEndProof (Proved (Opaque None,None))) }) in
        ignore(Future.join checked_proof);
      end;
      RespBuiltProof(proof,time)
    with
    | e when CErrors.noncritical e || e = Stack_overflow ->
        let (e, info) = CErrors.push e in
        (* This can happen if the proof is broken.  The error has also been
         * signalled as a feedback, hence we can silently recover *)
        let e_error_at, e_safe_id = match Stateid.get info with
          | Some (safe, err) -> err, safe
          | None -> Stateid.dummy, Stateid.dummy in
        let e_msg = iprint (e, info) in
        stm_pperr_endline Pp.(fun () -> str "failed with the following exception: " ++ fnl () ++ e_msg);
        let e_safe_states = List.filter State.is_cached_and_valid my_states in
        RespError { e_error_at; e_safe_id; e_msg; e_safe_states }

  let perform_states query =
    if query = [] then [] else
    let is_tac e = match classify_vernac e with
    | VtProofStep _, _ -> true
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
      | Some (prev, o, `Cmd { cast = { expr }}), Some n
        when is_tac expr && State.same_env o n -> (* A pure tactic *)
          Some (id, `Proof (prev, State.proof_part_of_frozen n))
      | Some _, Some s ->
          msg_debug (Pp.str "STM: sending back a fat state");
          Some (id, `Full s)
      | _, Some s -> Some (id, `Full s) in
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
    | States _ -> msg_error(Pp.strbrk("Marshalling error: "^s^". "^
        "The system state could not be sent to the master process."))
    | BuildProof { t_exn_info; t_stop; t_assign; t_loc; t_drop = drop_pt } ->
      msg_error(Pp.strbrk("Marshalling error: "^s^". "^
        "The system state could not be sent to the worker process. "^
        "Falling back to local, lazy, evaluation."));
      t_assign(`Comp(build_proof_here ?loc:t_loc ~drop_pt t_exn_info t_stop));
      feedback (InProgress ~-1)

end (* }}} *)

(* Slave processes (if initialized, otherwise local lazy evaluation) *)
and Slaves : sig

  (* (eventually) remote calls *)
  val build_proof :
    ?loc:Loc.t -> drop_pt:bool ->
    exn_info:(Stateid.t * Stateid.t) -> block_start:Stateid.t -> block_stop:Stateid.t ->
      name:string -> future_proof * cancel_switch

  (* blocking function that waits for the task queue to be empty *)
  val wait_all_done : unit -> unit
  
  (* initialize the whole machinery (optional) *)
  val init : unit -> unit

  type 'a tasks = (('a,VCS.vcs) Stateid.request * bool) list
  val dump_snapshot : unit -> Future.UUID.t tasks
  val check_task : string -> int tasks -> int -> bool
  val info_tasks : 'a tasks -> (string * float * int) list
  val finish_task :
    string ->
    Library.seg_univ -> Library.seg_discharge -> Library.seg_proofs ->
    int tasks -> int -> Library.seg_univ

  val cancel_worker : WorkerPool.worker_id -> unit

  val reset_task_queue : unit -> unit

  val set_perspective : Stateid.t list -> unit

end = struct (* {{{ *)

  module TaskQueue = AsyncTaskQueue.MakeQueue(ProofTask)
  
  let queue = ref None

  let init () =
    if Flags.async_proofs_is_master () then
      queue := Some (TaskQueue.create !Flags.async_proofs_n_workers)
    else
      queue := Some (TaskQueue.create 0)

  let check_task_aux extra name l i =
    let { Stateid.stop; document; loc; name = r_name }, drop = List.nth l i in
    Flags.if_verbose msg_info
      Pp.(str(Printf.sprintf "Checking task %d (%s%s) of %s" i r_name extra name));
    VCS.restore document;
    let start =
      let rec aux cur =
        try aux (VCS.visit cur).next
        with VCS.Expired -> cur in
      aux stop in
    try
      Reach.known_state ~cache:`No stop;
      if drop then
        let _proof = Proof_global.return_proof ~allow_partial:true () in
        `OK_ADMITTED
      else begin
      (* The original terminator, a hook, has not been saved in the .vio*)
      Proof_global.set_terminator
        (Lemmas.standard_proof_terminator []
          (Lemmas.mk_hook (fun _ _ -> ())));
      let proof =
        Proof_global.close_proof ~keep_body_ucst_separate:true (fun x -> x) in
      (* We jump at the beginning since the kernel handles side effects by also
       * looking at the ones that happen to be present in the current env *)
      Reach.known_state ~cache:`No start;
      stm_vernac_interp stop ~proof
        { verbose = false; loc; indentation = 0; strlen = 0;
          expr = (VernacEndProof (Proved (Opaque None,None))) };
      `OK proof
      end
    with e ->
      let (e, info) = CErrors.push e in
      (try match Stateid.get info with
      | None ->
          msg_error Pp.(
            str"File " ++ str name ++ str ": proof of " ++ str r_name ++
            spc () ++ iprint (e, info))
      | Some (_, cur) ->
          match VCS.visit cur with
          | { step = `Cmd { cast = { loc } } }
          | { step = `Fork (( { loc }, _, _, _), _) } 
          | { step = `Qed ( { qast = { loc } }, _) } 
          | { step = `Sideff (`Ast ( { loc }, _)) } ->
              let start, stop = Option.cata Loc.unloc (0,0) loc in
              msg_error Pp.(
                str"File " ++ str name ++ str ": proof of " ++ str r_name ++
                str ": chars " ++ int start ++ str "-" ++ int stop ++
                spc () ++ iprint (e, info))
          | _ ->
              msg_error Pp.(
                str"File " ++ str name ++ str ": proof of " ++ str r_name ++
                spc () ++ iprint (e, info))
    with e ->
      msg_error Pp.(str"unable to print error message: " ++
                    str (Printexc.to_string e)));
      if drop then `ERROR_ADMITTED else `ERROR

  let finish_task name (u,cst,_) d p l i =
    let { Stateid.uuid = bucket }, drop = List.nth l i in
    let bucket_name =
      if bucket < 0 then (assert drop; ", no bucket")
      else Printf.sprintf ", bucket %d" bucket in
    match check_task_aux bucket_name name l i with
    | `ERROR -> exit 1
    | `ERROR_ADMITTED -> u, cst, false
    | `OK_ADMITTED -> u, cst, false
    | `OK (po,_) ->
        let discharge c = List.fold_right Cooking.cook_constr d.(bucket) c in
        let con =
          Nametab.locate_constant
            (Libnames.qualid_of_ident po.Proof_global.id) in
        let c = Global.lookup_constant con in
        let o = match c.Declarations.const_body with
          | Declarations.OpaqueDef o -> o
          | _ -> assert false in
        let uc =
          Option.get
            (Opaqueproof.get_constraints (Global.opaque_tables ()) o) in
        let pr =
          Future.from_val (Option.get (Global.body_of_constant_body c)) in
        let uc =
          Future.chain
            ~pure:true uc Univ.hcons_universe_context_set in
        let pr = Future.chain ~pure:true pr discharge in
        let pr = Future.chain ~pure:true pr Constr.hcons in
        Future.sink pr;
        let extra = Future.join uc in
        u.(bucket) <- uc;
        p.(bucket) <- pr;
        u, Univ.ContextSet.union cst extra, false
  
  let check_task name l i =
    match check_task_aux "" name l i with
    | `OK _ | `OK_ADMITTED -> true
    | `ERROR | `ERROR_ADMITTED -> false

  let info_tasks l =
    CList.map_i (fun i ({ Stateid.loc; name }, _) ->
      let time1 =
        try float_of_string (Aux_file.get ?loc !hints "proof_build_time")
        with Not_found -> 0.0 in
      let time2 =
        try float_of_string (Aux_file.get ?loc !hints "proof_check_time")
        with Not_found -> 0.0 in
      name, max (time1 +. time2) 0.0001,i) 0 l

  let set_perspective idl =
    ProofTask.set_perspective idl;
    TaskQueue.broadcast (Option.get !queue);
    let open ProofTask in
    let overlap s1 s2 =
      List.exists (fun x -> CList.mem_f Stateid.equal x s2) s1 in
    let overlap_rel s1 s2 =
      match overlap s1 idl, overlap s2 idl with
      | true, true | false, false -> 0
      | true, false -> -1
      | false, true -> 1 in
    TaskQueue.set_order (Option.get !queue) (fun task1 task2 ->
     match task1, task2 with
     | BuildProof { t_states = s1 },
       BuildProof { t_states = s2 } -> overlap_rel s1 s2
     | _ -> 0)

  let build_proof ?loc ~drop_pt ~exn_info ~block_start ~block_stop ~name:pname =
    let id, valid as t_exn_info = exn_info in
    let cancel_switch = ref false in
    if TaskQueue.n_workers (Option.get !queue) = 0 then
      if !Flags.compilation_mode = Flags.BuildVio then begin
        let f,assign =
         Future.create_delegate ~blocking:true ~name:pname (State.exn_on id ~valid) in
        let t_uuid = Future.uuid f in
        let task = ProofTask.(BuildProof {
          t_exn_info; t_start = block_start; t_stop = block_stop; t_drop = drop_pt;
          t_assign = assign; t_loc = loc; t_uuid; t_name = pname;
          t_states = VCS.nodes_in_slice ~block_start ~block_stop }) in
        TaskQueue.enqueue_task (Option.get !queue) (task,cancel_switch);
        f, cancel_switch
      end else
        ProofTask.build_proof_here ?loc ~drop_pt t_exn_info block_stop, cancel_switch
    else 
      let f, t_assign = Future.create_delegate ~name:pname (State.exn_on id ~valid) in
      let t_uuid = Future.uuid f in
      feedback (InProgress 1);
      let task = ProofTask.(BuildProof {
        t_exn_info; t_start = block_start; t_stop = block_stop; t_assign; t_drop = drop_pt;
        t_loc = loc; t_uuid; t_name = pname;
        t_states = VCS.nodes_in_slice ~block_start ~block_stop }) in
      TaskQueue.enqueue_task (Option.get !queue) (task,cancel_switch);
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
             match request_of_task `Fresh x with
             | Some (ReqBuildProof (r, b, _)) -> Some(r, b)
             | _ -> None)
        tasks in
    stm_prerr_endline (fun () -> Printf.sprintf "dumping %d tasks\n" (List.length reqs));
    reqs

  let reset_task_queue () = TaskQueue.clear (Option.get !queue)

end (* }}} *)

and TacTask : sig

  type output = Constr.constr * Evd.evar_universe_context
  type task = {
    t_state    : Stateid.t;
    t_state_fb : Stateid.t;
    t_assign   : output Future.assignement -> unit;
    t_ast      : int * aast;
    t_goal     : Goal.goal;
    t_kill     : unit -> unit;
    t_name     : string }  
  exception NoProgress

  include AsyncTaskQueue.Task with type task := task

end = struct (* {{{ *)

  type output = Constr.constr * Evd.evar_universe_context
  
  let forward_feedback msg = Hooks.(call forward_feedback msg)

  type task = {
    t_state    : Stateid.t;
    t_state_fb : Stateid.t;
    t_assign   : output Future.assignement -> unit;
    t_ast      : int * aast;
    t_goal     : Goal.goal;
    t_kill     : unit -> unit;
    t_name     : string }  

  type request = {
    r_state    : Stateid.t;
    r_state_fb : Stateid.t;
    r_document : VCS.vcs option;
    r_ast      : int * aast;
    r_goal     : Goal.goal;
    r_name     : string }

  type response =
    | RespBuiltSubProof of output
    | RespError of Pp.std_ppcmds
    | RespNoProgress
  exception NoProgress

  let name = ref "tacworker"
  let extra_env () = [||]
  type competence = unit
  let task_match _ _ = true

  (* run by the master, on a thread *)
  let request_of_task age { t_state; t_state_fb; t_ast; t_goal; t_name } =
    try Some {
      r_state    = t_state;
      r_state_fb = t_state_fb;
      r_document =
        if age <> `Fresh then None
        else Some (VCS.slice ~block_start:t_state ~block_stop:t_state);
      r_ast      = t_ast;
      r_goal     = t_goal;
      r_name     = t_name }
    with VCS.Expired -> None
          
  let use_response _ { t_assign; t_state; t_state_fb; t_kill } resp =
    match resp with
    | RespBuiltSubProof o -> t_assign (`Val o); `Stay ((),[])
    | RespNoProgress ->
        let e = (NoProgress, Exninfo.null) in
        t_assign (`Exn e);
        t_kill ();
        `Stay ((),[])
    | RespError msg ->
        let e = (RemoteException msg, Exninfo.null) in
        t_assign (`Exn e);
        t_kill ();
        `Stay ((),[])
                    
  let on_marshal_error err { t_name } =
    stm_pr_err ("Fatal marshal error: " ^ t_name );
    flush_all (); exit 1

  let on_task_cancellation_or_expiration_or_slave_death = function
    | Some { t_kill } -> t_kill ()
    | _ -> ()
 
  let command_focus = Proof.new_focus_kind ()
  let focus_cond = Proof.no_cond command_focus

  let perform { r_state = id; r_state_fb; r_document = vcs; r_ast; r_goal } =
    Option.iter VCS.restore vcs;
    try
      Reach.known_state ~cache:`No id;
      Future.purify (fun () ->
       let _,_,_,_,sigma0 = Proof.proof (Proof_global.give_me_the_proof ()) in
       let g = Evd.find sigma0 r_goal in
       let is_ground c = Evarutil.is_ground_term sigma0 (EConstr.of_constr c) in
       if not (
         is_ground Evd.(evar_concl g) &&
         List.for_all (Context.Named.Declaration.for_all is_ground)
                      Evd.(evar_context g))
       then
         CErrors.user_err ~hdr:"STM" Pp.(strbrk("the par: goal selector supports ground "^
           "goals only"))
       else begin
        let (i, ast) = r_ast in
        Proof_global.simple_with_current_proof (fun _ p -> Proof.focus focus_cond () i p);
        stm_vernac_interp r_state_fb ast;
        let _,_,_,_,sigma = Proof.proof (Proof_global.give_me_the_proof ()) in
        match Evd.(evar_body (find sigma r_goal)) with
        | Evd.Evar_empty -> RespNoProgress
        | Evd.Evar_defined t ->
            let t = EConstr.of_constr t in
            let t = Evarutil.nf_evar sigma t in
            if Evarutil.is_ground_term sigma t then
              let t = EConstr.Unsafe.to_constr t in
              RespBuiltSubProof (t, Evd.evar_universe_context sigma)
            else CErrors.user_err ~hdr:"STM" Pp.(str"The solution is not ground")
       end) ()
    with e when CErrors.noncritical e -> RespError (CErrors.print e)

  let name_of_task { t_name } = t_name
  let name_of_request { r_name } = r_name
  
end (* }}} *)

and Partac : sig

  val vernac_interp :
    solve:bool -> abstract:bool -> cancel_switch ->
    int -> Stateid.t -> Stateid.t -> aast ->
      unit

end = struct (* {{{ *)
    
  module TaskQueue = AsyncTaskQueue.MakeQueue(TacTask)

  let vernac_interp ~solve ~abstract cancel nworkers safe_id id
    { indentation; verbose; loc; expr = e; strlen }
  =
    let e, time, fail =
      let rec find ~time ~fail = function
        | VernacTime (_,e) -> find ~time:true ~fail e
        | VernacRedirect (_,(_,e)) -> find ~time ~fail e
        | VernacFail e -> find ~time ~fail:true e
        | e -> e, time, fail in find ~time:false ~fail:false e in
    Vernacentries.with_fail fail (fun () ->
    (if time then System.with_time !Flags.time else (fun x -> x)) (fun () ->
    ignore(TaskQueue.with_n_workers nworkers (fun queue ->
    Proof_global.with_current_proof (fun _ p ->
      let goals, _, _, _, _ = Proof.proof p in
      let open TacTask in
      let res = CList.map_i (fun i g ->
        let f, assign =
          Future.create_delegate
            ~name:(Printf.sprintf "subgoal %d" i)
            (State.exn_on id ~valid:safe_id) in
        let t_ast = (i, { indentation; verbose; loc; expr = e; strlen }) in
        let t_name = Goal.uid g in
        TaskQueue.enqueue_task queue
          ({ t_state = safe_id; t_state_fb = id;
            t_assign = assign; t_ast; t_goal = g; t_name;
            t_kill = (fun () -> if solve then TaskQueue.cancel_all queue) },
           cancel);
        g,f)
        1 goals in
      TaskQueue.join queue;
      let assign_tac : unit Proofview.tactic =
        Proofview.(Goal.nf_enter { Goal.enter = fun g ->
        let gid = Goal.goal g in
        let f =
          try List.assoc gid res
          with Not_found -> CErrors.anomaly(str"Partac: wrong focus") in
        if not (Future.is_over f) then
          (* One has failed and cancelled the others, but not this one *)
          if solve then Tacticals.New.tclZEROMSG
            (str"Interrupted by the failure of another goal")
          else tclUNIT ()
        else
          let open Notations in
          try
            let pt, uc = Future.join f in
            stm_pperr_endline (fun () -> hov 0 (
              str"g=" ++ int (Evar.repr gid) ++ spc () ++
              str"t=" ++ (Printer.pr_constr pt) ++ spc () ++
              str"uc=" ++ Termops.pr_evar_universe_context uc));
            (if abstract then Tactics.tclABSTRACT None else (fun x -> x))
              (V82.tactic (Refiner.tclPUSHEVARUNIVCONTEXT uc) <*>
              Tactics.exact_no_check (EConstr.of_constr pt))
          with TacTask.NoProgress ->
            if solve then Tacticals.New.tclSOLVE [] else tclUNIT ()
        })
      in
      Proof.run_tactic (Global.env()) assign_tac p)))) ())
  
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

  let name = ref "queryworker"
  let extra_env _ = [||]
  type competence = unit
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
  
  let forward_feedback msg = Hooks.(call forward_feedback msg)

  let perform { r_where; r_doc; r_what; r_for } =
    VCS.restore r_doc;
    VCS.print ();
    Reach.known_state ~cache:`No r_where;
    try
      stm_vernac_interp r_for { r_what with verbose = true };
      feedback ~id:r_for Processed
    with e when CErrors.noncritical e ->
      let e = CErrors.push e in
      let msg = iprint e     in
      feedback ~id:r_for (Message (Error, None, msg))
    
  let name_of_task { t_what } = string_of_ppcmds (pr_ast t_what)
  let name_of_request { r_what } = string_of_ppcmds (pr_ast r_what)

end (* }}} *)

and Query : sig 

  val init : unit -> unit
  val vernac_interp : cancel_switch -> Stateid.t ->  Stateid.t -> aast -> unit

end = struct (* {{{ *)

  module TaskQueue = AsyncTaskQueue.MakeQueue(QueryTask)

  let queue = ref None

  let vernac_interp switch prev id q =
    assert(TaskQueue.n_workers (Option.get !queue) > 0);
    TaskQueue.enqueue_task (Option.get !queue)
      QueryTask.({ t_where = prev; t_for = id; t_what = q }, switch)

  let init () = queue := Some (TaskQueue.create
    (if !Flags.async_proofs_full then 1 else 0))

end (* }}} *)

(* Runs all transactions needed to reach a state *)
and Reach : sig

  val known_state :
    ?redefine_qed:bool -> cache:Summary.marshallable -> Stateid.t -> unit

end = struct (* {{{ *)

let pstate = summary_pstate

let async_policy () =
  let open Flags in
  if is_universe_polymorphism () then false
  else if interactive () = `Yes then
    (async_proofs_is_master () || !async_proofs_mode = APonLazy)
  else
    (!compilation_mode = BuildVio || !async_proofs_mode <> APoff)

let delegate name =
     get_hint_bp_time name >= !Flags.async_proofs_delegation_threshold
  || !Flags.compilation_mode = Flags.BuildVio
  || !Flags.async_proofs_full
 
let warn_deprecated_nested_proofs =
  CWarnings.create ~name:"deprecated-nested-proofs" ~category:"deprecated"
         (fun () ->
          strbrk ("Nested proofs are deprecated and will "^
                    "stop working in a future Coq version"))

let collect_proof keep cur hd brkind id =
 stm_prerr_endline (fun () -> "Collecting proof ending at "^Stateid.to_string id);
 let no_name = "" in
 let name = function
   | [] -> no_name
   | id :: _ -> Names.Id.to_string id in
 let loc = (snd cur).loc in
 let rec is_defined_expr = function
   | VernacEndProof (Proved ((Transparent|Opaque (Some _)),_)) -> true
   | VernacTime (_, e) -> is_defined_expr e
   | VernacRedirect (_, (_, e)) -> is_defined_expr e
   | VernacTimeout (_, e) -> is_defined_expr e
   | _ -> false in
 let is_defined = function
   | _, { expr = e } -> is_defined_expr e in
 let proof_using_ast = function
   | Some (_, ({ expr = VernacProof(_,Some _) } as v)) -> Some v
   | _ -> None in
 let has_proof_using x = proof_using_ast x <> None in
 let proof_no_using = function
   | Some (_, ({ expr = VernacProof(t,None) } as v)) -> t,v
   | _ -> assert false in
 let has_proof_no_using = function
   | Some (_, { expr = VernacProof(_,None) }) -> true
   | _ -> false in
 let too_complex_to_delegate = function
   | { expr = (VernacDeclareModule _
              | VernacDefineModule _
              | VernacDeclareModuleType _
              | VernacInclude _) } -> true
   | { expr =  (VernacRequire _ | VernacImport _) } -> true
   | ast -> may_pierce_opaque ast in
 let parent = function Some (p, _) -> p | None -> assert false in
 let is_empty = function `Async(_,_,[],_,_) | `MaybeASync(_,_,[],_,_) -> true | _ -> false in
 let rec collect last accn id =
    let view = VCS.visit id in
    match view.step with
    | (`Sideff (`Ast(x,_)) | `Cmd { cast = x })
      when too_complex_to_delegate x -> `Sync(no_name,None,`Print)
    | `Cmd { cast = x } -> collect (Some (id,x)) (id::accn) view.next
    | `Sideff (`Ast(x,_)) -> collect (Some (id,x)) (id::accn) view.next
    (* An Alias could jump everywhere... we hope we can ignore it*)
    | `Alias _ -> `Sync (no_name,None,`Alias)
    | `Fork((_,_,_,_::_::_), _) ->
        `Sync (no_name,proof_using_ast last,`MutualProofs)
    | `Fork((_,_,Doesn'tGuaranteeOpacity,_), _) ->
        `Sync (no_name,proof_using_ast last,`Doesn'tGuaranteeOpacity)
    | `Fork((_,hd',GuaranteesOpacity,ids), _) when has_proof_using last ->
        assert (VCS.Branch.equal hd hd' || VCS.Branch.equal hd VCS.edit_branch);
        let name = name ids in
        `ASync (parent last,proof_using_ast last,accn,name,delegate name)
    | `Fork((_, hd', GuaranteesOpacity, ids), _) when
       has_proof_no_using last && not (State.is_cached_and_valid (parent last)) &&
       !Flags.compilation_mode = Flags.BuildVio ->
        assert (VCS.Branch.equal hd hd'||VCS.Branch.equal hd VCS.edit_branch);
        (try
          let name, hint = name ids, get_hint_ctx loc  in
          let t, v = proof_no_using last in
          v.expr <- VernacProof(t, Some hint);
          `ASync (parent last,proof_using_ast last,accn,name,delegate name)
        with Not_found ->
          let name = name ids in
          `MaybeASync (parent last, None, accn, name, delegate name))
    | `Fork((_, hd', GuaranteesOpacity, ids), _) ->
        assert (VCS.Branch.equal hd hd' || VCS.Branch.equal hd VCS.edit_branch);
        let name = name ids in
        `MaybeASync (parent last, None, accn, name, delegate name)
    | `Sideff _ ->
       warn_deprecated_nested_proofs ();
        `Sync (no_name,None,`NestedProof)
    | _ -> `Sync (no_name,None,`Unknown) in
 let make_sync why = function
   | `Sync(name,pua,_) -> `Sync (name,pua,why)
   | `MaybeASync(_,pua,_,name,_) -> `Sync (name,pua,why)
   | `ASync(_,pua,_,name,_) -> `Sync (name,pua,why) in
 let check_policy rc = if async_policy () then rc else make_sync `Policy rc in
 match cur, (VCS.visit id).step, brkind with
 | (parent, { expr = VernacExactProof _ }), `Fork _, _ ->
     `Sync (no_name,None,`Immediate)
 | _, _, { VCS.kind = `Edit _ }  -> check_policy (collect (Some cur) [] id)
 | _ ->
     if is_defined cur then `Sync (no_name,None,`Transparent)
     else if keep == VtDrop then `Sync (no_name,None,`Aborted)
     else
       let rc = collect (Some cur) [] id in
       if is_empty rc then make_sync `AlreadyEvaluated rc
       else if (keep == VtKeep || keep == VtKeepAsAxiom) &&
          (not(State.is_cached_and_valid id) || !Flags.async_proofs_full)
       then check_policy rc
       else make_sync `AlreadyEvaluated rc

let string_of_reason = function
  | `Transparent -> "non opaque"
  | `AlreadyEvaluated -> "proof already evaluated"
  | `Policy -> "policy"
  | `NestedProof -> "contains nested proof"
  | `Immediate -> "proof term given explicitly"
  | `Aborted -> "aborted proof"
  | `Doesn'tGuaranteeOpacity -> "not a simple opaque lemma"
  | `MutualProofs -> "block of mutually recursive proofs"
  | `Alias -> "contains Undo-like command"
  | `Print -> "contains Print-like command"
  | `NoPU_NoHint_NoES -> "no 'Proof using..', no .aux file, inside a section"
  | `Unknown -> "unsupported case"

let log_string s = stm_prerr_debug (fun () -> "STM: " ^ s)
let log_processing_async id name = log_string Printf.(sprintf
  "%s: proof %s: asynch" (Stateid.to_string id) name
)
let log_processing_sync id name reason = log_string Printf.(sprintf
  "%s: proof %s: synch (cause: %s)"
  (Stateid.to_string id) name (string_of_reason reason)
)

let wall_clock_last_fork = ref 0.0

let known_state ?(redefine_qed=false) ~cache id =
 
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
        match dynamic_check decl with
        | `Leaks -> Exninfo.iraise exn
        | `ValidBlock { base_state; goals_to_admit; recovery_command } -> begin
           let tac =
             let open Proofview.Notations in
             Proofview.Goal.nf_enter { enter = fun gl ->
               if CList.mem_f Evar.equal
                 (Proofview.Goal.goal gl) goals_to_admit then
             Proofview.give_up else Proofview.tclUNIT ()
               } in
           match (VCS.get_info base_state).state with
           | Valid { proof } ->
               Proof_global.unfreeze proof;
               Proof_global.with_current_proof (fun _ p ->
                 feedback ~id:id Feedback.AddedAxiom;
                 fst (Pfedit.solve Vernacexpr.SelectAll None tac p), ());
               Option.iter (fun expr -> stm_vernac_interp id {
                  verbose = true; loc = None; expr; indentation = 0;
                  strlen = 0 })
               recovery_command
           | _ -> assert false
        end
      with Not_found ->
          CErrors.user_err ~hdr:"STM"
            (str "Unknown proof block delimiter " ++ str name)
  in

  (* Absorb tactic errors from f () *)
  let resilient_tactic id blockname f =
    if !Flags.async_proofs_tac_error_resilience = `None ||
       (Flags.async_proofs_is_master () &&
        !Flags.async_proofs_mode = Flags.APoff)
    then f ()
    else
      try f ()
      with e when CErrors.noncritical e ->
        let ie = CErrors.push e in
        error_absorbing_tactic id blockname ie in
  (* Absorb errors from f x *)
  let resilient_command f x =
    if not !Flags.async_proofs_cmd_error_resilience ||
       (Flags.async_proofs_is_master () &&
        !Flags.async_proofs_mode = Flags.APoff)
    then f x
    else
      try f x
      with e when CErrors.noncritical e -> () in

  (* ugly functions to process nested lemmas, i.e. hard to reproduce
   * side effects *)
  let cherry_pick_non_pstate () =
    Summary.freeze_summary ~marshallable:`No ~complement:true pstate,
    Lib.freeze ~marshallable:`No in
  let inject_non_pstate (s,l) =
    Summary.unfreeze_summary s; Lib.unfreeze l; update_global_env ()
  in
  let rec pure_cherry_pick_non_pstate safe_id id = Future.purify (fun id ->
    stm_prerr_endline (fun () -> "cherry-pick non pstate " ^ Stateid.to_string id);
    reach ~safe_id id;
    cherry_pick_non_pstate ()) id

  (* traverses the dag backward from nodes being already calculated *)
  and reach ?safe_id ?(redefine_qed=false) ?(cache=cache) id =
    stm_prerr_endline (fun () -> "reaching: " ^ Stateid.to_string id);
    if not redefine_qed && State.is_cached ~cache id then begin
      Hooks.(call state_computed id ~in_cache:true);
      stm_prerr_endline (fun () -> "reached (cache)");
      State.install_cached id
    end else
    let step, cache_step, feedback_processed =
      let view = VCS.visit id in
      match view.step with
      | `Alias (id,_) -> (fun () ->
            reach view.next; reach id
          ), cache, true
      | `Cmd { cast = x; cqueue = `SkipQueue } -> (fun () ->
            reach view.next), cache, true
      | `Cmd { cast = x; cqueue = `TacQueue (solve,abstract,cancel); cblock } ->
          (fun () ->
            resilient_tactic id cblock (fun () ->
              reach ~cache:`Shallow view.next;
              Partac.vernac_interp ~solve ~abstract
                cancel !Flags.async_proofs_n_tacworkers view.next id x)
          ), cache, true
      | `Cmd { cast = x; cqueue = `QueryQueue cancel }
        when Flags.async_proofs_is_master () -> (fun () ->
            reach view.next;
            Query.vernac_interp cancel view.next id x
          ), cache, false
      | `Cmd { cast = x; ceff = eff; ctac = true; cblock } -> (fun () ->
            resilient_tactic id cblock (fun () ->
              reach view.next;
              stm_vernac_interp id x);
	    if eff then update_global_env ()
          ), (if eff then `Yes else cache), true
      | `Cmd { cast = x; ceff = eff } -> (fun () ->
          (match !Flags.async_proofs_mode with
           | Flags.APon | Flags.APonLazy ->
             resilient_command reach view.next
           | Flags.APoff -> reach view.next);
          stm_vernac_interp id x;
          if eff then update_global_env ()
        ), (if eff then `Yes else cache), true
      | `Fork ((x,_,_,_), None) -> (fun () ->
            resilient_command reach view.next;
            stm_vernac_interp id x;
            wall_clock_last_fork := Unix.gettimeofday ()
          ), `Yes, true
      | `Fork ((x,_,_,_), Some prev) -> (fun () -> (* nested proof *)
            reach ~cache:`Shallow prev;
            reach view.next;
            (try stm_vernac_interp id x;
            with e when CErrors.noncritical e ->
              let (e, info) = CErrors.push e in
              let info = Stateid.add info ~valid:prev id in
              Exninfo.iraise (e, info));
            wall_clock_last_fork := Unix.gettimeofday ()
          ), `Yes, true
      | `Qed ({ qast = x; keep; brinfo; brname } as qed, eop) ->
          let rec aux = function
          | `ASync (block_start, pua, nodes, name, delegate) -> (fun () ->
                assert(keep == VtKeep || keep == VtKeepAsAxiom);
                let drop_pt = keep == VtKeepAsAxiom in
                let block_stop, exn_info, loc = eop, (id, eop), x.loc in
                log_processing_async id name;
                VCS.create_proof_task_box nodes ~qed:id ~block_start;
                begin match brinfo, qed.fproof with
                | { VCS.kind = `Edit _ }, None -> assert false
                | { VCS.kind = `Edit (_,_,_, okeep, _) }, Some (ofp, cancel) ->
                    assert(redefine_qed = true);
                    if okeep != keep then
                      msg_error(strbrk("The command closing the proof changed. "
                        ^"The kernel cannot take this into account and will "
                        ^(if keep == VtKeep then "not check " else "reject ")
                        ^"the "^(if keep == VtKeep then "new" else "incomplete")
                        ^" proof. Reprocess the command declaring "
                        ^"the proof's statement to avoid that."));
                    let fp, cancel =
                      Slaves.build_proof
                        ?loc ~drop_pt ~exn_info ~block_start ~block_stop ~name in
                    Future.replace ofp fp;
                    qed.fproof <- Some (fp, cancel);
                    (* We don't generate a new state, but we still need
                     * to install the right one *)
                    State.install_cached id
                | { VCS.kind = `Proof _ }, Some _ -> assert false
                | { VCS.kind = `Proof _ }, None ->
                    reach ~cache:`Shallow block_start;
                    let fp, cancel =
                      if delegate then
                        Slaves.build_proof
                          ?loc ~drop_pt ~exn_info ~block_start ~block_stop ~name
                      else
                        ProofTask.build_proof_here ?loc
                          ~drop_pt exn_info block_stop, ref false
                    in
                    qed.fproof <- Some (fp, cancel);
                    let proof =
                      Proof_global.close_future_proof ~feedback_id:id fp in
                    if not delegate then ignore(Future.compute fp);
                    reach view.next;
                    stm_vernac_interp id ~proof x;
                    feedback ~id:id Incomplete
                | { VCS.kind = `Master }, _ -> assert false
                end;
                Proof_global.discard_all ()
              ), (if redefine_qed then `No else `Yes), true
          | `Sync (name, _, `Immediate) -> (fun () -> 
                reach eop; stm_vernac_interp id x; Proof_global.discard_all ()
              ), `Yes, true
          | `Sync (name, pua, reason) -> (fun () ->
                log_processing_sync id name reason;
                reach eop;
                let wall_clock = Unix.gettimeofday () in
                record_pb_time name ?loc:x.loc (wall_clock -. !wall_clock_last_fork);
                let proof =
                  match keep with
                  | VtDrop -> None
                  | VtKeepAsAxiom ->
                      let ctx = Evd.empty_evar_universe_context in
                      let fp = Future.from_val ([],ctx) in
                      qed.fproof <- Some (fp, ref false); None
                  | VtKeep ->
                      Some(Proof_global.close_proof
                                ~keep_body_ucst_separate:false
                                (State.exn_on id ~valid:eop)) in
                if keep != VtKeepAsAxiom then
                  reach view.next;
                let wall_clock2 = Unix.gettimeofday () in
                stm_vernac_interp id ?proof x;
                let wall_clock3 = Unix.gettimeofday () in
                Aux_file.record_in_aux_at ?loc:x.loc "proof_check_time"
                  (Printf.sprintf "%.3f" (wall_clock3 -. wall_clock2));
                Proof_global.discard_all ()
              ), `Yes, true
          | `MaybeASync (start, pua, nodes, name, delegate) -> (fun () ->
                reach ~cache:`Shallow start;
                (* no sections *)
                if CList.is_empty (Environ.named_context (Global.env ()))
                then Util.pi1 (aux (`ASync (start, pua, nodes, name, delegate))) ()
                else Util.pi1 (aux (`Sync (name, pua, `NoPU_NoHint_NoES))) ()
              ), (if redefine_qed then `No else `Yes), true
          in
          aux (collect_proof keep (view.next, x) brname brinfo eop)
      | `Sideff (`Ast (x,_)) -> (fun () ->
            reach view.next; stm_vernac_interp id x; update_global_env ()
          ), cache, true
      | `Sideff (`Id origin) -> (fun () ->
            reach view.next;
            inject_non_pstate (pure_cherry_pick_non_pstate view.next origin);
          ), cache, true
    in
    let cache_step =
      if !Flags.async_proofs_cache = Some Flags.Force then `Yes
      else cache_step in
    State.define ?safe_id
      ~cache:cache_step ~redefine:redefine_qed ~feedback_processed step id;
    stm_prerr_endline (fun () -> "reached: "^ Stateid.to_string id) in
  reach ~redefine_qed id

end (* }}} *)
[@@@ocaml.warning "+60"]

(********************************* STM API ************************************)
(******************************************************************************)

let init () =
  VCS.init Stateid.initial;
  set_undo_classifier Backtrack.undo_vernac_classifier;
  State.define ~cache:`Yes (fun () -> ()) Stateid.initial;
  Backtrack.record ();
  Slaves.init ();
  if Flags.async_proofs_is_master () then begin
    stm_prerr_endline (fun () -> "Initializing workers");
    Query.init ();
    let opts = match !Flags.async_proofs_private_flags with
      | None -> []
      | Some s -> Str.split_delim (Str.regexp ",") s in
    begin try
      let env_opt = Str.regexp "^extra-env=" in
      let env = List.find (fun s -> Str.string_match env_opt s 0) opts in
      async_proofs_workers_extra_env := Array.of_list
        (Str.split_delim (Str.regexp ";") (Str.replace_first env_opt "" env))
    with Not_found -> () end;
  end

let observe id =
  let vcs = VCS.backup () in
  try
    Reach.known_state ~cache:(interactive ()) id;
    VCS.print ()
  with e ->
    let e = CErrors.push e in
    VCS.print ();
    VCS.restore vcs;
    Exninfo.iraise e

let finish () =
  let head = VCS.current_branch () in
  observe (VCS.get_branch_pos head);
  VCS.print ();
  (* EJGA: Setting here the proof state looks really wrong, and it
     hides true bugs cf bug #5363. Also, what happens with observe? *)
  (* Some commands may by side effect change the proof mode *)
  match VCS.get_branch head with
  | { VCS.kind = `Edit (mode,_,_,_,_) } -> Proof_global.activate_proof_mode mode
  | { VCS.kind = `Proof (mode, _) } -> Proof_global.activate_proof_mode mode
  | _ -> ()

let wait () =
  Slaves.wait_all_done ();
  VCS.print ()

let rec join_admitted_proofs id =
  if Stateid.equal id Stateid.initial then () else
  let view = VCS.visit id in
  match view.step with
  | `Qed ({ keep = VtKeepAsAxiom; fproof = Some (fp,_) },_) ->
       ignore(Future.force fp);
       join_admitted_proofs view.next
  | _ -> join_admitted_proofs view.next

let join () =
  finish ();
  wait ();
  stm_prerr_endline (fun () -> "Joining the environment");
  Global.join_safe_environment ();
  stm_prerr_endline (fun () -> "Joining Admitted proofs");
  join_admitted_proofs (VCS.get_branch_pos (VCS.current_branch ()));
  VCS.print ();
  VCS.print ()

let dump_snapshot () = Slaves.dump_snapshot (), RemoteCounter.snapshot ()
type document = VCS.vcs
type tasks = int Slaves.tasks * RemoteCounter.remote_counters_status
let check_task name (tasks,rcbackup) i =
  RemoteCounter.restore rcbackup;
  let vcs = VCS.backup () in
  try
    let rc = Future.purify (Slaves.check_task name tasks) i in
    VCS.restore vcs;
    rc
  with e when CErrors.noncritical e -> VCS.restore vcs; false
let info_tasks (tasks,_) = Slaves.info_tasks tasks
let finish_tasks name u d p (t,rcbackup as tasks) =
  RemoteCounter.restore rcbackup;
  let finish_task u (_,_,i) =
    let vcs = VCS.backup () in
    let u = Future.purify (Slaves.finish_task name u d p t) i in
    VCS.restore vcs;
    u in
  try
    let u, a, _ = List.fold_left finish_task u (info_tasks tasks) in
    (u,a,true), p
  with e ->
    let e = CErrors.push e in
    msg_error (str"File " ++ str name ++ str ":" ++ spc () ++ iprint e);
    exit 1

let merge_proof_branch ~valid ?id qast keep brname =
  let brinfo = VCS.get_branch brname in
  let qed fproof = { qast; keep; brname; brinfo; fproof } in
  match brinfo with
  | { VCS.kind = `Proof _ } ->
      VCS.checkout VCS.Branch.master;
      let id = VCS.new_node ?id () in
      VCS.merge id ~ours:(Qed (qed None)) brname;
      VCS.delete_branch brname;
      VCS.propagate_sideff ~replay:None;
      `Ok
  | { VCS.kind = `Edit (mode, qed_id, master_id, _,_) } ->
      let ofp =
        match VCS.visit qed_id with
        | { step = `Qed ({ fproof }, _) } -> fproof
        | _ -> assert false in
      VCS.rewrite_merge qed_id ~ours:(Qed (qed ofp)) ~at:master_id brname;
      VCS.delete_branch brname;
      VCS.gc ();
      Reach.known_state ~redefine_qed:true ~cache:`No qed_id;
      VCS.checkout VCS.Branch.master;
      `Unfocus qed_id
  | { VCS.kind = `Master } ->
       Exninfo.iraise (State.exn_on ~valid Stateid.dummy (Proof_global.NoCurrentProof, Exninfo.null))

(* When tty is true, this code also does some of the job of the user interface:
   jump back to a state that is valid *)
let handle_failure (e, info) vcs =
  if e = CErrors.Drop then Exninfo.iraise (e, info) else
  match Stateid.get info with
  | None ->
      VCS.restore vcs;
      VCS.print ();
      anomaly(str"error with no safe_id attached:" ++ spc() ++
        CErrors.iprint_no_report (e, info))
  | Some (safe_id, id) ->
      stm_prerr_endline (fun () -> "Failed at state " ^ Stateid.to_string id);
      VCS.restore vcs;
      VCS.print ();
      Exninfo.iraise (e, info)

let snapshot_vio ldir long_f_dot_vo =
  finish ();
  if List.length (VCS.branches ()) > 1 then
    CErrors.user_err ~hdr:"stm" (str"Cannot dump a vio with open proofs");
  Library.save_library_to ~todo:(dump_snapshot ()) ldir long_f_dot_vo
    (Global.opaque_tables ())

let reset_task_queue = Slaves.reset_task_queue

(* Document building *)
let process_transaction ?(newtip=Stateid.fresh ())
  ({ verbose; loc; expr } as x) c =
  stm_pperr_endline (fun () -> str "{{{ processing: " ++ pr_ast x);
  let vcs = VCS.backup () in
  try
    let head = VCS.current_branch () in
    VCS.checkout head;
    let rc = begin
      stm_prerr_endline (fun () ->
        "  classified as: " ^ string_of_vernac_classification c);
      match c with
      (* Joining various parts of the document *)
      | VtStm (VtJoinDocument, b), VtNow -> join (); `Ok
      | VtStm (VtWait, b),         VtNow -> finish (); wait (); `Ok
      | VtStm ((VtJoinDocument|VtWait),_), VtLater ->
          anomaly(str"classifier: join actions cannot be classified as VtLater")

      (* Back *)
      | VtStm (VtBack oid, true), w ->
          let id = VCS.new_node ~id:newtip () in
          let { mine; others } = Backtrack.branches_of oid in
          let valid = VCS.get_branch_pos head in
          List.iter (fun branch ->
            if not (List.mem_assoc branch (mine::others)) then
              ignore(merge_proof_branch ~valid x VtDrop branch))
            (VCS.branches ());
          VCS.checkout_shallowest_proof_branch ();
          let head = VCS.current_branch () in
          List.iter (fun b ->
            if not(VCS.Branch.equal b head) then begin
              VCS.checkout b;
              VCS.commit (VCS.new_node ()) (Alias (oid,x));
            end)
            (VCS.branches ());
          VCS.checkout_shallowest_proof_branch ();
          VCS.commit id (Alias (oid,x));
          Backtrack.record (); if w == VtNow then finish (); `Ok
      | VtStm (VtBack id, false), VtNow ->
          stm_prerr_endline (fun () -> "undo to state " ^ Stateid.to_string id);
          Backtrack.backto id;
          VCS.checkout_shallowest_proof_branch ();
          Reach.known_state ~cache:(interactive ()) id; `Ok
      | VtStm (VtBack id, false), VtLater ->
          anomaly(str"classifier: VtBack + VtLater must imply part_of_script")

      (* Query *)
      | VtQuery (false,(report_id,route)), VtNow ->
          (try stm_vernac_interp report_id ~route x
           with e ->
             let e = CErrors.push e in
             Exninfo.iraise (State.exn_on ~valid:Stateid.dummy report_id e)); `Ok
      | VtQuery (true,(report_id,_)), w ->
          assert(Stateid.equal report_id Stateid.dummy);
          let id = VCS.new_node ~id:newtip () in
          let queue =
            if !Flags.async_proofs_full then `QueryQueue (ref false)
            else if Flags.(!compilation_mode = BuildVio) &&
                    VCS.((get_branch head).kind = `Master) &&
                    may_pierce_opaque x
                 then `SkipQueue 
            else `MainQueue in
          VCS.commit id (mkTransCmd x [] false queue);
          Backtrack.record (); if w == VtNow then finish (); `Ok
      | VtQuery (false,_), VtLater ->
          anomaly(str"classifier: VtQuery + VtLater must imply part_of_script")

      (* Proof *)
      | VtStartProof (mode, guarantee, names), w ->
          let id = VCS.new_node ~id:newtip () in
          let bname = VCS.mk_branch_name x in
          VCS.checkout VCS.Branch.master;
          if VCS.Branch.equal head VCS.Branch.master then begin
            VCS.commit id (Fork (x, bname, guarantee, names));
            VCS.branch bname (`Proof (mode, VCS.proof_nesting () + 1))
          end else begin
            VCS.branch bname (`Proof (mode, VCS.proof_nesting () + 1));
            VCS.merge id ~ours:(Fork (x, bname, guarantee, names)) head
          end;
          Proof_global.activate_proof_mode mode;
          Backtrack.record (); if w == VtNow then finish (); `Ok
      | VtProofMode _, VtLater ->
          anomaly(str"VtProofMode must be executed VtNow")
      | VtProofMode mode, VtNow ->
          let id = VCS.new_node ~id:newtip () in
          VCS.commit id (mkTransCmd x [] false `MainQueue);
          List.iter
            (fun bn -> match VCS.get_branch bn with
            | { VCS.root; kind = `Master; pos } -> ()
            | { VCS.root; kind = `Proof(_,d); pos } ->
                VCS.delete_branch bn;
                VCS.branch ~root ~pos bn (`Proof(mode,d))
            | { VCS.root; kind = `Edit(_,f,q,k,ob); pos } ->
                VCS.delete_branch bn;
                VCS.branch ~root ~pos bn (`Edit(mode,f,q,k,ob)))
            (VCS.branches ());
          VCS.checkout_shallowest_proof_branch ();
          Backtrack.record ();
          finish ();
          `Ok
      | VtProofStep { parallel; proof_block_detection = cblock }, w ->
          let id = VCS.new_node ~id:newtip () in
          let queue =
            match parallel with
            | `Yes(solve,abstract) -> `TacQueue (solve, abstract, ref false)
            | `No -> `MainQueue in
          VCS.commit id (mkTransTac x cblock queue);
          (* Static proof block detection delayed until an error really occurs.
             If/when and UI will make something useful with this piece of info,
             detection should occur here.
          detect_proof_block id cblock; *)
          Backtrack.record (); if w == VtNow then finish (); `Ok
      | VtQed keep, w ->
          let valid = VCS.get_branch_pos head in
          let rc = merge_proof_branch ~valid ~id:newtip x keep head in
          VCS.checkout_shallowest_proof_branch ();
          Backtrack.record (); if w == VtNow then finish ();
          rc
          
      (* Side effect on all branches *)
      | VtUnknown, _ when expr = VernacToplevelControl Drop ->
          stm_vernac_interp (VCS.get_branch_pos head) x; `Ok

      | VtSideff l, w ->
          let in_proof = not (VCS.Branch.equal head VCS.Branch.master) in
          let id = VCS.new_node ~id:newtip () in
          VCS.checkout VCS.Branch.master;
          VCS.commit id (mkTransCmd x l in_proof `MainQueue);
          (* We can't replay a Definition since universes may be differently
           * inferred.  This holds in Coq >= 8.5 *)
	  let replay = match x.expr with
	    | VernacDefinition(_, _, DefineBody _) -> None
	    | _ -> Some x in
	  VCS.propagate_sideff ~replay;
          VCS.checkout_shallowest_proof_branch ();
          Backtrack.record (); if w == VtNow then finish (); `Ok

      (* Unknown: we execute it, check for open goals and propagate sideeff *)
      | VtUnknown, VtNow ->
          let in_proof = not (VCS.Branch.equal head VCS.Branch.master) in
          let id = VCS.new_node ~id:newtip () in
          let head_id = VCS.get_branch_pos head in
          Reach.known_state ~cache:`Yes head_id; (* ensure it is ok *)
          let step () =
            VCS.checkout VCS.Branch.master;
            let mid = VCS.get_branch_pos VCS.Branch.master in
            Reach.known_state ~cache:(interactive ()) mid;
            stm_vernac_interp id x;
            (* Vernac x may or may not start a proof *)
            if not in_proof && Proof_global.there_are_pending_proofs () then
            begin
              let bname = VCS.mk_branch_name x in
              let rec opacity_of_produced_term = function
                (* This AST is ambiguous, hence we check it dynamically *)
                | VernacInstance (false, _,_ , None, _) -> GuaranteesOpacity
                | VernacLocal (_,e) -> opacity_of_produced_term e
                | _ -> Doesn'tGuaranteeOpacity in
              VCS.commit id (Fork (x,bname,opacity_of_produced_term x.expr,[]));
              let proof_mode = default_proof_mode () in
              VCS.branch bname (`Proof (proof_mode, VCS.proof_nesting () + 1));
              Proof_global.activate_proof_mode proof_mode;
            end else begin
              VCS.commit id (mkTransCmd x [] in_proof `MainQueue);
              (* We hope it can be replayed, but we can't really know *)
              VCS.propagate_sideff ~replay:(Some x);
              VCS.checkout_shallowest_proof_branch ();
            end in
          State.define ~safe_id:head_id ~cache:`Yes step id;
          Backtrack.record (); `Ok

      | VtUnknown, VtLater ->
          anomaly(str"classifier: VtUnknown must imply VtNow")
    end in
    stm_prerr_endline (fun () -> "processed }}}");
    VCS.print ();
    rc
  with e ->
    let e = CErrors.push e in
    handle_failure e vcs

let get_ast id =
  match VCS.visit id with
  | { step = `Cmd { cast = { loc; expr } } }
  | { step = `Fork (({ loc; expr }, _, _, _), _) } 
  | { step = `Qed ({ qast = { loc; expr } }, _) } ->
         Some (Loc.tag ?loc expr)
  | _ -> None

let stop_worker n = Slaves.cancel_worker n

(* We must parse on top of a state id, it should be something like:

   - get parsing information for that state.
   - feed the parsable / parser with the right parsing information.
   - call the parser

   Now, the invariant in ensured by the callers, but this is a bit
   problematic.
*)
exception End_of_input

let parse_sentence sid pa =
  (* XXX: Should this restore the previous state?
     Using reach here to try to really get to the
     proper state makes the error resilience code fail *)
  (* Reach.known_state ~cache:`Yes sid; *)
  let cur_tip = VCS.cur_tip () in
  let real_tip = !State.cur_id in
  if not (Stateid.equal sid cur_tip) then
    user_err ~hdr:"Stm.parse_sentence"
      (str "Currently, the parsing api only supports parsing at the tip of the document." ++ fnl () ++
       str "You wanted to parse at: "  ++ str (Stateid.to_string sid) ++
       str " but the current tip is: " ++ str (Stateid.to_string cur_tip)) ;
  if not (Stateid.equal sid real_tip) && !Flags.debug && stm_debug then
    Feedback.msg_debug
      (str "Warning, the real tip doesn't match the current tip." ++
       str "You wanted to parse at: "  ++ str (Stateid.to_string sid) ++
       str " but the real tip is: " ++ str (Stateid.to_string real_tip) ++ fnl () ++
       str "This is usually due to use of Stm.observe to evaluate a state different than the tip. " ++
       str "All is good if not parsing changes occur between the two states, however if they do, a problem might occur.");
  Flags.with_option Flags.we_are_parsing (fun () ->
      try
        match Pcoq.Gram.entry_parse Pcoq.main_entry pa with
        | None            -> raise End_of_input
        | Some (loc, cmd) -> Loc.tag ~loc cmd
      with e when CErrors.noncritical e ->
        let (e, info) = CErrors.push e in
        Exninfo.iraise (e, info))
    ()

(* You may need to know the len + indentation of previous command to compute
 * the indentation of the current one.
 *  Eg.   foo. bar.
 * Here bar is indented of the indentation of foo + its strlen (4) *)
let ind_len_loc_of_id sid =
  if Stateid.equal sid Stateid.initial then None
  else match (VCS.visit sid).step with
  | `Cmd { ctac = true; cast = { indentation; strlen; loc } } ->
         Some (indentation, strlen, loc)
  | _ -> None

(* the indentation logic works like this: if the beginning of the
   command is different than the start we are in a new line, thus
   indentation follows from the starting position. Otherwise, we use
   the previous one plus the offset.

   Note, this could maybe improved by handling more cases in
   compute_indentation. *)

let compute_indentation ?loc sid = Option.cata (fun loc ->
  let open Loc              in
  (* The effective lenght is the lenght on the last line *)
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

let add ~ontop ?newtip verb (loc, ast) =
  let cur_tip = VCS.cur_tip () in
  if not (Stateid.equal ontop cur_tip) then
    user_err ?loc ~hdr:"Stm.add"
      (str "Stm.add called for a different state (" ++ str (Stateid.to_string ontop) ++
       str ") than the tip: " ++ str (Stateid.to_string cur_tip) ++ str "." ++ fnl () ++
       str "This is not supported yet, sorry.");
  let indentation, strlen = compute_indentation ?loc ontop in
  CWarnings.set_current_loc loc;
  (* XXX: Classifiy vernac should be moved inside process transaction *)
  let clas = classify_vernac ast in
  let aast = { verbose = verb; indentation; strlen; loc; expr = ast } in
  match process_transaction ?newtip aast clas with
  | `Ok -> VCS.cur_tip (), `NewTip
  | `Unfocus qed_id -> qed_id, `Unfocus (VCS.cur_tip ())

let set_perspective id_list = Slaves.set_perspective id_list

type focus = {
  start : Stateid.t;
  stop : Stateid.t;
  tip : Stateid.t
}

let query ~at ?(report_with=(Stateid.dummy,default_route)) s =
  Future.purify (fun s ->
    if Stateid.equal at Stateid.dummy then finish ()
    else Reach.known_state ~cache:`Yes at;
    let loc, ast = parse_sentence at s in
    let indentation, strlen = compute_indentation ?loc at in
    CWarnings.set_current_loc loc;
    let clas = classify_vernac ast in
    let aast = { verbose = true; indentation; strlen; loc; expr = ast } in
    match clas with
    | VtStm (w,_), _ ->
       ignore(process_transaction aast (VtStm (w,false), VtNow))
    | _ ->
       ignore(process_transaction aast (VtQuery (false,report_with), VtNow)))
  s

let edit_at id =
  if Stateid.equal id Stateid.dummy then anomaly(str"edit_at dummy") else
  let vcs = VCS.backup () in
  let on_cur_branch id =
    let rec aux cur =
      if id = cur then true
      else match VCS.visit cur with
      | { step = `Fork _ } -> false
      | { next } -> aux next in
    aux (VCS.get_branch_pos (VCS.current_branch ())) in
  let rec is_pure_aux id =
    let view = VCS.visit id in
    match view.step with
    | `Cmd _ -> is_pure_aux view.next
    | `Fork _ -> true
    | _ -> false in
  let is_pure id =
    match (VCS.visit id).step with
    | `Qed (_,last_step) -> is_pure_aux last_step
    | _ -> assert false
  in
  let is_ancestor_of_cur_branch id =
    Stateid.Set.mem id
      (VCS.reachable (VCS.get_branch_pos (VCS.current_branch ()))) in
  let has_failed qed_id =
    match VCS.visit qed_id with
    | { step = `Qed ({ fproof = Some (fp,_) }, _) } -> Future.is_exn fp
    | _ -> false in
  let rec master_for_br root tip =
      if Stateid.equal tip Stateid.initial then tip else
      match VCS.visit tip with
      | { step = (`Fork _ | `Qed _) } -> tip
      | { step = `Sideff (`Ast(_,id)) } -> id
      | { step = `Sideff _ } -> tip
      | { next } -> master_for_br root next in
  let reopen_branch start at_id mode qed_id tip old_branch =
    let master_id, cancel_switch, keep =
      (* Hum, this should be the real start_id in the cluster and not next *)
      match VCS.visit qed_id with
      | { step = `Qed ({ fproof = Some (_,cs); keep },_) } -> start, cs, keep
      | _ -> anomaly (str "ProofTask not ending with Qed") in
    VCS.branch ~root:master_id ~pos:id
      VCS.edit_branch (`Edit (mode, qed_id, master_id, keep, old_branch));
    VCS.delete_boxes_of id;
    cancel_switch := true;
    Reach.known_state ~cache:(interactive ()) id;
    VCS.checkout_shallowest_proof_branch ();
    `Focus { stop = qed_id; start = master_id; tip } in
  let no_edit = function
   | `Edit (pm, _,_,_,_) -> `Proof(pm,1)
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
    if not !Flags.async_proofs_full then
      Reach.known_state ~cache:(interactive ()) id;
    VCS.checkout_shallowest_proof_branch ();
    `NewTip in
  try
    let rc =
      let focused = List.exists ((=) VCS.edit_branch) (VCS.branches ()) in
      let branch_info =
        match snd (VCS.get_info id).vcs_backup with
        | Some{ mine = bn, { VCS.kind = `Proof(m,_) }} -> Some(m,bn)
        | Some{ mine = _, { VCS.kind = `Edit(m,_,_,_,bn) }} -> Some (m,bn)
        | _ -> None in
      match focused, VCS.proof_task_box_of id, branch_info with
      | _, Some _, None -> assert false
      | false, Some { qed = qed_id ; lemma = start }, Some(mode,bn) ->
          let tip = VCS.cur_tip () in
          if has_failed qed_id && is_pure qed_id && not !Flags.async_proofs_never_reopen_branch
          then reopen_branch start id mode qed_id tip bn
          else backto id (Some bn)
      | true, Some { qed = qed_id }, Some(mode,bn) ->
          if on_cur_branch id then begin
            assert false
          end else if is_ancestor_of_cur_branch id then begin
            backto id (Some bn)
          end else begin
            anomaly(str"Cannot leave an `Edit branch open")
          end
      | true, None, _ ->
          if on_cur_branch id then begin
            VCS.reset_branch (VCS.current_branch ()) id;
            Reach.known_state ~cache:(interactive ()) id;
            VCS.checkout_shallowest_proof_branch ();
            `NewTip
          end else if is_ancestor_of_cur_branch id then begin
            backto id None
          end else begin
            anomaly(str"Cannot leave an `Edit branch open")
          end
      | false, None, Some(_,bn) -> backto id (Some bn)
      | false, None, None -> backto id None
    in
    VCS.print ();
    rc
  with e ->
    let (e, info) = CErrors.push e in
    match Stateid.get info with
    | None ->
        VCS.print ();
        anomaly (str ("edit_at "^Stateid.to_string id^": ") ++
          CErrors.print_no_report e)
    | Some (_, id) ->
        stm_prerr_endline (fun () -> "Failed at state " ^ Stateid.to_string id);
        VCS.restore vcs;
        VCS.print ();
        Exninfo.iraise (e, info)

let backup () = VCS.backup ()
let restore d = VCS.restore d

let get_current_state () = VCS.cur_tip ()

(*********************** TTY API (PG, coqtop, coqc) ***************************)
(******************************************************************************)

let current_proof_depth () =
  let head = VCS.current_branch () in
  match VCS.get_branch head with
  | { VCS.kind = `Master } -> 0
  | { VCS.pos = cur; VCS.kind = (`Proof _ | `Edit _); VCS.root = root } ->
      let rec distance root =
        if Stateid.equal cur root then 0
        else 1 + distance (VCS.visit cur).next in
      distance cur

let unmangle n =
  let n = VCS.Branch.to_string n in
  let idx = String.index n '_' + 1 in
  Names.id_of_string (String.sub n idx (String.length n - idx))

let proofname b = match VCS.get_branch b with
  | { VCS.kind = (`Proof _| `Edit _) } -> Some b
  | _ -> None

let get_all_proof_names () =
  List.map unmangle (CList.map_filter proofname (VCS.branches ()))

(* Export hooks *)
let state_computed_hook = Hooks.state_computed_hook
let state_ready_hook = Hooks.state_ready_hook
let forward_feedback_hook = Hooks.forward_feedback_hook
let unreachable_state_hook = Hooks.unreachable_state_hook
let () = Hook.set Obligations.stm_get_fix_exn (fun () -> !State.fix_exn_ref)

(* vim:set foldmethod=marker: *)
