(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2013     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

let pr_err s = Printf.eprintf "%s] %s\n" (System.process_id ()) s; flush stderr

let prerr_endline s = if !Flags.debug then begin pr_err s end else ()

let (f_process_error, process_error_hook) = Hook.make ()
let ((f_interp : (?verbosely:bool -> ?proof:Proof_global.closed_proof ->
  Loc.t * Vernacexpr.vernac_expr -> unit) Hook.value), interp_hook) = Hook.make ()
let with_fail, with_fail_hook = Hook.make ()

open Vernacexpr
open Errors
open Pp
open Names
open Util
open Ppvernac
open Vernac_classifier

(* During interactive use we cache more states so that Undoing is fast *)
let interactive () =
  if !Flags.ide_slave || !Flags.print_emacs || not !Flags.batch_mode then `Yes
  else `No

let fallback_to_lazy_if_marshal_error = ref true
let fallback_to_lazy_if_slave_dies = ref true
let async_proofs_workers_extra_env = ref [||]

type ast = { verbose : bool; loc : Loc.t; mutable expr : vernac_expr }
let pr_ast { expr } = pr_vernac expr

(* Wrapper for Vernacentries.interp to set the feedback id *)
let vernac_interp ?proof id ?route { verbose; loc; expr } =
  let rec internal_command = function
    | VernacResetName _ | VernacResetInitial | VernacBack _
    | VernacBackTo _ | VernacRestart | VernacUndo _ | VernacUndoTo _
    | VernacBacktrack _ | VernacAbortAll | VernacAbort _ -> true
    | VernacTime el -> List.for_all (fun (_,e) -> internal_command e) el
    | _ -> false in
  if internal_command expr then begin
    prerr_endline ("ignoring " ^ string_of_ppcmds(pr_vernac expr))
  end else begin
    Pp.set_id_for_feedback ?route (Feedback.State id);
    Aux_file.record_in_aux_set_at loc;
    prerr_endline ("interpreting " ^ string_of_ppcmds(pr_vernac expr));
    let interp = Hook.get f_interp in
    try interp ~verbosely:verbose ?proof (loc, expr)
    with e ->
      let e = Errors.push e in
      raise (Hook.get f_process_error e)
  end

(* Wrapper for Vernac.parse_sentence to set the feedback id *)
let vernac_parse ?newtip ?route eid s =
  if Option.is_empty newtip then set_id_for_feedback ?route (Feedback.Edit eid)
  else set_id_for_feedback ?route (Feedback.State (Option.get newtip));
  let pa = Pcoq.Gram.parsable (Stream.of_string s) in
  Flags.with_option Flags.we_are_parsing (fun () ->
    try
      match Pcoq.Gram.entry_parse Pcoq.main_entry pa with
      | None -> raise (Invalid_argument "vernac_parse")
      | Some ast -> ast
    with e when Errors.noncritical e ->
      let e = Errors.push e in
      let loc = Option.default Loc.ghost (Loc.get_loc e) in
      let msg = string_of_ppcmds (print e) in
      Pp.feedback (Feedback.ErrorMsg (loc, msg));
      raise e)
  ()

let pr_open_cur_subgoals () =
  try Printer.pr_open_subgoals ()
  with Proof_global.NoCurrentProof -> Pp.str""

module Vcs_ = Vcs.Make(Stateid)
type future_proof = Proof_global.closed_proof_output Future.computation
type proof_mode = string
type depth = int
type cancel_switch = bool ref
type branch_type =
  [ `Master
  | `Proof of proof_mode * depth
  | `Edit of proof_mode * Stateid.t * Stateid.t ]
type cmd_t = {
  cast : ast;
  cids : Id.t list;
  cqueue : [ `MainQueue | `TacQueue of cancel_switch | `QueryQueue of cancel_switch ] }
type fork_t = ast * Vcs_.Branch.t * Vernacexpr.opacity_guarantee * Id.t list
type qed_t = {
  qast : ast;
  keep : vernac_qed_type;
  mutable fproof : (future_proof * cancel_switch) option;
  brname : Vcs_.Branch.t;
  brinfo : branch_type Vcs_.branch_info
}
type seff_t = ast option
type alias_t = Stateid.t
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
  | `Sideff of [ `Ast of ast * Stateid.t | `Id of Stateid.t ]
  | `Alias  of alias_t ]
type visit = { step : step; next : Stateid.t }

type state = {
  system : States.state;
  proof : Proof_global.state;
  shallow : bool
}
type branch = Vcs_.Branch.t * branch_type Vcs_.branch_info
type backup = { mine : branch; others : branch list }
type 'vcs state_info = { (* Make private *)
  mutable n_reached : int;
  mutable n_goals : int;
  mutable state : state option;
  mutable vcs_backup : 'vcs option * backup option;
}
let default_info () =
  { n_reached = 0; n_goals = 0; state = None; vcs_backup = None,None }

(* Functions that work on a Vcs with a specific branch type *)
module Vcs_aux : sig

  val proof_nesting : (branch_type, 't,'i) Vcs_.t -> int
  val find_proof_at_depth :
    (branch_type, 't, 'i) Vcs_.t -> int ->
      Vcs_.Branch.t * branch_type Vcs_.branch_info
  exception Expired
  val visit : (branch_type, transaction,'i) Vcs_.t -> Vcs_.Dag.node -> visit

end = struct (* {{{ *)

  let proof_nesting vcs =
    List.fold_left max 0
      (List.map_filter
        (function
         | { Vcs_.kind = `Proof (_,n) } -> Some n
         | { Vcs_.kind = `Edit _ } -> Some 1
         | _ -> None)
        (List.map (Vcs_.get_branch vcs) (Vcs_.branches vcs)))

  let find_proof_at_depth vcs pl =
    try List.find (function
          | _, { Vcs_.kind = `Proof(m, n) } -> Int.equal n pl
          | _, { Vcs_.kind = `Edit _ } -> anomaly(str"find_proof_at_depth")
          | _ -> false)
        (List.map (fun h -> h, Vcs_.get_branch vcs h) (Vcs_.branches vcs))
    with Not_found -> failwith "find_proof_at_depth"

  exception Expired
  let visit vcs id =
    if Stateid.equal id Stateid.initial then
      anomaly(str"Visiting the initial state id")
    else if Stateid.equal id Stateid.dummy then
      anomaly(str"Visiting the dummy state id")
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
      | _ -> anomaly (str ("Malformed VCS at node "^Stateid.to_string id))
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

  type vcs = (branch_type, transaction, vcs state_info) Vcs_.t

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
  val mk_branch_name : ast -> Branch.t
  val edit_branch : Branch.t
  val branch : ?root:id -> ?pos:id -> Branch.t -> branch_type -> unit
  val reset_branch : Branch.t -> id -> unit
  val reachable : id -> Vcs_.NodeSet.t
  val cur_tip : unit -> id

  val get_info : id -> vcs state_info
  val reached : id -> bool -> unit
  val goals : id -> int -> unit
  val set_state : id -> state -> unit
  val get_state : id -> state option

  (* cuts from start -> stop, raising Expired if some nodes are not there *)
  val slice : start:id -> stop:id -> vcs
  
  val create_cluster : id list -> tip:id -> unit
  val cluster_of : id -> id option
  val delete_cluster_of : id -> unit

  val proof_nesting : unit -> int
  val checkout_shallowest_proof_branch : unit -> unit
  val propagate_sideff : ast option -> unit

  val gc : unit -> unit

  val visit : id -> visit

  val print : ?now:bool -> unit -> unit

  val backup : unit -> vcs
  val restore : vcs -> unit

end = struct (* {{{ *)

  include Vcs_
  exception Expired = Vcs_aux.Expired

  module StateidSet = Set.Make(Stateid)
  open Printf

  let print_dag vcs () =
    let fname =
      "stm_" ^ Str.global_replace (Str.regexp " ") "_" (System.process_id ()) in
    let string_of_transaction = function
      | Cmd { cast = t } | Fork (t, _,_,_) ->
          (try string_of_ppcmds (pr_ast t) with _ -> "ERR")
      | Sideff (Some t) ->
          sprintf "Sideff(%s)"
            (try string_of_ppcmds (pr_ast t) with _ -> "ERR")
      | Sideff None -> "EnvChange"
      | Noop -> " "
      | Alias id -> sprintf "Alias(%s)" (Stateid.to_string id)
      | Qed { qast } -> string_of_ppcmds (pr_ast qast) in
    let is_green id = 
      match get_info vcs id with
      | Some { state = Some _ } -> true
      | _ -> false in
    let is_red id =
      match get_info vcs id with
      | Some s -> Int.equal s.n_reached ~-1
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
    let ids = ref StateidSet.empty in
    let clus = Hashtbl.create 13 in
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
    let add_to_clus_or_ids from cf =
      match cf with
      | None -> ids := StateidSet.add from !ids; false
      | Some c -> Hashtbl.replace clus c
         (try let n = Hashtbl.find clus c in from::n
         with Not_found -> [from]); true in
    let oc = open_out fname_dot in
    output_string oc "digraph states {\nsplines=ortho\n";
    Dag.iter graph (fun from cf _ l ->
      let c1 = add_to_clus_or_ids from cf in
      List.iter (fun (dest, trans) ->
       let c2 = add_to_clus_or_ids dest (Dag.cluster_of graph dest) in
       fprintf oc "%s -> %s [xlabel=%s,labelfloat=%b];\n"
           (node from) (node dest) (edge trans) (c1 && c2)) l
    );
    StateidSet.iter (nodefmt oc) !ids;
    Hashtbl.iter (fun c nodes ->
       fprintf oc "subgraph cluster_%s {\n" (Dag.Cluster.to_string c);
       List.iter (nodefmt oc) nodes;
       fprintf oc "color=blue; }\n"
    ) clus;
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

  type vcs = (branch_type, transaction, vcs state_info) t
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
    | VernacDefinition (_,(_,i),_) -> string_of_id i
    | VernacStartTheoremProof (_,[Some (_,i),_],_) -> string_of_id i
    | _ -> "branch")
  let edit_branch = Branch.make "edit"
  let branch ?root ?pos name kind = vcs := branch !vcs ?root ?pos name kind
  let get_info id =
    match get_info !vcs id with
    | Some x -> x
    | None -> raise Vcs_aux.Expired
  let set_state id s = (get_info id).state <- Some s
  let get_state id = (get_info id).state
  let reached id b =
    let info = get_info id in
    if b then info.n_reached <- info.n_reached + 1
    else info.n_reached <- -1
  let goals id n = (get_info id).n_goals <- n
  let cur_tip () = get_branch_pos (current_branch ())

  let proof_nesting () = Vcs_aux.proof_nesting !vcs

  let checkout_shallowest_proof_branch () =
    if List.mem edit_branch (Vcs_.branches !vcs) then begin
      checkout edit_branch;
      match get_branch edit_branch with
      | { kind = `Edit (mode, _, _) } -> Proof_global.activate_proof_mode mode
      | _ -> assert false
    end else
      let pl = proof_nesting () in
      try
        let branch, mode = match Vcs_aux.find_proof_at_depth !vcs pl with
          | h, { Vcs_.kind = `Proof (m, _) } -> h, m | _ -> assert false in
        checkout branch;
        prerr_endline ("mode:" ^ mode);
        Proof_global.activate_proof_mode mode
      with Failure _ ->
        checkout Branch.master;
        Proof_global.disactivate_proof_mode "Classic"

  (* copies the transaction on every open branch *)
  let propagate_sideff t =
    List.iter (fun b ->
      checkout b;
      let id = new_node () in
      merge id ~ours:(Sideff t) ~into:b Branch.master)
    (List.filter (fun b -> not (Branch.equal b Branch.master)) (branches ()))
  
  let visit id = Vcs_aux.visit !vcs id

  let slice ~start ~stop =
    let l =
      let rec aux id =
        if Stateid.equal id stop then [] else
        match visit id with
        | { next = n; step = `Cmd x } -> (id,Cmd x) :: aux n
        | { next = n; step = `Alias x } -> (id,Alias x) :: aux n
        | { next = n; step = `Sideff (`Ast (x,_)) } ->
             (id,Sideff (Some x)) :: aux n
        | _ -> anomaly(str("Cannot slice from "^ Stateid.to_string start ^
                           " to "^Stateid.to_string stop))
      in aux start in
    let copy_info v id =
      Vcs_.set_info v id
        { (get_info id) with state = None; vcs_backup = None,None } in
    let copy_info_w_state v id =
      Vcs_.set_info v id { (get_info id) with vcs_backup = None,None } in
    let v = Vcs_.empty stop in
    let v = copy_info v stop in
    let v = List.fold_right (fun (id,tr) v ->
      let v = Vcs_.commit v id tr in
      let v = copy_info v id in
      v) l v in
    (* Stm should have reached the beginning of proof *)
    assert (not (Option.is_empty (get_info stop).state));
    (* We put in the new dag the most recent state known to master *)
    let rec fill id =
      if (get_info id).state = None then fill (Vcs_aux.visit v id).next
      else copy_info_w_state v id in
    fill start

  let create_cluster l ~tip = vcs := create_cluster !vcs l tip
  let cluster_of id = Option.map Dag.Cluster.data (cluster_of !vcs id)
  let delete_cluster_of id =
    Option.iter (fun x -> vcs := delete_cluster !vcs x) (Vcs_.cluster_of !vcs id)

  let gc () =
    let old_vcs = !vcs in
    let new_vcs, erased_nodes = gc old_vcs in
    Vcs_.NodeSet.iter (fun id ->
        match (Vcs_aux.visit old_vcs id).step with
        | `Qed ({ fproof = Some (_, cancel_switch) }, _)
        | `Cmd { cqueue = `TacQueue cancel_switch }
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
    ?feedback_processed: bool -> (unit -> unit) -> Stateid.t -> unit

  val install_cached : Stateid.t -> unit
  val is_cached : ?cache:Summary.marshallable -> Stateid.t -> bool


  val exn_on : Stateid.t -> ?valid:Stateid.t -> exn -> exn
  (* to send states across worker/master *)
  type frozen_state
  val get_cached : Stateid.t -> frozen_state
  val assign : Stateid.t -> frozen_state -> unit

end = struct (* {{{ *)

  (* cur_id holds Stateid.dummy in case the last attempt to define a state
   * failed, so the global state may contain garbage *)
  let cur_id = ref Stateid.dummy

  (* helpers *)
  let freeze_global_state marshallable =
    { system = States.freeze ~marshallable;
      proof = Proof_global.freeze ~marshallable;
      shallow = (marshallable = `Shallow) }
  let unfreeze_global_state { system; proof } =
    States.unfreeze system; Proof_global.unfreeze proof

  (* hack to make futures functional *)
  let in_t, out_t = Dyn.create "state4future"
  let () = Future.set_freeze
    (fun () -> in_t (freeze_global_state `No, !cur_id))
    (fun t -> let s,i = out_t t in unfreeze_global_state s; cur_id := i)
  
  type frozen_state = state

  let freeze marhallable id = VCS.set_state id (freeze_global_state marhallable)

  let is_cached ?(cache=`No) id =
    if Stateid.equal id !cur_id then
      try match VCS.get_info id with
        | { state = None } when cache = `Yes -> freeze `No id; true
        | { state = None } when cache = `Shallow -> freeze `Shallow id; true
        | _ -> true
      with VCS.Expired -> false
    else
      try match VCS.get_info id with
        | { state = Some _ } -> true
        | _ -> false 
      with VCS.Expired -> false

  let install_cached id =
    if Stateid.equal id !cur_id then () else (* optimization *)
    let s =
      match VCS.get_info id with
      | { state = Some s } -> s
      | _ -> anomaly (str "unfreezing a non existing state") in
    unfreeze_global_state s; cur_id := id

  let get_cached id =
    try match VCS.get_info id with
    | { state = Some s } -> s
    | _ -> anomaly (str "not a cached state")
    with VCS.Expired -> anomaly (str "not a cached state (expired)")

  let assign id s =
    try if VCS.get_state id = None then VCS.set_state id s
    with VCS.Expired -> ()

  let exn_on id ?valid e =
    match Stateid.get e with
    | Some _ -> e
    | None ->
        let loc = Option.default Loc.ghost (Loc.get_loc e) in
        let msg = string_of_ppcmds (print e) in
        Pp.feedback ~state_id:id (Feedback.ErrorMsg (loc, msg));
        Stateid.add (Hook.get f_process_error e) ?valid id

  let define ?safe_id ?(redefine=false) ?(cache=`No) ?(feedback_processed=true)
        f id
  =
    let str_id = Stateid.to_string id in
    if is_cached id && not redefine then
      anomaly (str"defining state "++str str_id++str" twice");
    try
      prerr_endline("defining "^str_id^" (cache="^
        if cache = `Yes then "Y)" else if cache = `Shallow then "S)" else "N)");
      f ();
      if cache = `Yes then freeze `No id
      else if cache = `Shallow then freeze `Shallow id;
      prerr_endline ("setting cur id to "^str_id);
      cur_id := id;
      if feedback_processed then feedback ~state_id:id Feedback.Processed;
      VCS.reached id true;
      if Proof_global.there_are_pending_proofs () then
        VCS.goals id (Proof_global.get_open_goals ());
    with e ->
      let e = Errors.push e in
      let good_id = !cur_id in
      cur_id := Stateid.dummy;
      VCS.reached id false;
      match Stateid.get e, safe_id with
      | None, None -> raise (exn_on id ~valid:good_id e)
      | None, Some good_id -> raise (exn_on id ~valid:good_id e)
      | Some _, None -> raise e
      | Some (_,at), Some id -> raise (Stateid.add e ~valid:id at)

end (* }}} *)


(****************************** CRUFT *****************************************)
(******************************************************************************)

(* TODO: Currently, this mimics the process_goal function of ide/ide_slave.ml, 
 * but we have the opportunity to provide more structure in the xml, here. *)
let process_goal sigma g =
  let env = Goal.V82.env sigma g in
  let id = Goal.uid g in
  let ccl =
    let norm_constr = Reductionops.nf_evar sigma (Goal.V82.concl sigma g) in
    let ccl_string = string_of_ppcmds (Printer.pr_goal_concl_style_env env sigma norm_constr) in
    Xml_datatype.Element ("conclusion", [], [Xml_datatype.PCData ccl_string]) in
  let process_hyp env h_env acc =
    let hyp_string = (string_of_ppcmds (Printer.pr_var_decl env sigma h_env)) in
    (Xml_datatype.Element ("hypothesis", [], [Xml_datatype.PCData hyp_string])) :: acc in
  let hyps = Xml_datatype.Element ("hypotheses", [], 
    (List.rev (Environ.fold_named_context process_hyp env ~init:[]))) in
  Xml_datatype.Element ("goal", [("id", id)], [hyps; ccl])

let print_goals_of_state, forward_feedback =
  let already_printed = ref Stateid.Set.empty in
  let add_to_already_printed =
    let m = Mutex.create () in
    fun id ->
      Mutex.lock m;
      already_printed := Stateid.Set.add id !already_printed;
      Mutex.unlock m in
  (fun id ->
    if Stateid.Set.mem id !already_printed then ()
    else begin
      add_to_already_printed id;
      try
        Option.iter (fun { proof = pstate } ->
          let pfts = Proof_global.proof_of_state pstate in
          let structured_goals = Proof.map_structured_proof pfts process_goal in
          let xml_bg_goal = fun (l, r) -> Xml_datatype.Element("bg_goal", [], 
              [Xml_datatype.Element("left_bg_goals", [], l); 
               Xml_datatype.Element("right_bg_goals", [], r)]) in

          let xml_structured_goals = Xml_datatype.Element("goals", [],
            [ Xml_datatype.Element("focussed_goals", [], 
                structured_goals.Proof.fg_goals);
              Xml_datatype.Element("bg_goals", [], 
                List.map xml_bg_goal structured_goals.Proof.bg_goals);
              Xml_datatype.Element("shelved_goals", [], 
                structured_goals.Proof.shelved_goals);
              Xml_datatype.Element("given_up_goals", [], 
                structured_goals.Proof.given_up_goals)
            ]
          ) in
          Pp.feedback ~state_id:id
           (Feedback.StructuredGoals (Loc.ghost, xml_structured_goals));
          Pp.feedback ~state_id:id
            (Feedback.Goals
              (Loc.ghost, Pp.string_of_ppcmds
                (Printer.pr_open_subgoals
                  ~proof:(Proof_global.proof_of_state pstate) ()))))
            (VCS.get_info id).state
      with Proof_global.NoCurrentProof -> ()
  end),
  fun id -> function
    | Feedback.Goals _ as msg ->
        add_to_already_printed id;
        Pp.feedback ~state_id:id msg
    | msg -> Pp.feedback ~state_id:id msg

(* The backtrack module simulates the classic behavior of a linear document *)
module Backtrack : sig

  val record : unit -> unit
  val backto : Stateid.t -> unit
  val back_safe : unit -> unit

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
       anomaly(str"Backtrack.backto "++str(Stateid.to_string oid)++
               str": a state with no vcs_backup")
    | Some vcs, _ -> VCS.restore vcs

  let branches_of id =
    let info = VCS.get_info id in
    match info.vcs_backup with
    | _, None ->
       anomaly(str"Backtrack.branches_of "++str(Stateid.to_string id)++
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
        let ids =
          if id = Stateid.initial || id = Stateid.dummy then [] else
          match VCS.visit id with
          | { step = `Fork ((_,_,_,l),_) } -> l
          | { step = `Cmd { cids = l } } -> l
          | _ -> [] in
        match f acc (id, vcs, ids) with
        | `Stop x -> x
        | `Cont acc -> next acc
 
  let back_safe () =
    let id =
      fold_until (fun n (id,_,_) ->
        if n >= 0 && State.is_cached id then `Stop id else `Cont (succ n))
        0 (VCS.get_branch_pos (VCS.current_branch ())) in
    backto id

  let undo_vernac_classifier v =
    try
      match v with
      | VernacResetInitial ->
          VtStm (VtBack Stateid.initial, true), VtNow
      | VernacResetName (_,name) ->
          msg_warning
            (str"Reset not implemented for automatically generated constants");
          let id = VCS.get_branch_pos (VCS.current_branch ()) in
          (try
            let oid =
              fold_until (fun b (id,_,label) ->
                if b then `Stop id else `Cont (List.mem name label))
              false id in
            VtStm (VtBack oid, true), VtNow
          with Not_found ->
            VtStm (VtBack id, true), VtNow)
      | VernacBack n ->
          let id = VCS.get_branch_pos (VCS.current_branch ()) in
          let oid = fold_until (fun n (id,_,_) ->
            if Int.equal n 0 then `Stop id else `Cont (n-1)) n id in
          VtStm (VtBack oid, true), VtNow
      | VernacUndo n ->
          let id = VCS.get_branch_pos (VCS.current_branch ()) in
          let oid = fold_until (fun n (id,_,_) ->
            if Int.equal n 0 then `Stop id else `Cont (n-1)) n id in
          if n = 1 && !Flags.coqtop_ui && not !Flags.batch_mode &&
             not !Flags.print_emacs then
           VtStm (VtBack oid, false), VtNow
          else VtStm (VtBack oid, true), VtLater
      | VernacUndoTo _
      | VernacRestart as e ->
          let m = match e with VernacUndoTo m -> m | _ -> 0 in
          let id = VCS.get_branch_pos (VCS.current_branch ()) in
          let vcs =
            match (VCS.get_info id).vcs_backup with 
            | None, _ -> anomaly(str"Backtrack: tip with no vcs_backup")
            | Some vcs, _ -> vcs in
          let cb, _ =
            Vcs_aux.find_proof_at_depth vcs (Vcs_aux.proof_nesting vcs) in
          let n = fold_until (fun n (_,vcs,_) ->
            if List.mem cb (Vcs_.branches vcs) then `Cont (n+1) else `Stop n)
            0 id in
          let oid = fold_until (fun n (id,_,_) ->
            if Int.equal n 0 then `Stop id else `Cont (n-1)) (n-m-1) id in
          VtStm (VtBack oid, true), VtLater
      | VernacAbortAll ->
          let id = VCS.get_branch_pos (VCS.current_branch ()) in
          let oid = fold_until (fun () (id,vcs,_) ->
            match Vcs_.branches vcs with [_] -> `Stop id | _ -> `Cont ())
            () id in
          VtStm (VtBack oid, true), VtLater
      | VernacBacktrack (id,_,_)
      | VernacBackTo id ->
          VtStm (VtBack (Stateid.of_int id), not !Flags.print_emacs), VtNow
      | _ -> VtUnknown, VtNow
    with
    | Not_found ->
       msg_warning(str"undo_vernac_classifier: going back to the initial state.");
       VtStm (VtBack Stateid.initial, true), VtNow

end (* }}} *)

let hints = ref Aux_file.empty_aux_file
let set_compilation_hints file =
  hints := Aux_file.load_aux_file_for file
let get_hint_ctx loc =
  let s = Aux_file.get !hints loc "context_used" in
  let ids = List.map Names.Id.of_string (Str.split (Str.regexp " ") s) in
  let ids = List.map (fun id -> Loc.ghost, id) ids in
  SsExpr (SsSet ids)

let get_hint_bp_time proof_name =
  try float_of_string (Aux_file.get !hints Loc.ghost proof_name)
  with Not_found -> 1.0

let record_pb_time proof_name loc time =
  let proof_build_time = Printf.sprintf "%.3f" time in
  Aux_file.record_in_aux_at loc "proof_build_time" proof_build_time;
  if proof_name <> "" then begin
    Aux_file.record_in_aux_at Loc.ghost proof_name proof_build_time;
    hints := Aux_file.set !hints Loc.ghost proof_name proof_build_time
  end
 
exception RemoteException of std_ppcmds
let _ = Errors.register_handler (function
  | RemoteException ppcmd -> ppcmd
  | _ -> raise Unhandled)

(****************************** THE SCHEDULER *********************************)
(******************************************************************************)

module rec ProofTask : sig
 
  type task = {
    t_exn_info : Stateid.t * Stateid.t;
    t_start    : Stateid.t;
    t_stop     : Stateid.t;
    t_assign   : Proof_global.closed_proof_output Future.assignement -> unit;
    t_loc      : Loc.t;
    t_uuid     : Future.UUID.t;
    t_name     : string }   

  include AsyncTaskQueue.Task with type task := task

  val build_proof_here :
    Stateid.t * Stateid.t -> Loc.t -> Stateid.t ->
      Proof_global.closed_proof_output Future.computation
  val build_proof_here_core :
    Loc.t -> Stateid.t -> unit -> Proof_global.closed_proof_output
   
end = struct (* {{{ *)

  let forward_feedback = forward_feedback

  type task = {
    t_exn_info : Stateid.t * Stateid.t;
    t_start    : Stateid.t;
    t_stop     : Stateid.t;
    t_assign   : Proof_global.closed_proof_output Future.assignement -> unit;
    t_loc      : Loc.t;
    t_uuid     : Future.UUID.t;
    t_name     : string }   

  type request = (Future.UUID.t,VCS.vcs) Stateid.request
  
  type error = {
    e_error_at    : Stateid.t;
    e_safe_id     : Stateid.t;
    e_msg         : std_ppcmds;
    e_safe_states : (Stateid.t * State.frozen_state) list }

  type response =
    | RespBuiltProof of Proof_global.closed_proof_output * float
    | RespError of error

  let name = "proofworker"
  let extra_env () = !async_proofs_workers_extra_env

  let name_of_task t = t.t_name
  let name_of_request r = r.Stateid.name

  let request_of_task age { t_exn_info;t_start;t_stop;t_loc;t_uuid;t_name } =
   assert(age = `Fresh);
   try Some {
     Stateid.exn_info = t_exn_info;
     stop = t_stop;
     document = VCS.slice ~start:t_stop ~stop:t_start;
     loc = t_loc;
     uuid = t_uuid;
     name = t_name }
   with VCS.Expired -> None

  let use_response { t_assign; t_loc; t_name } = function
    | RespBuiltProof (pl, time) ->
        Pp.feedback (Feedback.InProgress ~-1);
        t_assign (`Val pl);
        record_pb_time t_name t_loc time;
        (* We restart the slave, to avoid memory leaks.  We could just
           Pp.feedback (Feedback.InProgress ~-1) *)
        `StayReset
    | RespError { e_error_at; e_safe_id = valid; e_msg; e_safe_states } ->
        Pp.feedback (Feedback.InProgress ~-1);
        let e = Stateid.add ~valid (RemoteException e_msg) e_error_at in
        t_assign (`Exn e);
        List.iter (fun (id,s) -> State.assign id s) e_safe_states;
        (* We restart the slave, to avoid memory leaks.  We could just
           Pp.feedback (Feedback.InProgress ~-1) *)
        `StayReset           

  let on_task_cancellation_or_expiration = function
    | None -> ()
    | Some { t_start = start; t_assign } ->
        let s = "Worker cancelled by the user" in
        let e = Stateid.add ~valid:start (RemoteException (strbrk s)) start in
        t_assign (`Exn e);
        Pp.feedback ~state_id:start (Feedback.ErrorMsg (Loc.ghost, s));
        Pp.feedback (Feedback.InProgress ~-1)

  let build_proof_here_core loc eop () =
    let wall_clock1 = Unix.gettimeofday () in
    if !Flags.batch_mode then Reach.known_state ~cache:`No eop
    else Reach.known_state ~cache:`Shallow eop;
    let wall_clock2 = Unix.gettimeofday () in
    Aux_file.record_in_aux_at loc "proof_build_time"
      (Printf.sprintf "%.3f" (wall_clock2 -. wall_clock1));
    Proof_global.return_proof ()
  let build_proof_here (id,valid) loc eop =
    Future.create (State.exn_on id ~valid) (build_proof_here_core loc eop)
  let perform { Stateid.exn_info; stop = eop; document = vcs; loc } =
    try
      VCS.restore vcs;
      VCS.print ();
      let rc, time =
        let wall_clock = Unix.gettimeofday () in
        let l = Future.force (build_proof_here exn_info loc eop) in
        l, Unix.gettimeofday () -. wall_clock in
      VCS.print ();
      RespBuiltProof(rc,time)
    with
    | e when Errors.noncritical e ->
        (* This can happen if the proof is broken.  The error has also been
         * signalled as a feedback, hence we can silently recover *)
        let e_error_at, e_safe_id = match Stateid.get e with
          | Some (safe, err) -> err, safe
          | None -> Stateid.dummy, Stateid.dummy in
        prerr_endline "failed with the following exception:";
        prerr_endline (string_of_ppcmds (print e));
        prerr_endline ("last safe id is: " ^ Stateid.to_string e_safe_id);
        prerr_endline ("cached? " ^ string_of_bool (State.is_cached e_safe_id));
        let prog old_v n =
          if n < 3 then n else old_v + n/3 + if n mod 3 > 0 then 1 else 0 in
        let e_safe_states =
          let open State in
          let rec aux n m prev_id =
            let next =
              try Some (VCS.visit prev_id).next
              with VCS.Expired -> None in
            match next with
            | None -> []
            | Some id when n = m ->
                prerr_endline ("sending back state " ^  string_of_int m);
                let tail = aux (n+1) (prog m (n+1)) id in
                if is_cached id then (id, get_cached id) :: tail else tail
            | Some id -> aux (n+1) m id in
          (if is_cached e_safe_id then [e_safe_id,get_cached e_safe_id] else [])
          @ aux 1 (prog 1 1) e_safe_id in
        RespError { e_error_at; e_safe_id; e_msg = print e; e_safe_states }

  let on_slave_death task =
    if not !fallback_to_lazy_if_slave_dies then `Exit 1
    else match task with
    | None -> `Stay
    | Some { t_exn_info; t_loc; t_stop; t_assign } ->     
        msg_warning(strbrk "Falling back to local, lazy, evaluation.");
        t_assign (`Comp(build_proof_here t_exn_info t_loc t_stop));
        Pp.feedback (Feedback.InProgress ~-1);
        `Stay

  let on_marshal_error s { t_exn_info; t_stop; t_assign; t_loc } =
    if !fallback_to_lazy_if_marshal_error then begin
      msg_error(strbrk("Marshalling error: "^s^". "^
        "The system state could not be sent to the worker process. "^
        "Falling back to local, lazy, evaluation."));
      t_assign(`Comp(build_proof_here t_exn_info t_loc t_stop));
      Pp.feedback (Feedback.InProgress ~-1)
    end else begin
      pr_err ("Fatal marshal error: " ^ s);
      flush_all (); exit 1
    end

end (* }}} *)

(* Slave processes (if initialized, otherwise local lazy evaluation) *)
and Slaves : sig

  (* (eventually) remote calls *)
  val build_proof : loc:Loc.t ->
    exn_info:(Stateid.t * Stateid.t) -> start:Stateid.t -> stop:Stateid.t ->
      name:string -> future_proof * cancel_switch

  (* blocking function that waits for the task queue to be empty *)
  val wait_all_done : unit -> unit
  
  (* initialize the whole machinery (optional) *)
  val init : unit -> unit

  type 'a tasks = ('a,VCS.vcs) Stateid.request list
  val dump_snapshot : unit -> Future.UUID.t tasks
  val check_task : string -> int tasks -> int -> bool
  val info_tasks : 'a tasks -> (string * float * int) list
  val finish_task :
    string ->
    Library.seg_univ -> Library.seg_discharge -> Library.seg_proofs ->
    int tasks -> int -> Library.seg_univ

  val cancel_worker : string -> unit

  val reset_task_queue : unit -> unit

  val set_perspective : Stateid.t list -> unit

end = struct (* {{{ *)

  module TaskQueue = AsyncTaskQueue.MakeQueue(ProofTask)

  let check_task_aux extra name l i =
    let { Stateid.stop; document; loc; name = r_name } = List.nth l i in
    Pp.msg_info(
      str(Printf.sprintf "Checking task %d (%s%s) of %s" i r_name extra name));
    VCS.restore document;
    try
      Reach.known_state ~cache:`No stop;
      (* The original terminator, a hook, has not been saved in the .vi*)
      Proof_global.set_terminator
        (Lemmas.standard_proof_terminator []
          (Lemmas.mk_hook (fun _ _ -> ())));
      let proof = Proof_global.close_proof (fun x -> x) in
      vernac_interp stop ~proof
        { verbose = false; loc;
          expr = (VernacEndProof (Proved (true,None))) };
      Some proof
    with e ->
      let e = Errors.push e in
      (try match Stateid.get e with
      | None ->
          Pp.pperrnl Pp.(
            str"File " ++ str name ++ str ": proof of " ++ str r_name ++
            spc () ++ print e)
      | Some (_, cur) ->
          match VCS.visit cur with
          | { step = `Cmd { cast = { loc } } }
          | { step = `Fork (( { loc }, _, _, _), _) } 
          | { step = `Qed ( { qast = { loc } }, _) } 
          | { step = `Sideff (`Ast ( { loc }, _)) } ->
              let start, stop = Loc.unloc loc in
              Pp.pperrnl Pp.(
                str"File " ++ str name ++ str ": proof of " ++ str r_name ++
                str ": chars " ++ int start ++ str "-" ++ int stop ++
                spc () ++ print e)
          | _ ->
              Pp.pperrnl Pp.(
                str"File " ++ str name ++ str ": proof of " ++ str r_name ++
                spc () ++ print e)
    with e ->
      Pp.msg_error (str"unable to print error message: " ++
                    str (Printexc.to_string e))); None

  let finish_task name (u,cst,_) d p l i =
    let bucket = (List.nth l i).Stateid.uuid in
    match check_task_aux (Printf.sprintf ", bucket %d" bucket) name l i with
    | None -> exit 1
    | Some (po,pt) ->
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
            ~greedy:true ~pure:true uc Univ.hcons_universe_context_set in
        let pr = Future.chain ~greedy:true ~pure:true pr discharge in
        let pr = Future.chain ~greedy:true ~pure:true pr Constr.hcons in
        Future.sink pr;
        let extra = Future.join uc in
        u.(bucket) <- uc;
        p.(bucket) <- pr;
        u, Univ.ContextSet.union cst extra, false
  
  let check_task name l i =
    match check_task_aux "" name l i with
    | Some _ -> true
    | None -> false

  let info_tasks l =
    CList.map_i (fun i { Stateid.loc; name } ->
      let time1 =
        try float_of_string (Aux_file.get !hints loc "proof_build_time")
        with Not_found -> 0.0 in
      let time2 =
        try float_of_string (Aux_file.get !hints loc "proof_check_time")
        with Not_found -> 0.0 in
      name, max (time1 +. time2) 0.0001,i) 0 l

  let set_perspective idl =
    let open Stateid in
    let p = List.fold_right Set.add idl Set.empty in
    TaskQueue.set_order (fun task1 task2 ->
      let { ProofTask.t_start = a1; t_stop = b1 } = task1 in
      let { ProofTask.t_start = a2; t_stop = b2 } = task2 in
      match Set.mem a1 p || Set.mem b1 p, Set.mem a2 p || Set.mem b2 p with
      | true, true | false, false -> 0
      | true, false -> -1
      | false, true -> 1)

  let build_proof ~loc ~exn_info:(id,valid as t_exn_info) ~start ~stop ~name =
    let cancel_switch = ref false in
    if TaskQueue.n_workers () = 0 then
      if !Flags.compilation_mode = Flags.BuildVi then begin
        let force () : Proof_global.closed_proof_output Future.assignement =
          try `Val (ProofTask.build_proof_here_core loc stop ())
          with e -> let e = Errors.push e in `Exn e in
        let f,assign = Future.create_delegate ~force (State.exn_on id ~valid) in
        let t_uuid = Future.uuid f in
        TaskQueue.enqueue_task {
          ProofTask.t_exn_info; t_start = start; t_stop = stop;
          t_assign = assign; t_loc = loc; t_uuid; t_name = name } cancel_switch;
        f, cancel_switch
      end else
        ProofTask.build_proof_here t_exn_info loc stop, cancel_switch
    else 
      let f, t_assign = Future.create_delegate (State.exn_on id ~valid) in
      let t_uuid = Future.uuid f in
      Pp.feedback (Feedback.InProgress 1);
      TaskQueue.enqueue_task {
        ProofTask.t_exn_info; t_start = start; t_stop = stop; t_assign;
        t_loc = loc; t_uuid; t_name = name } cancel_switch;
      f, cancel_switch

  let init () = TaskQueue.init !Flags.async_proofs_n_workers
  let wait_all_done = TaskQueue.join

  let cancel_worker = TaskQueue.cancel_worker

  (* For external users this name is nicer than request *)
  type 'a tasks = ('a,VCS.vcs) Stateid.request list
  let dump_snapshot () =
    let tasks = TaskQueue.snapshot () in
    prerr_endline (Printf.sprintf "dumping %d tasks\n" (List.length tasks));
    CList.map_filter (ProofTask.request_of_task `Fresh) tasks

  let reset_task_queue () = TaskQueue.clear ()

end (* }}} *)

and TacTask : sig

  type output = Constr.constr * Evd.evar_universe_context
  type task = {
    t_state    : Stateid.t;
    t_state_fb : Stateid.t;
    t_assign   : output Future.assignement -> unit;
    t_ast      : ast;
    t_goal     : Goal.goal;
    t_kill     : unit -> unit;
    t_name     : string }  

  include AsyncTaskQueue.Task with type task := task

end = struct (* {{{ *)

  type output = Constr.constr * Evd.evar_universe_context
  
  let forward_feedback = forward_feedback

  type task = {
    t_state    : Stateid.t;
    t_state_fb : Stateid.t;
    t_assign   : output Future.assignement -> unit;
    t_ast      : ast;
    t_goal     : Goal.goal;
    t_kill     : unit -> unit;
    t_name     : string }  

  type request = {
    r_state    : Stateid.t;
    r_state_fb : Stateid.t;
    r_document : VCS.vcs option;
    r_ast      : ast;
    r_goal     : Goal.goal;
    r_name     : string }

  type response =
    | RespBuiltSubProof of output
    | RespError of std_ppcmds

  let name = "tacworker"
  let extra_env () = [||]

  (* run by the master, on a thread *)
  let request_of_task age { t_state; t_state_fb; t_ast; t_goal; t_name } =
    try Some {
      r_state    = t_state;
      r_state_fb = t_state_fb;
      r_document =
        if age = `Old then None
        else Some (VCS.slice ~start:t_state ~stop:t_state);
      r_ast      = t_ast;
      r_goal     = t_goal;
      r_name     = t_name }
    with VCS.Expired -> None
          
  let use_response { t_assign; t_state; t_state_fb; t_kill } = function
    | RespBuiltSubProof o -> t_assign (`Val o); `Stay
    | RespError msg ->
        let e = Stateid.add ~valid:t_state (RemoteException msg) t_state_fb in
        t_assign (`Exn e);
        t_kill ();
        `Stay
                    
  let on_marshal_error err { t_name } =
    pr_err ("Fatal marshal error: " ^ t_name );
    flush_all (); exit 1

  let on_slave_death task = `Stay
  let on_task_cancellation_or_expiration task = () (* We shall die *)
 
  let perform { r_state = id; r_state_fb; r_document = vcs; r_ast; r_goal } =
    Option.iter VCS.restore vcs;
    try
      Reach.known_state ~cache:`No id;
      let t, uc = Future.purify (fun () ->
        vernac_interp r_state_fb r_ast;
        let _,_,_,_,sigma = Proof.proof (Proof_global.give_me_the_proof ()) in
        match Evd.(evar_body (find sigma r_goal)) with
        | Evd.Evar_empty -> Errors.errorlabstrm "Stm" (str "no progress")
        | Evd.Evar_defined t ->
            let t = Evarutil.nf_evar sigma t in
            if Evarutil.is_ground_term sigma t then
              t, Evd.evar_universe_context sigma
            else Errors.errorlabstrm "Stm" (str"The solution is not ground"))
        () in
      RespBuiltSubProof (t,uc) 
    with e when Errors.noncritical e -> RespError (Errors.print e)

  let name_of_task { t_name } = t_name
  let name_of_request { r_name } = r_name
  
end (* }}} *)

and Partac : sig

  val vernac_interp :
    cancel_switch -> int -> Stateid.t -> Stateid.t -> ast -> unit

end = struct (* {{{ *)
    
  module TaskQueue = AsyncTaskQueue.MakeQueue(TacTask)

  let vernac_interp cancel nworkers safe_id id { verbose; loc; expr = e } =
    let e, etac, time, fail =
      let rec find time fail = function
        | VernacSolve(_,_,re,b) -> re, b, time, fail
        | VernacTime [_,e] -> find true fail e
        | VernacFail e -> find time true e
        | _ -> errorlabstrm "Stm" (str"unsupported") in find false false e in
    Hook.get with_fail fail (fun () ->
    (if time then System.with_time false else (fun x -> x)) (fun () ->
    ignore(TaskQueue.with_n_workers nworkers (fun ~join ~cancel_all ->
    Proof_global.with_current_proof (fun _ p ->
      let goals, _, _, _, _ = Proof.proof p in
      let open TacTask in
      let res = CList.map_i (fun i g ->
        let f,assign= Future.create_delegate (State.exn_on id ~valid:safe_id) in
        let t_ast =
          { verbose;loc;expr = VernacSolve(SelectNth i,None,e,etac) } in
        let t_name = Goal.uid g in
        TaskQueue.enqueue_task
          { t_state = safe_id; t_state_fb = id;
            t_assign = assign; t_ast; t_goal = g; t_name; t_kill = cancel_all }
          cancel;
        Goal.uid g,f)
        1 goals in
      join ();
      let assign_tac : unit Proofview.tactic =
        Proofview.V82.tactic (fun gl ->
          let open Tacmach in
          let sigma, g = project gl, sig_it gl in
          let gid = Goal.uid g in
          let f =
            try List.assoc gid res
            with Not_found -> Errors.anomaly(str"Partac: wrong focus") in
          if Future.is_over f then
            let pt, uc = Future.join f in
            prerr_endline Pp.(string_of_ppcmds(hov 0 (
              str"g=" ++ str gid ++ spc () ++
              str"t=" ++ (Printer.pr_constr pt) ++ spc () ++
              str"uc=" ++ Evd.pr_evar_universe_context uc)));
            let sigma = Goal.V82.partial_solution sigma g pt in
            let sigma = Evd.merge_universe_context sigma uc in
            re_sig [] sigma
          else (* One has failed and cancelled the others, but not this one *)
            re_sig [g] sigma) in
      Proof.run_tactic (Global.env()) assign_tac p)))) ())
  
end (* }}} *)

and QueryTask : sig

  type task = { t_where : Stateid.t; t_for : Stateid.t ; t_what : ast }
  include AsyncTaskQueue.Task with type task := task

end = struct (* {{{ *)
  
  type task =
    { t_where : Stateid.t; t_for : Stateid.t ; t_what : ast }
  
  type request =
    { r_where : Stateid.t ; r_for : Stateid.t ; r_what : ast; r_doc : VCS.vcs }
  type response = unit

  let name = "queryworker"
  let extra_env _ = [||]

  let request_of_task _ { t_where; t_what; t_for } =
    try Some {
      r_where = t_where;
      r_for   = t_for;
      r_doc   = VCS.slice ~start:t_where ~stop:t_where;
      r_what  = t_what }
    with VCS.Expired -> None
  
  let use_response _ _ = `StayReset

  let on_marshal_error _ _ =
    pr_err ("Fatal marshal error in query");
    flush_all (); exit 1

  let on_slave_death _ = `Stay
  let on_task_cancellation_or_expiration _ = ()
  
  let forward_feedback = forward_feedback

  let perform { r_where; r_doc; r_what; r_for } =
    VCS.restore r_doc;
    VCS.print ();
    Reach.known_state ~cache:`No r_where;
    try
      vernac_interp r_for { r_what with verbose = true };
      Pp.feedback ~state_id:r_for Feedback.Processed     
    with e when Errors.noncritical e ->
      let msg = string_of_ppcmds (print e) in
      Pp.feedback ~state_id:r_for (Feedback.ErrorMsg (Loc.ghost, msg))
    
  let name_of_task { t_what } = string_of_ppcmds (pr_ast t_what)
  let name_of_request { r_what } = string_of_ppcmds (pr_ast r_what)

end (* }}} *)

and Query : sig 

  val init : unit -> unit
  val vernac_interp : cancel_switch -> Stateid.t ->  Stateid.t -> ast -> unit

end = struct (* {{{ *)

  module TaskQueue = AsyncTaskQueue.MakeQueue(QueryTask)

  let vernac_interp switch prev id q =
    assert(TaskQueue.n_workers () > 0);
    TaskQueue.enqueue_task
      QueryTask.({ QueryTask.t_where = prev; t_for = id; t_what = q }) switch

  let init () = TaskQueue.init 
    (if !Flags.async_queries_always_delegate then 1 else 0)

end (* }}} *)

(* Runs all transactions needed to reach a state *)
and Reach : sig

  val known_state :
    ?redefine_qed:bool -> cache:Summary.marshallable -> Stateid.t -> unit

end = struct (* {{{ *)

let pstate = ["meta counter"; "evar counter"; "program-tcc-table"]

let delegate_policy_check time =
  if interactive () = `Yes then
    (Flags.async_proofs_is_master () ||
    !Flags.async_proofs_mode = Flags.APonLazy) &&
    (time >= 1.0 || !Flags.async_proofs_always_delegate)
  else if !Flags.compilation_mode = Flags.BuildVi then true
  else !Flags.async_proofs_mode <> Flags.APoff &&
       (time >= 1.0 || !Flags.async_proofs_always_delegate)

let collect_proof keep cur hd brkind id =
 prerr_endline ("Collecting proof ending at "^Stateid.to_string id);
 let no_name = "" in
 let name = function
   | [] -> no_name
   | id :: _ -> Id.to_string id in
 let loc = (snd cur).loc in
 let is_defined = function
   | _, { expr = VernacEndProof (Proved (false,_)) } -> true
   | _ -> false in
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
 let parent = function Some (p, _) -> p | None -> assert false in
 let rec collect last accn id =
    let view = VCS.visit id in
    match view.step with
    | `Cmd { cast = x } -> collect (Some (id,x)) (id::accn) view.next
    (* An Alias could jump everywhere... we hope we can ignore it*)
    | `Alias _ -> `Sync (no_name,None,`Alias)
    | `Fork((_,_,_,_::_::_), _) ->
         `Sync (no_name,proof_using_ast last,`MutualProofs)
    | `Fork((_,_,Doesn'tGuaranteeOpacity,_), _) ->
        `Sync (no_name,proof_using_ast last,`Doesn'tGuaranteeOpacity)
    | `Fork((_,hd',GuaranteesOpacity,ids), _) when has_proof_using last ->
        let name = name ids in
        let time = get_hint_bp_time name in
        assert (VCS.Branch.equal hd hd' || VCS.Branch.equal hd VCS.edit_branch);
        if delegate_policy_check time
        then `ASync (parent last,proof_using_ast last,accn,name)
        else `Sync (name,proof_using_ast last,`Policy)
    | `Fork((_, hd', GuaranteesOpacity, ids), _) when
       has_proof_no_using last && not (State.is_cached (parent last)) &&
       !Flags.compilation_mode = Flags.BuildVi ->
        (try
          let name = name ids in
          let hint, time = get_hint_ctx loc, get_hint_bp_time name in
          assert (VCS.Branch.equal hd hd'||VCS.Branch.equal hd VCS.edit_branch);
          let t, v = proof_no_using last in
          v.expr <- VernacProof(t, Some hint);
          if delegate_policy_check time
          then `ASync (parent last,proof_using_ast last,accn,name)
          else `Sync (name,proof_using_ast last,`Policy)
        with Not_found -> `Sync (no_name,None,`NoHint))
    | `Fork((_, hd', GuaranteesOpacity, ids), _) ->
        assert (VCS.Branch.equal hd hd' || VCS.Branch.equal hd VCS.edit_branch);
        let name = name ids in
        let time = get_hint_bp_time name in
        if delegate_policy_check time
        then `MaybeASync (parent last, None, accn, name)
        else `Sync (name,None,`Policy)
    | `Sideff _ -> `Sync (no_name,None,`NestedProof)
    | _ -> `Sync (no_name,None,`Unknown) in
 match cur, (VCS.visit id).step, brkind with
 |( parent, { expr = VernacExactProof _ }), `Fork _, _ ->
     `Sync (no_name,None,`Immediate)
 | _, _, { VCS.kind = `Edit _ }  -> collect (Some cur) [] id
 | _ ->
     if is_defined cur then `Sync (no_name,None,`Transparent)
     else if keep == VtDrop then `Sync (no_name,None,`Aborted)
     else
       let rc = collect (Some cur) [] id in
       if keep == VtKeep &&
          (not(State.is_cached id) || !Flags.async_proofs_always_delegate)
       then rc
       else (* we already have the proof, no gain in delaying *)
         match rc with
         | `Sync(name,pua,_) -> `Sync (name,pua,`AlreadyEvaluated)
         | `MaybeASync(_,pua,_,name) -> `Sync (name,pua,`AlreadyEvaluated)
         | `ASync(_,pua,_,name) -> `Sync (name,pua,`AlreadyEvaluated)

let string_of_reason = function
  | `Transparent -> "Transparent"
  | `AlreadyEvaluated -> "AlreadyEvaluated"
  | `Policy -> "Policy"
  | `NestedProof -> "NestedProof"
  | `Immediate -> "Immediate"
  | `Alias -> "Alias"
  | `NoHint -> "NoHint"
  | `Doesn'tGuaranteeOpacity -> "Doesn'tGuaranteeOpacity"
  | `Aborted -> "Aborted"
  | _ -> "Unknown Reason"

let wall_clock_last_fork = ref 0.0

let known_state ?(redefine_qed=false) ~cache id =

  (* ugly functions to process nested lemmas, i.e. hard to reproduce
   * side effects *)
  let cherry_pick_non_pstate () =
    Summary.freeze_summary ~marshallable:`No ~complement:true pstate,
    Lib.freeze ~marshallable:`No in
  let inject_non_pstate (s,l) = Summary.unfreeze_summary s; Lib.unfreeze l in

  let rec pure_cherry_pick_non_pstate id = Future.purify (fun id ->
    prerr_endline ("cherry-pick non pstate " ^ Stateid.to_string id);
    reach id;
    cherry_pick_non_pstate ()) id

  (* traverses the dag backward from nodes being already calculated *)
  and reach ?(redefine_qed=false) ?(cache=cache) id =
    prerr_endline ("reaching: " ^ Stateid.to_string id);
    if not redefine_qed && State.is_cached ~cache id then begin
      State.install_cached id;
      feedback ~state_id:id Feedback.Processed;
      prerr_endline ("reached (cache)")
    end else
    let step, cache_step, feedback_processed =
      let view = VCS.visit id in
      match view.step with
      | `Alias id -> (fun () ->
            reach view.next; reach id
          ), cache, true
      | `Cmd { cast = x; cqueue = `TacQueue cancel } -> (fun () ->
            reach ~cache:`Shallow view.next;
            Partac.vernac_interp
              cancel !Flags.async_proofs_n_tacworkers view.next id x
          ), cache, true
      | `Cmd { cast = x; cqueue = `QueryQueue cancel }
        when Flags.async_proofs_is_master () -> (fun () ->
            reach ~cache:`Shallow view.next;
            Query.vernac_interp cancel view.next id x
          ), cache, false
      | `Cmd { cast = x } -> (fun () ->
            reach view.next; vernac_interp id x
          ), cache, true
      | `Fork ((x,_,_,_), None) -> (fun () ->
            reach view.next; vernac_interp id x;
            wall_clock_last_fork := Unix.gettimeofday ()
          ), `Yes, true
      | `Fork ((x,_,_,_), Some prev) -> (fun () ->
            reach ~cache:`Shallow prev;
            reach view.next;
            (try vernac_interp id x;
            with e when Errors.noncritical e ->
              let e = Errors.push e in
              raise (Stateid.add e ~valid:prev id));
            wall_clock_last_fork := Unix.gettimeofday ()
          ), `Yes, true
      | `Qed ({ qast = x; keep; brinfo; brname } as qed, eop) ->
          let rec aux = function
          | `ASync (start, pua, nodes, name) -> (fun () ->
                assert(keep == VtKeep);
                prerr_endline ("Asynchronous " ^ Stateid.to_string id);
                VCS.create_cluster nodes ~tip:id;
                begin match brinfo, qed.fproof with
                | { VCS.kind = `Edit _ }, None -> assert false
                | { VCS.kind = `Edit _ }, Some (ofp, cancel) ->
                    assert(redefine_qed = true);
                    VCS.create_cluster nodes ~tip:id;
                    let fp, cancel = Slaves.build_proof
                      ~loc:x.loc ~exn_info:(id,eop) ~start ~stop:eop ~name in
                    Future.replace ofp fp;
                    qed.fproof <- Some (fp, cancel)
                | { VCS.kind = `Proof _ }, Some _ -> assert false
                | { VCS.kind = `Proof _ }, None ->
                    reach ~cache:`Shallow start;
                    let fp, cancel = Slaves.build_proof
                      ~loc:x.loc ~exn_info:(id,eop) ~start ~stop:eop ~name in
                    qed.fproof <- Some (fp, cancel);
                    let proof =
                      Proof_global.close_future_proof ~feedback_id:id fp in
                    reach view.next;
                    vernac_interp id ~proof x;
                    feedback ~state_id:id Feedback.Incomplete
                | { VCS.kind = `Master }, _ -> assert false
                end;
                Proof_global.discard_all ()
              ), (if redefine_qed then `No else `Yes), true
          | `Sync (name, _, `Immediate) -> (fun () -> 
                assert (Stateid.equal view.next eop);
                reach eop; vernac_interp id x; Proof_global.discard_all ()
              ), `Yes, true
          | `Sync (name, pua, reason) -> (fun () ->
                prerr_endline ("Synchronous " ^ Stateid.to_string id ^ " " ^
                  string_of_reason reason);
                reach eop;
                let wall_clock = Unix.gettimeofday () in
                record_pb_time name x.loc (wall_clock -. !wall_clock_last_fork);
                let proof =
                  if keep != VtKeep then None
                  else Some(Proof_global.close_proof
                              (State.exn_on id ~valid:eop)) in
                if proof = None then prerr_endline "NONE!!!!!";
                reach view.next;
                if keep == VtKeepAsAxiom then
                  Option.iter (vernac_interp id) pua;
                let wall_clock2 = Unix.gettimeofday () in
                vernac_interp id ?proof x;
                let wall_clock3 = Unix.gettimeofday () in
                Aux_file.record_in_aux_at x.loc "proof_check_time"
                  (Printf.sprintf "%.3f" (wall_clock3 -. wall_clock2));
                Proof_global.discard_all ()
              ), `Yes, true
          | `MaybeASync (start, pua, nodes, name) -> (fun () ->
                prerr_endline ("MaybeAsynchronous " ^ Stateid.to_string id);
                reach ~cache:`Shallow start;
                (* no sections *)
                if List.is_empty (Environ.named_context (Global.env ()))
                then pi1 (aux (`ASync (start, pua, nodes, name))) ()
                else pi1 (aux (`Sync (name, pua, `Unknown))) ()
              ), (if redefine_qed then `No else `Yes), true
          in
          aux (collect_proof keep (view.next, x) brname brinfo eop)
      | `Sideff (`Ast (x,_)) -> (fun () ->
            reach view.next; vernac_interp id x;
          ), cache, true
      | `Sideff (`Id origin) -> (fun () ->
            reach view.next;
            inject_non_pstate (pure_cherry_pick_non_pstate origin);
          ), cache, true
    in
    let cache_step =
      if !Flags.async_proofs_cache = Some Flags.Force then `Yes
      else cache_step in
    if Flags.async_proofs_is_master () then
      Pp.feedback ~state_id:id Feedback.ProcessingInMaster;
    State.define
      ~cache:cache_step ~redefine:redefine_qed ~feedback_processed step id;
    if !Flags.feedback_goals then print_goals_of_state id;
    prerr_endline ("reached: "^ Stateid.to_string id) in
  reach ~redefine_qed id

end (* }}} *)

(********************************* STM API ************************************)
(******************************************************************************)

let init () =
  VCS.init Stateid.initial;
  set_undo_classifier Backtrack.undo_vernac_classifier;
  State.define ~cache:`Yes (fun () -> ()) Stateid.initial;
  Backtrack.record ();
  if Flags.async_proofs_is_master () then begin
    prerr_endline "Initialising workers";
    Slaves.init ();
    Query.init ();
    let opts = match !Flags.async_proofs_private_flags with
      | None -> []
      | Some s -> Str.split_delim (Str.regexp ",") s in
    if String.List.mem "fallback-to-lazy-if-marshal-error=no" opts then
      fallback_to_lazy_if_marshal_error := false;
    if String.List.mem "fallback-to-lazy-if-slave-dies=no" opts then
      fallback_to_lazy_if_slave_dies := false;
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
    let e = Errors.push e in
    VCS.print ();
    VCS.restore vcs;
    raise e

let finish ?(print_goals=false) () =
  observe (VCS.get_branch_pos (VCS.current_branch ()));
  if print_goals then Pp.msg_notice (pr_open_cur_subgoals ());
  VCS.print ()

let wait () =
  Slaves.wait_all_done ();
  VCS.print ()

let join () =
  finish ();
  wait ();
  prerr_endline "Joining the environment";
  Global.join_safe_environment ();
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
    Pp.pperr_flush ();
    VCS.restore vcs;
    rc
  with e when Errors.noncritical e -> VCS.restore vcs; false
let info_tasks (tasks,_) = Slaves.info_tasks tasks
let finish_tasks name u d p (t,rcbackup as tasks) =
  RemoteCounter.restore rcbackup;
  let finish_task u (_,_,i) =
    let vcs = VCS.backup () in
    let u = Future.purify (Slaves.finish_task name u d p t) i in
    Pp.pperr_flush ();
    VCS.restore vcs;
    u in
  try
    let u, a, _ = List.fold_left finish_task u (info_tasks tasks) in
    (u,a,true), p
  with e ->
    let e = Errors.push e in
    Pp.pperrnl Pp.(str"File " ++ str name ++ str ":" ++ spc () ++ print e);
    exit 1

let merge_proof_branch ?id qast keep brname =
  let brinfo = VCS.get_branch brname in
  let qed fproof = { qast; keep; brname; brinfo; fproof } in
  match brinfo with
  | { VCS.kind = `Proof _ } ->
      VCS.checkout VCS.Branch.master;
      let id = VCS.new_node ?id () in
      VCS.merge id ~ours:(Qed (qed None)) brname;
      VCS.delete_branch brname;
      if keep <> VtDrop then VCS.propagate_sideff None;
      `Ok
  | { VCS.kind = `Edit (mode, qed_id, master_id) } ->
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
       raise (State.exn_on Stateid.dummy Proof_global.NoCurrentProof)

(* When tty is true, this code also does some of the job of the user interface:
   jump back to a state that is valid *)
let handle_failure e vcs tty =
  if e = Errors.Drop then raise e else
  match Stateid.get e with
  | None ->
      VCS.restore vcs;
      VCS.print ();
      if tty && interactive () = `Yes then begin
        (* Hopefully the 1 to last state is valid *)
        Backtrack.back_safe (); 
        VCS.checkout_shallowest_proof_branch ();
      end;
      VCS.print ();
      anomaly(str"error with no safe_id attached:" ++ spc() ++
        Errors.print_no_report e)
  | Some (safe_id, id) ->
      prerr_endline ("Failed at state " ^ Stateid.to_string id);
      VCS.restore vcs;
      if tty && interactive () = `Yes then begin
        (* We stay on a valid state *)
        Backtrack.backto safe_id;
        VCS.checkout_shallowest_proof_branch ();
        Reach.known_state ~cache:(interactive ()) safe_id;
      end;
      VCS.print ();
      raise e

let snapshot_vi ldir long_f_dot_v =
  finish ();
  if List.length (VCS.branches ()) > 1 then
    Errors.errorlabstrm "stm" (str"Cannot dump a vi with open proofs");
  Library.save_library_to ~todo:(dump_snapshot ()) ldir long_f_dot_v
    (Global.opaque_tables ())

let reset_task_queue = Slaves.reset_task_queue

(* Document building *)
let process_transaction ?(newtip=Stateid.fresh ()) ~tty verbose c (loc, expr) =
  let warn_if_pos a b =
    if b then msg_warning(pr_ast a ++ str" should not be part of a script") in
  let v, x = expr, { verbose = verbose; loc; expr } in
  prerr_endline ("{{{ processing: "^ string_of_ppcmds (pr_ast x));
  let vcs = VCS.backup () in
  try
    let head = VCS.current_branch () in
    VCS.checkout head;
    let rc = begin
      prerr_endline ("  classified as: " ^ string_of_vernac_classification c);
      match c with
      (* PG stuff *)    
      | VtStm(VtPG,false), VtNow -> vernac_interp Stateid.dummy x; `Ok
      | VtStm(VtPG,_), _ -> anomaly(str "PG command in script or VtLater")
      (* Joining various parts of the document *)
      | VtStm (VtJoinDocument, b), VtNow -> warn_if_pos x b; join (); `Ok
      | VtStm (VtFinish, b),       VtNow -> warn_if_pos x b; finish (); `Ok
      | VtStm (VtWait, b),     VtNow -> warn_if_pos x b; finish (); wait (); `Ok
      | VtStm (VtPrintDag, b), VtNow ->
          warn_if_pos x b; VCS.print ~now:true (); `Ok
      | VtStm (VtObserve id, b),   VtNow -> warn_if_pos x b; observe id; `Ok
      | VtStm ((VtObserve _ | VtFinish | VtJoinDocument
                |VtPrintDag |VtWait),_), VtLater ->
          anomaly(str"classifier: join actions cannot be classified as VtLater")
      
      (* Back *)
      | VtStm (VtBack oid, true), w ->
          let id = VCS.new_node ~id:newtip () in
          let { mine; others } = Backtrack.branches_of oid in
          List.iter (fun branch ->
            if not (List.mem_assoc branch (mine::others)) then
              ignore(merge_proof_branch x VtDrop branch))
            (VCS.branches ());
          VCS.checkout_shallowest_proof_branch ();
          let head = VCS.current_branch () in
          List.iter (fun b ->
            if not(VCS.Branch.equal b head) then begin
              VCS.checkout b;
              VCS.commit (VCS.new_node ()) (Alias oid);
            end)
            (VCS.branches ());
          VCS.checkout_shallowest_proof_branch ();
          VCS.commit id (Alias oid);
          Backtrack.record (); if w == VtNow then finish (); `Ok
      | VtStm (VtBack id, false), VtNow ->
          prerr_endline ("undo to state " ^ Stateid.to_string id);
          Backtrack.backto id;
          VCS.checkout_shallowest_proof_branch ();
          Reach.known_state ~cache:(interactive ()) id; `Ok
      | VtStm (VtBack id, false), VtLater ->
          anomaly(str"classifier: VtBack + VtLater must imply part_of_script")

      (* Query *)
      | VtQuery (false,(report_id,route)), VtNow when tty = true ->
          finish ();
          (try Future.purify (vernac_interp report_id ~route)
                  { verbose = true; loc; expr }
           with e when Errors.noncritical e ->
             let e = Errors.push e in
             raise(State.exn_on report_id e)); `Ok
      | VtQuery (false,(report_id,route)), VtNow ->
          (try vernac_interp report_id ~route x
           with e when Errors.noncritical e ->
             let e = Errors.push e in
             raise(State.exn_on report_id e)); `Ok
      | VtQuery (true,(report_id,_)), w ->
          assert(Stateid.equal report_id Stateid.dummy);
          let id = VCS.new_node ~id:newtip () in
          let queue =
            if !Flags.async_queries_always_delegate then `QueryQueue (ref false)
            else `MainQueue in
          VCS.commit id (Cmd { cast = x; cids = []; cqueue = queue });
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
          VCS.checkout VCS.Branch.master;
          VCS.commit id (Cmd {cast = x; cids=[]; cqueue = `MainQueue});
          VCS.propagate_sideff (Some x);
          List.iter
            (fun bn -> match VCS.get_branch bn with
            | { VCS.root; kind = `Master; pos } -> ()
            | { VCS.root; kind = `Proof(_,d); pos } ->
                VCS.delete_branch bn;
                VCS.branch ~root ~pos bn (`Proof(mode,d))
            | { VCS.root; kind = `Edit(_,f,q); pos } ->
                VCS.delete_branch bn;
                VCS.branch ~root ~pos bn (`Edit(mode,f,q)))
            (VCS.branches ());
          VCS.checkout_shallowest_proof_branch ();
          Backtrack.record ();
          finish ();
          `Ok
      | VtProofStep paral, w ->
          let id = VCS.new_node ~id:newtip () in
          let queue = if paral then `TacQueue (ref false) else `MainQueue in
          VCS.commit id (Cmd {cast = x; cids = []; cqueue = queue });
          Backtrack.record (); if w == VtNow then finish (); `Ok
      | VtQed keep, w ->
          let rc = merge_proof_branch ~id:newtip x keep head in
          VCS.checkout_shallowest_proof_branch ();
          Backtrack.record (); if w == VtNow then finish ();
          rc
          
      (* Side effect on all branches *)
      | VtUnknown, _ when expr = VernacToplevelControl Drop ->
          vernac_interp (VCS.get_branch_pos head) x; `Ok

      | VtSideff l, w ->
          let id = VCS.new_node ~id:newtip () in
          VCS.checkout VCS.Branch.master;
          VCS.commit id (Cmd { cast = x; cids = l; cqueue = `MainQueue});
          VCS.propagate_sideff (Some x);
          VCS.checkout_shallowest_proof_branch ();
          Backtrack.record (); if w == VtNow then finish (); `Ok

      (* Unknown: we execute it, check for open goals and propagate sideeff *)
      | VtUnknown, VtNow ->
          let id = VCS.new_node ~id:newtip () in
          let head_id = VCS.get_branch_pos head in
          Reach.known_state ~cache:`Yes head_id; (* ensure it is ok *)
          let step () =
            VCS.checkout VCS.Branch.master;
            let mid = VCS.get_branch_pos VCS.Branch.master in
            Reach.known_state ~cache:(interactive ()) mid;
            vernac_interp id x;
            (* Vernac x may or may not start a proof *)
            if VCS.Branch.equal head VCS.Branch.master &&
               Proof_global.there_are_pending_proofs ()
            then begin
              let bname = VCS.mk_branch_name x in
              VCS.commit id (Fork (x,bname,Doesn'tGuaranteeOpacity,[]));
              VCS.branch bname (`Proof ("Classic", VCS.proof_nesting () + 1));
              Proof_global.activate_proof_mode "Classic";
            end else begin
              VCS.commit id (Cmd { cast = x; cids = []; cqueue = `MainQueue});
              VCS.propagate_sideff (Some x);
              VCS.checkout_shallowest_proof_branch ();
            end in
          State.define ~safe_id:head_id ~cache:`Yes step id;
          Backtrack.record (); `Ok

      | VtUnknown, VtLater ->
          anomaly(str"classifier: VtUnknown must imply VtNow")
    end in
    (* Proof General *)
    begin match v with 
      | VernacStm (PGLast _) ->
        if not (VCS.Branch.equal head VCS.Branch.master) then
          vernac_interp Stateid.dummy
            { verbose = true; loc = Loc.ghost;
              expr = VernacShow (ShowGoal OpenSubgoals) }
      | _ -> ()
    end;
    prerr_endline "processed }}}";
    VCS.print ();
    rc
  with e ->
    let e = Errors.push e in
    handle_failure e vcs tty

let print_ast id =
  try
    match VCS.visit id with
    | { step = `Cmd { cast = { loc; expr } } }
    | { step = `Fork (({ loc; expr }, _, _, _), _) } 
    | { step = `Qed ({ qast = { loc; expr } }, _) } ->
        let xml = 
          try Texmacspp.tmpp expr loc
          with e -> Xml_datatype.PCData ("ERROR " ^ Printexc.to_string e) in
        xml;
    | _ -> Xml_datatype.PCData "ERROR"
  with _ -> Xml_datatype.PCData "ERROR"

let stop_worker n = Slaves.cancel_worker n

let query ~at ?(report_with=(Stateid.dummy,Feedback.default_route)) s =
  Future.purify (fun s ->
    if Stateid.equal at Stateid.dummy then finish ()
    else Reach.known_state ~cache:`Yes at;
    let newtip, route = report_with in
    let _, ast as loc_ast = vernac_parse ~newtip ~route 0 s in
    let clas = classify_vernac ast in
    match clas with
    | VtStm (w,_), _ ->
       ignore(process_transaction
         ~tty:false true (VtStm (w,false), VtNow) loc_ast)
    | _ ->
       ignore(process_transaction
         ~tty:false true (VtQuery (false,report_with), VtNow) loc_ast))
  s

let add ~ontop ?newtip ?(check=ignore) verb eid s =
  let cur_tip = VCS.cur_tip () in
  if Stateid.equal ontop cur_tip then begin
    let _, ast as loc_ast = vernac_parse ?newtip eid s in
    check(loc_ast);
    let clas = classify_vernac ast in
    match process_transaction ?newtip ~tty:false verb clas loc_ast with
    | `Ok -> VCS.cur_tip (), `NewTip
    | `Unfocus qed_id -> qed_id, `Unfocus (VCS.cur_tip ())
  end else begin
    (* For now, arbitrary edits should be announced with edit_at *)
    anomaly(str"Not yet implemented, the GUI should not try this")
  end

let set_perspective id_list = Slaves.set_perspective id_list

type focus = {
  start : Stateid.t;
  stop : Stateid.t;
  tip : Stateid.t
}

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
  let is_ancestor_of_cur_branch id =
    Vcs_.NodeSet.mem id
      (VCS.reachable (VCS.get_branch_pos (VCS.current_branch ()))) in
  let has_failed qed_id =
    match VCS.visit qed_id with
    | { step = `Qed ({ fproof = Some (fp,_) }, _) } -> Future.is_exn fp
    | _ -> false in
  let rec master_for_br root tip =
      if Stateid.equal tip Stateid.initial then tip else
      match VCS.visit tip with
      | { next } when next = root -> root
      | { step = `Fork _ } -> tip
      | { step = `Sideff (`Ast(_,id)|`Id id) } -> id
      | { next } -> master_for_br root next in
  let reopen_branch at_id mode qed_id tip =
    VCS.delete_cluster_of id;
    let master_id =
      match VCS.visit qed_id with
      | { step = `Qed _; next = master_id } -> master_id
      | _ -> anomaly (str "Cluster not ending with Qed") in
    VCS.branch ~root:master_id ~pos:id
      VCS.edit_branch (`Edit (mode, qed_id, master_id));
    Reach.known_state ~cache:(interactive ()) id;
    VCS.checkout_shallowest_proof_branch ();
    `Focus { stop = qed_id; start = master_id; tip } in
  let backto id =
    List.iter VCS.delete_branch (VCS.branches ());
    let ancestors = VCS.reachable id in
    let { mine = brname, brinfo; others } = Backtrack.branches_of id in
    List.iter (fun (name,{ VCS.kind = k; root; pos }) ->
      if not(VCS.Branch.equal name VCS.Branch.master) &&
         Vcs_.NodeSet.mem root ancestors then
        VCS.branch ~root ~pos name k)
      others;
    VCS.reset_branch VCS.Branch.master (master_for_br brinfo.VCS.root id);
    VCS.branch ~root:brinfo.VCS.root ~pos:brinfo.VCS.pos brname brinfo.VCS.kind;
    VCS.delete_cluster_of id;
    VCS.gc ();
    Reach.known_state ~cache:(interactive ()) id;
    VCS.checkout_shallowest_proof_branch ();
    `NewTip in
  try
    let rc =
      let focused = List.exists ((=) VCS.edit_branch) (VCS.branches ()) in
      let branch_info =
        match snd (VCS.get_info id).vcs_backup with
        | Some{ mine = _, { VCS.kind = (`Proof(m,_)|`Edit(m,_,_)) }} -> Some m
        | _ -> None in
      match focused, VCS.cluster_of id, branch_info with
      | _, Some _, None -> assert false
      | false, Some qed_id, Some mode ->
          let tip = VCS.cur_tip () in
          if has_failed qed_id && not !Flags.async_proofs_never_reopen_branch
          then reopen_branch id mode qed_id tip
          else backto id
      | true, Some qed_id, Some mode ->
          if on_cur_branch id then begin
            assert false
          end else if is_ancestor_of_cur_branch id then begin
            backto id
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
            backto id
          end else begin
            anomaly(str"Cannot leave an `Edit branch open")
          end
      | false, None, _ -> backto id
    in
    VCS.print ();
    rc
  with e ->
    let e = Errors.push e in
    match Stateid.get e with
    | None ->
        VCS.print ();
        anomaly (str ("edit_at "^Stateid.to_string id^": ") ++
          Errors.print_no_report e)
    | Some (_, id) ->
        prerr_endline ("Failed at state " ^ Stateid.to_string id);
        VCS.restore vcs;
        VCS.print ();
        raise e

(*********************** TTY API (PG, coqtop, coqc) ***************************)
(******************************************************************************)

let interp verb (_,e as lexpr) =
  let clas = classify_vernac e in
  let rc = process_transaction ~tty:true verb clas lexpr in
  if rc <> `Ok then anomaly(str"tty loop can't be mixed with the STM protocol");
  if interactive () = `Yes ||
     (!Flags.async_proofs_mode = Flags.APoff &&
      !Flags.compilation_mode = Flags.BuildVo) then
    let vcs = VCS.backup () in
    let print_goals =
      (if !Flags.print_emacs then Flags.is_verbose () else !Flags.coqtop_ui) &&
      match clas with
      | VtQuery _, _ -> false
      | _ -> true in
    try finish ~print_goals ()
    with e ->
      let e = Errors.push e in
      handle_failure e vcs true

let finish () = finish ()

let get_current_state () = VCS.cur_tip ()

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
  List.map unmangle (List.map_filter proofname (VCS.branches ()))

let get_current_proof_name () =
  Option.map unmangle (proofname (VCS.current_branch ()))

let get_script prf =
  let branch, test =
    match prf with
    | None -> VCS.Branch.master, fun _ -> true
    | Some name -> VCS.current_branch (),  List.mem name in
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
    | `Cmd {cast = x} -> find ((x.expr, (VCS.get_info id).n_goals)::acc) view.next 
    | `Alias id -> find acc id
    | `Fork _ -> find acc view.next
    in
  find [] (VCS.get_branch_pos branch)

(* indentation code for Show Script, initially contributed
   by D. de Rauglaudre *)

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
  let pp =
    (if nl then fnl () else mt ()) ++
    (hov (ind+1) (str (String.make ind ' ') ++ Ppvernac.pr_vernac cmd))
  in
  (new_ngl, new_nl, new_beginend, pp :: ppl)

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
    msg_notice (v 0 (Pp.prlist_with_sep Pp.fnl (fun x -> x) indented_cmds))
  with Vcs_aux.Expired -> ()

(* vim:set foldmethod=marker: *)
