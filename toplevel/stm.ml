(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2013     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

let prerr_endline s = if !Flags.debug then prerr_endline s else ()

open Stateid
open Vernacexpr
open Errors
open Pp
open Names
open Util
open Ppvernac
open Vernac_classifier

(* During interactive use we cache more states so that Undoing is fast *)
let interactive () =
  !Flags.ide_slave || !Flags.print_emacs || not !Flags.batch_mode

(* Wrap interp to set the feedback id *)
let interp ?proof id (verbosely, loc, expr) =
  let internal_command = function
    | VernacResetName _ | VernacResetInitial | VernacBack _
    | VernacBackTo _ | VernacRestart | VernacUndo _ | VernacUndoTo _
    | VernacBacktrack _ | VernacAbortAll | VernacAbort _ -> true | _ -> false in
  if internal_command expr then ()
  else begin
    Pp.set_id_for_feedback (Interface.State id);
    try Vernacentries.interp ~verbosely ?proof (loc, expr)
    with e -> raise (Errors.push (Cerrors.process_vernac_interp_error e))
  end

type ast = bool * Loc.t * vernac_expr
let pr_ast (_, _, v) = pr_vernac v

module Vcs_ = Vcs.Make(StateidOrderedType)

type branch_type = [ `Master | `Proof of string * int ]
type cmd_t = ast
type fork_t = ast * Vcs_.branch_name * Names.Id.t list
type qed_t =
  ast * vernac_qed_type * (Vcs_.branch_name * branch_type Vcs_.branch_info)
type seff_t = ast option
type alias_t = state_id
type transaction =
  | Cmd    of cmd_t
  | Fork   of fork_t
  | Qed    of qed_t
  | Sideff of seff_t
  | Alias  of alias_t
  | Noop
type step =
  [ `Cmd    of cmd_t
  | `Fork   of fork_t
  | `Qed    of qed_t * state_id
  | `Sideff of [ `Ast of ast * state_id | `Id of state_id ]
  | `Alias  of alias_t ]
type visit = { step : step; next : state_id }

type state = States.state * Proof_global.state
type state_info = { (* Make private *)
  mutable n_reached : int;
  mutable n_goals : int;
  mutable state : state option;
}
let default_info () = { n_reached = 0; n_goals = 0; state = None }

(* Functions that work on a Vcs with a specific branch type *)
module Vcs_aux : sig

  val proof_nesting : (branch_type, 't,'i) Vcs_.t -> int
  val find_proof_at_depth :
    (branch_type, 't, 'i) Vcs_.t -> int ->
      Vcs_.branch_name * branch_type Vcs_.branch_info

end = struct (* {{{ *)

  let proof_nesting vcs =
    List.fold_left max 0
      (List.map_filter
        (function { Vcs_.kind = `Proof (_,n) } -> Some n | _ -> None)
        (List.map (Vcs_.get_branch vcs) (Vcs_.branches vcs)))

  let find_proof_at_depth vcs pl =
    try List.find (function
          | _, { Vcs_.kind = `Proof(m, n) } -> n = pl
          | _ -> false)
        (List.map (fun h -> h, Vcs_.get_branch vcs h) (Vcs_.branches vcs))
    with Not_found -> failwith "find_proof_at_depth"

end (* }}} *)

(* Imperative wrap around VCS to obtain _the_ VCS *)
module VCS : sig

  type id = state_id
  type branch_name = Vcs_.branch_name
  type 'branch_type branch_info = 'branch_type Vcs_.branch_info = {
    kind : [> `Master] as 'branch_type;
    root : id;
    pos  : id;
  }

  type vcs = (branch_type, transaction, state_info) Vcs_.t

  val init : id -> unit

  val string_of_branch_name : branch_name -> string

  val current_branch : unit -> branch_name
  val checkout : branch_name -> unit
  val master : branch_name
  val branches : unit -> branch_name list
  val get_branch : branch_name -> branch_type branch_info
  val get_branch_pos : branch_name -> id
  val new_node : unit -> id
  val merge : id -> ours:transaction -> ?into:branch_name -> branch_name -> unit
  val delete_branch : branch_name -> unit
  val commit : id -> transaction -> unit
  val mk_branch_name : ast -> branch_name
  val branch : branch_name -> branch_type -> unit
  
  val get_info : id -> state_info
  val reached : id -> bool -> unit
  val goals : id -> int -> unit
  val set_state : id -> state -> unit
  val forget_state : id -> unit
  
  val create_cluster : id list -> unit

  val proof_nesting : unit -> int
  val checkout_shallowest_proof_branch : unit -> unit
  val propagate_sideff : ast option -> unit

  val visit : id -> visit

  val print : unit -> unit

  val backup : unit -> vcs
  val restore : vcs -> unit

end = struct (* {{{ *)

  include Vcs_

  module StateidSet = Set.Make(StateidOrderedType)
  open Printf

  let print_dag vcs () = (* {{{ *)
    let fname = "stm" in
    let string_of_transaction = function
      | Cmd t | Fork (t, _, _) ->
          (try string_of_ppcmds (pr_ast t) with _ -> "ERR")
      | Sideff (Some t) ->
          sprintf "Sideff(%s)"
            (try string_of_ppcmds (pr_ast t) with _ -> "ERR")
      | Sideff None -> "EnvChange"
      | Noop -> " "
      | Alias id -> sprintf "Alias(%s)" (string_of_state_id id)
      | Qed (a,_,_) -> string_of_ppcmds (pr_ast a) in
    let is_green id = 
      match get_info vcs id with
      | Some { state = Some _ } -> true
      | _ -> false in
    let is_red id =
      match get_info vcs id with
      | Some s -> s.n_reached = ~-1
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
    let node id = "s" ^ string_of_state_id id in
    let edge tr =
      sprintf "<<FONT POINT-SIZE=\"12\" FACE=\"sans\">%s</FONT>>"
        (quote (string_of_transaction tr)) in
    let ids = ref StateidSet.empty in
    let clus = Hashtbl.create 13 in
    let node_info id =
      match get_info vcs id with
      | None -> ""
      | Some info ->
          sprintf "<<FONT POINT-SIZE=\"12\">%s</FONT>" (string_of_state_id id) ^
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
       fprintf oc "%s -> %s [label=%s,labelfloat=%b];\n"
           (node from) (node dest) (edge trans) (c1 && c2)) l
    );
    StateidSet.iter (nodefmt oc) !ids;
    Hashtbl.iter (fun c nodes ->
       fprintf oc "subgraph cluster_%s {\n" (Dag.string_of_cluster_id c);
       List.iter (nodefmt oc) nodes;
       fprintf oc "color=blue; }\n"
    ) clus;
    List.iteri (fun i (b,id) ->
      let shape = if head = b then "box3d" else "box" in
      fprintf oc "b%d -> %s;\n" i (node id);
      fprintf oc "b%d [shape=%s,label=\"%s\"];\n" i shape
        (string_of_branch_name b);
    ) heads;
    output_string oc "}\n";
    close_out oc;
    ignore(Sys.command
      ("dot -Tpdf -Gcharset=latin1 " ^ fname_dot ^ " -o" ^ fname_ps))
  (* }}} *)
  
  type vcs = (branch_type, transaction, state_info) t
  let vcs : vcs ref = ref (empty dummy_state_id)

  let init id =
    vcs := empty id;
    vcs := set_info !vcs id (default_info ())

  let current_branch () = current_branch !vcs

  let checkout head = vcs := checkout !vcs head
  let master = master
  let branches () = branches !vcs
  let get_branch head = get_branch !vcs head
  let get_branch_pos head = (get_branch head).pos
  let new_node () =
    let id = Stateid.fresh_state_id () in
    vcs := set_info !vcs id (default_info ());
    id
  let merge id ~ours ?into branch =
    vcs := merge !vcs id ~ours ~theirs:Noop ?into branch
  let delete_branch branch = vcs := delete_branch !vcs branch
  let commit id t = vcs := commit !vcs id t
  let mk_branch_name (_, _, x) = mk_branch_name
    (match x with
    | VernacDefinition (_,(_,i),_) -> string_of_id i
    | VernacStartTheoremProof (_,[Some (_,i),_],_) -> string_of_id i
    | _ -> "branch")
  let branch name kind = vcs := branch !vcs name kind
  let get_info id =
    match get_info !vcs id with
    | Some x -> x
    | None -> assert false
  let set_state id s = (get_info id).state <- Some s
  let forget_state id = (get_info id).state <- None
  let reached id b =
    let info = get_info id in
    if b then info.n_reached <- info.n_reached + 1
    else info.n_reached <- -1
  let goals id n = (get_info id).n_goals <- n
  let create_cluster l = vcs := create_cluster !vcs l

  let proof_nesting () = Vcs_aux.proof_nesting !vcs

  let checkout_shallowest_proof_branch () =
    let pl = proof_nesting () in
    try
      let branch, mode = match Vcs_aux.find_proof_at_depth !vcs pl with
        | h, { Vcs_.kind = `Proof (m, _) } -> h, m | _ -> assert false in
      checkout branch;
      Proof_global.activate_proof_mode mode
    with Failure _ ->
      checkout master;
      Proof_global.disactivate_proof_mode "Classic" (* XXX *)

  (* copies the transaction on every open branch *)
  let propagate_sideff t =
    List.iter (fun b ->
      checkout b;
      let id = new_node () in
      merge id ~ours:(Sideff t) ~into:b master)
    (List.filter ((<>) master) (branches ()))
  
  let visit id =
    match Dag.from_node (dag !vcs) id with
    | [n, Cmd x] -> { step = `Cmd x; next = n }
    | [n, Alias x] -> { step = `Alias x; next = n }
    | [n, Fork x] -> { step = `Fork x; next = n }
    | [n, Qed x; p, Noop]
    | [p, Noop; n, Qed x] -> { step = `Qed (x,p); next = n }
    | [n, Sideff None; p, Noop]
    | [p, Noop; n, Sideff None]-> { step = `Sideff (`Id p); next = n }
    | [n, Sideff (Some x); p, Noop]
    | [p, Noop; n, Sideff (Some x)]-> { step = `Sideff (`Ast (x,p)); next = n }
    | _ -> anomaly (str "Malformed VCS, or visiting the root")

  module NB : sig

    val command : (unit -> unit) -> unit

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
      while !job = None do Condition.wait c m; done;
      match !job with
      | None -> assert false
      | Some x -> job := None; Mutex.unlock m; x

    let run_command () =
      while true do get_last_job () () done

    let command job =
      set_last_job job;
      if !worker = None then worker := Some (Thread.create run_command ())

  end

  let print () =
    if not !Flags.debug then () else NB.command (print_dag !vcs)

  let backup () = !vcs
  let restore v = vcs := v

end (* }}} *)

(* Fills in the nodes of the VCS *)
module State : sig

  (** The function is from unit, so it uses the current state to define
      a new one.  I.e. one may been to install the right state before
      defining a new one.

      Warning: an optimization requires that state modifying functions
      are always executed using this wrapper. *)
  val define : ?cache:bool -> (unit -> unit) -> state_id -> unit

  val install_cached : state_id -> unit
  val is_cached : state_id -> bool

  val exn_on : state_id -> ?valid:state_id -> exn -> exn

end = struct (* {{{ *)

  (* cur_id holds dummy_state_id in case the last attempt to define a state
   * failed, so the global state may contain garbage *)
  let cur_id = ref dummy_state_id

  (* helpers *)
  let freeze_global_state () =
    States.freeze ~marshallable:false, Proof_global.freeze ()
  let unfreeze_global_state (s,p) =
    States.unfreeze s; Proof_global.unfreeze p

  (* hack to make futures functional *)
  let in_t, out_t = Dyn.create "state4future"
  let () = Future.set_freeze
    (fun () -> in_t (freeze_global_state (), !cur_id))
    (fun t -> let s,i = out_t t in unfreeze_global_state s; cur_id := i)

  let is_cached id =
    id = !cur_id ||
    match VCS.get_info id with
    | { state = Some _ } -> true
    | _ -> false

  let install_cached id =
    if id = !cur_id then () else (* optimization *)
    let s =
      match VCS.get_info id with
      | { state = Some s } -> s
      | _ -> anomaly (str "unfreezing a non existing state") in
    unfreeze_global_state s; cur_id := id

  let freeze id = VCS.set_state id (freeze_global_state ())

  let exn_on id ?valid e =
    let loc = Option.default Loc.ghost (Loc.get_loc e) in
    let msg = string_of_ppcmds (print e) in
    Pp.feedback ~state_id:id (Interface.ErrorMsg (loc, msg));
    Stateid.add_state_id e ?valid id

  let define ?(cache=false) f id =
    if is_cached id then
      anomaly (str"defining state "++str(string_of_state_id id)++str" twice");
    try
      prerr_endline ("defining " ^
        string_of_state_id id ^ " (cache=" ^ string_of_bool cache ^ ")");
      f ();
      if cache then freeze id;
      cur_id := id;
      feedback ~state_id:id Interface.Processed;
      VCS.reached id true;
      if Proof_global.there_are_pending_proofs () then
        VCS.goals id (Proof_global.get_open_goals ());
    with e ->
      let e = Errors.push e in
      let good_id = !cur_id in
      cur_id := dummy_state_id;
      VCS.reached id false;
      match Stateid.get_state_id e with
      | Some _ -> raise e
      | None -> raise (exn_on id ~valid:good_id e)

end
(* }}} *)


(* Runs all transactions needed to reach a state *)
module Reach : sig

  val known_state : cache:bool -> state_id -> unit

end = struct (* {{{ *)

let pstate = ["meta counter"; "evar counter"; "program-tcc-table"]

let collect_proof cur hd id =
 let rec collect last accn id =
    let view = VCS.visit id in
    match last, view.step with
    | _, `Cmd x -> collect (Some (id,x)) (id::accn) view.next
    | _, `Alias _ -> collect None (id::accn) view.next
    | Some (parent, (_,_,VernacExactProof _)), `Fork _ ->
        `NotOptimizable `Immediate
    | Some (parent, (_,_,VernacProof(_,Some _) as v)), `Fork (_, hd', _) ->
        assert( hd = hd' );
        `Optimizable (parent, Some v, accn)
    | Some (parent, _), `Fork (_, hd', _) ->
        assert( hd = hd' );
        `MaybeOptimizable (parent, accn)
    | _, `Sideff se -> collect None (id::accn) view.next
    | _ -> `NotOptimizable `Unknown in
 if State.is_cached id then `NotOptimizable `Unknown
 else collect (Some cur) [] id

let known_state ~cache id =

  (* ugly functions to process nested lemmas, i.e. hard to reproduce
   * side effects *)
  let cherry_pick_non_pstate () =
    Summary.freeze_summary ~marshallable:false ~complement:true pstate,
    Lib.freeze ~marshallable:false in
  let inject_non_pstate (s,l) = Summary.unfreeze_summary s; Lib.unfreeze l in

  let rec pure_cherry_pick_non_pstate id = Future.purify (fun id ->
    prerr_endline ("cherry-pick non pstate " ^ string_of_state_id id);
    reach id;
    cherry_pick_non_pstate ()) id

  (* traverses the dag backward from nodes being already calculated *)
  and reach ?(cache=cache) id =
    prerr_endline ("reaching: " ^ string_of_state_id id);
    if State.is_cached id then begin
      State.install_cached id;
      feedback ~state_id:id Interface.Processed;
      prerr_endline ("reached (cache)")
    end else
    let step, cache_step =
      let view = VCS.visit id in
      match view.step with
      | `Alias id ->
           (fun () ->
              reach view.next; reach id; Vernacentries.try_print_subgoals ()),
           cache
      | `Cmd (x,_) -> (fun () -> reach view.next; interp id x), cache
      | `Fork (x,_,_) -> (fun () -> reach view.next; interp id x), true
      | `Qed ((x,keep,(hd,_)), eop) ->
           let rec aux = function
           | `Optimizable (start, proof_using_ast, nodes) ->
               (fun () ->
                 prerr_endline ("Optimizable " ^ string_of_state_id id);
                 VCS.create_cluster nodes;
                 begin match keep with
                 | KeepProof ->
                     let f = Future.create (fun () -> reach eop) in
                     reach start;
                     let proof =
                       Proof_global.close_future_proof
                         ~fix_exn:(State.exn_on id ~valid:eop) f in
                     reach view.next;
                     interp id ~proof x;
                 | DropProof ->
                     reach view.next;
                     Option.iter (interp start) proof_using_ast;
                     interp id x
                 end;
                 Proof_global.discard_all ())
           | `NotOptimizable `Immediate -> assert (view.next = eop);
               (fun () -> reach eop; interp id x; Proof_global.discard_all ())
           | `NotOptimizable `Unknown ->
               (fun () ->
                 prerr_endline ("NotOptimizable " ^ string_of_state_id id);
                 reach eop;
                 begin match keep with
                 | KeepProof ->
                     let proof = Proof_global.close_proof () in
                     reach view.next;
                     interp id ~proof x
                 | DropProof ->
                     reach view.next;
                     interp id x
                 end;
                 Proof_global.discard_all ())
           | `MaybeOptimizable (start, nodes) ->
               (fun () ->
                 prerr_endline ("MaybeOptimizable " ^ string_of_state_id id);
                 reach ~cache:true start;
                 (* no sections and no modules *)
                 if Environ.named_context (Global.env ()) = [] &&
                    Safe_typing.is_curmod_library (Global.safe_env ()) then
                   aux (`Optimizable (start, None, nodes)) ()
                 else
                   aux (`NotOptimizable `Unknown) ())
           in
             aux (collect_proof (view.next, x) hd eop), true
      | `Sideff (`Ast (x,_)) ->
           (fun () -> reach view.next; interp id x), cache
      | `Sideff (`Id origin) ->
           (fun () ->
              let s = pure_cherry_pick_non_pstate origin in
              reach view.next;
              inject_non_pstate s),
           cache
    in
    State.define ~cache:cache_step step id;
    prerr_endline ("reached: "^ string_of_state_id id) in
  reach id

end (* }}} *)

(* The backtrack module simulates the classic behavior of a linear document *)
module Backtrack : sig

  val record : unit -> unit
  val backto : state_id -> unit
  val cur : unit -> state_id

  (* we could navigate the dag, but this ways easy *)
  val branches_of : state_id -> VCS.branch_name list

  (* To be installed during initialization *)
  val undo_vernac_classifier : vernac_expr -> vernac_classification

end = struct (* {{{ *)

  module S  = Searchstack

  type hystory_elt = {
    id : state_id ;
    vcs : VCS.vcs;
    label : Names.Id.t list; (* To implement a limited form of reset *)
  }

  let history : hystory_elt S.t = S.create ()

  let cur () =
    if S.is_empty history then anomaly (str "Empty history");
    (S.top history).id

  let record () =
    let id = VCS.get_branch_pos (VCS.current_branch ()) in
    S.push {
      id = id;
      vcs = VCS.backup ();
      label =
        if id = initial_state_id || id = dummy_state_id then [] else 
        match VCS.visit id with
        | { step = `Fork (_,_,l) } -> l
        | { step = `Cmd (_,_, VernacFixpoint (_,l)) } -> 
              List.map (fun (((_,id),_,_,_,_),_) -> id) l
        | { step = `Cmd (_,_, VernacCoFixpoint (_,l)) } -> 
              List.map (fun (((_,id),_,_,_),_) -> id) l
        | { step = `Cmd (_,_, VernacAssumption (_,_,l)) } -> 
              List.flatten (List.map (fun (_,(lid,_)) -> List.map snd lid) l)
        | { step = `Cmd (_,_, VernacInductive (_,_,l)) } -> 
              List.map (fun (((_,(_,id)),_,_,_,_),_) -> id) l
        | { step = `Cmd (_,_, (VernacDefinition (_,(_,id),DefineBody _) |
                               VernacDeclareModuleType ((_,id),_,_,_) |
                               VernacDeclareModule (_,(_,id),_,_) |
                               VernacDefineModule (_,(_,id),_,_,_))) } -> [id]
        | _ -> [] }
    history

  let backto oid =
    assert(not (S.is_empty history));
    let rec pop_until_oid () =
      let id = (S.top history).id in
      if id = initial_state_id || id = oid then ()
      else begin ignore (S.pop history); pop_until_oid (); end in
    pop_until_oid ();
    let backup = S.top history in
    VCS.restore backup.vcs;
    if backup.id <> oid then anomaly (str "Backto an unknown state")

  let branches_of id =
    try
      let s = S.find (fun n s ->
        if s.id = id then `Stop s else `Cont ()) () history in
      Vcs_.branches s.vcs
    with Not_found -> assert false
 
  let undo_vernac_classifier = function
    | VernacResetInitial ->
        VtStm (VtBack initial_state_id, true), VtNow
    | VernacResetName (_,name) ->
        msg_warning
          (str"Reset not implemented for automatically generated constants");
        (try
          let s =
            S.find (fun b s ->
              if b then `Stop s else `Cont (List.mem name s.label))
            false history in
          VtStm (VtBack s.id, true), VtNow
        with Not_found ->
          VtStm (VtBack (S.top history).id, true), VtNow)
    | VernacBack n ->
        let s = S.find (fun n s ->
          if n = 0 then `Stop s else `Cont (n-1)) n history in
        VtStm (VtBack s.id, true), VtNow
    | VernacUndo n ->
        let s = S.find (fun n s ->
          if n = 0 then `Stop s else `Cont (n-1)) n history in
        VtStm (VtBack s.id, true), VtLater
    | VernacUndoTo _
    | VernacRestart as e ->
        let m = match e with VernacUndoTo m -> m | _ -> 0 in
        let vcs = (S.top history).vcs in
        let cb, _ =
          Vcs_aux.find_proof_at_depth vcs (Vcs_aux.proof_nesting vcs) in
        let n = S.find (fun n { vcs } ->
          if List.mem cb (Vcs_.branches vcs) then `Cont (n+1) else `Stop n)
          0 history in
        let s = S.find (fun n s ->
          if n = 0 then `Stop s else `Cont (n-1)) (n-m-1) history in
        VtStm (VtBack s.id, true), VtLater
    | VernacAbortAll ->
        let s = S.find (fun () s ->
          if List.length (Vcs_.branches s.vcs) = 1 then `Stop s else `Cont ())
          () history in
        VtStm (VtBack s.id, true), VtLater
    | VernacBacktrack (id,_,_)
    | VernacBackTo id ->
        VtStm (VtBack (Stateid.state_id_of_int id), true), VtNow
    | _ -> VtUnknown, VtNow

end (* }}} *)

let init () =
  VCS.init initial_state_id;
  declare_vernac_classifier "Stm" Backtrack.undo_vernac_classifier;
  State.define ~cache:true (fun () -> ()) initial_state_id;
  Backtrack.record ()

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

let finish () =
  observe (VCS.get_branch_pos (VCS.current_branch ()));
  VCS.print ()

let join_aborted_proofs () =
  let rec aux id =
    if id = initial_state_id then () else
    let view = VCS.visit id in
    match view.step with
    | `Qed ((_,DropProof,_),eop) -> observe eop; aux view.next
    | `Sideff _ | `Alias _ | `Cmd _ | `Fork _ | `Qed _ -> aux view.next
  in
    aux (VCS.get_branch_pos VCS.master)

let join () =
  finish ();
  VCS.print ();
  prerr_endline "Joining the environment";
  Global.join_safe_environment ();
  VCS.print ();
  prerr_endline "Joining the aborted proofs";
  join_aborted_proofs ();
  VCS.print ()

let merge_proof_branch x keep branch =
  if branch = VCS.master then
    raise(State.exn_on dummy_state_id Proof_global.NoCurrentProof);
  let info = VCS.get_branch branch in
  VCS.checkout VCS.master;
  let id = VCS.new_node () in
  VCS.merge id ~ours:(Qed (x,keep,(branch, info))) branch;
  VCS.delete_branch branch;
  if keep = KeepProof then VCS.propagate_sideff None

let process_transaction verbosely (loc, expr) =
  let warn_if_pos a b =
    if b then msg_warning(pr_ast a ++ str" should not be part of a script") in
  let v, x = expr, (verbosely && Flags.is_verbose(), loc, expr) in
  prerr_endline ("{{{ execute: "^ string_of_ppcmds (pr_ast x));
  let vcs = VCS.backup () in
  try
    let head = VCS.current_branch () in
    VCS.checkout head;
    begin
      let c = classify_vernac v in
      prerr_endline ("  classified as: " ^ string_of_vernac_classification c);
      match c with
      (* Joining various parts of the document *)
      | VtStm (VtJoinDocument, b), VtNow -> warn_if_pos x b; join ()
      | VtStm (VtFinish, b),       VtNow -> warn_if_pos x b; finish ()
      | VtStm (VtObserve id, b),   VtNow -> warn_if_pos x b; observe id
      | VtStm ((VtObserve _ | VtFinish | VtJoinDocument), _), VtLater ->
          anomaly(str"classifier: join actions cannot be classified as VtLater")
      
      (* Back *)
      | VtStm (VtBack oid, true), w ->
          let id = VCS.new_node () in
          let bl = Backtrack.branches_of oid in
          List.iter (fun branch ->
            if not (List.mem branch bl) then
              merge_proof_branch
                (false,Loc.ghost,VernacAbortAll) DropProof branch)
            (VCS.branches ());
          VCS.checkout_shallowest_proof_branch ();
          VCS.commit id (Alias oid);
          Backtrack.record (); if w = VtNow then finish ()
      | VtStm (VtBack id, false), VtNow ->
          prerr_endline ("undo to state " ^ string_of_state_id id);
          Backtrack.backto id;
          VCS.checkout_shallowest_proof_branch ();
          Reach.known_state ~cache:(interactive ()) id;
      | VtStm (VtBack id, false), VtLater ->
          anomaly(str"classifier: VtBack + VtLater must imply part_of_script")

      (* Query *)
      | VtQuery false, VtNow ->
          finish ();
          (try Future.purify (interp dummy_state_id) (true,loc,expr)
           with e when Errors.noncritical e ->
             let e = Errors.push e in
             raise(State.exn_on dummy_state_id e))
      | VtQuery true, w ->
          let id = VCS.new_node () in
          VCS.commit id (Cmd x);
          Backtrack.record (); if w = VtNow then finish ()
      | VtQuery false, VtLater ->
          anomaly(str"classifier: VtQuery + VtLater must imply part_of_script")

      (* Proof *)
      | VtStartProof (mode, names), w ->
          let id = VCS.new_node () in
          let bname = VCS.mk_branch_name x in
          VCS.checkout VCS.master;
          VCS.commit id (Fork (x, bname, names));
          VCS.branch bname (`Proof (mode, VCS.proof_nesting () + 1));
          Proof_global.activate_proof_mode mode;
          Backtrack.record (); if w = VtNow then finish ()
      | VtProofStep, w ->
          let id = VCS.new_node () in
          VCS.commit id (Cmd x);
          Backtrack.record (); if w = VtNow then finish ()
      | VtQed keep, w ->
          merge_proof_branch x keep head;
          VCS.checkout_shallowest_proof_branch ();
          Backtrack.record (); if w = VtNow then finish ()
          
      (* Side effect on all branches *)
      | VtSideff, w ->
          let id = VCS.new_node () in
          VCS.checkout VCS.master;
          VCS.commit id (Cmd x);
          VCS.propagate_sideff (Some x);
          VCS.checkout_shallowest_proof_branch ();
          Backtrack.record (); if w = VtNow then finish ()

      (* Unknown: we execute it, check for open goals and propagate sideeff *)
      | VtUnknown, VtNow ->
          let id = VCS.new_node () in
          let step () =
            VCS.checkout VCS.master;
            let mid = VCS.get_branch_pos VCS.master in
            Reach.known_state ~cache:(interactive ()) mid;
            interp id x;
            (* Vernac x may or may not start a proof *)
            if head = VCS.master &&
               Proof_global.there_are_pending_proofs ()
            then begin
              let bname = VCS.mk_branch_name x in
              VCS.commit id (Fork (x,bname,[]));
              VCS.branch bname (`Proof ("Classic", VCS.proof_nesting () + 1))
            end else begin
              VCS.commit id (Cmd x);
              VCS.propagate_sideff (Some x);
              VCS.checkout_shallowest_proof_branch ();
            end in
          State.define ~cache:true step id;
          Backtrack.record ()

      | VtUnknown, VtLater ->
          anomaly(str"classifier: VtUnknown must imply VtNow")
    end;
    (* Proof General *)
    begin match v with 
      | VernacStm (PGLast _) ->
        if head <> VCS.master then
          interp dummy_state_id
            (true,Loc.ghost,VernacShow (ShowGoal OpenSubgoals))
      | _ -> ()
    end;
    prerr_endline "executed }}}";
    VCS.print ()
  with e ->
    match Stateid.get_state_id e with
    | None ->
        VCS.restore vcs;
        VCS.print ();
        anomaly (str ("execute: "^ 
          string_of_ppcmds (Errors.print_no_report e) ^ "}}}"))
    | Some (_, id) ->
        let e = Errors.push e in
        prerr_endline ("Failed at state " ^ Stateid.string_of_state_id id);
        VCS.restore vcs;
        VCS.print ();
        raise e

(* Query API *)

let get_current_state () = Backtrack.cur ()

let current_proof_depth () =
  let head = VCS.current_branch () in
  match VCS.get_branch head with
  | { VCS.kind = `Master } -> 0
  | { VCS.pos = cur; VCS.kind = `Proof (_,n); VCS.root = root } ->
      let rec distance cur =
        if cur = root then 0
        else 1 + distance (VCS.visit cur).next in
      distance cur

let unmangle n =
  let n = VCS.string_of_branch_name n in
  let idx = String.index n '_' + 1 in
  Names.id_of_string (String.sub n idx (String.length n - idx))

let proofname b = match VCS.get_branch b with
  | { VCS.kind = `Proof _ } -> Some b
  | _ -> None

let get_all_proof_names () =
  List.map unmangle (List.map_filter proofname (VCS.branches ()))

let get_current_proof_name () =
  Option.map unmangle (proofname (VCS.current_branch ()))

let get_script prf =
  let rec find acc id =
    if id = initial_state_id || id = dummy_state_id then acc else
    let view = VCS.visit id in
    match view.step with
    | `Fork (_,_,ns) when List.mem prf ns -> acc
    | `Qed ((x,_,_), proof) -> find [pi3 x, (VCS.get_info id).n_goals] proof
    | `Sideff (`Ast (x,id)) -> find ((pi3 x, (VCS.get_info id).n_goals)::acc) id
    | `Sideff (`Id id)  -> find acc id
    | `Cmd x -> find ((pi3 x, (VCS.get_info id).n_goals)::acc) view.next 
    | `Alias id -> find acc id
    | `Fork _ -> find acc view.next
    in
  find [] (VCS.get_branch_pos VCS.master)

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
      let _ = assert (Int.equal ng (ngprev - 1)) in
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
      match proof with
      | None -> Pfedit.get_current_proof_name ()
      | Some (id,_) -> id in
    let cmds = get_script prf in
    let _,_,_,indented_cmds =
      List.fold_left indent_script_item ((1,[]),false,[],[]) cmds
    in
    let indented_cmds = List.rev (indented_cmds) in
    msg_notice (v 0 (Pp.prlist_with_sep Pp.fnl (fun x -> x) indented_cmds))
  with Proof_global.NoCurrentProof -> ()

let () = Vernacentries.show_script := show_script

(* vim:set foldmethod=marker: *)
