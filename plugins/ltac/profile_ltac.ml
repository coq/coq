(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Unicode
open Pp
open Printer
open Util

module M = CString.Map

(** [is_profiling] and the profiling info ([stack]) should be synchronized with
    the document; the rest of the ref cells are either local to individual
    tactic invocations, or global flags, and need not be synchronized, since no
    document-level backtracking happens within tactics. We synchronize
    is_profiling via an option. *)
let is_profiling = Flags.profile_ltac

let set_profiling b = is_profiling := b
let get_profiling () = !is_profiling

(** LtacProf cannot yet handle backtracking into multi-success tactics.
    To properly support this, we'd have to somehow recreate our location in the
    call-stack, and stop/restart the intervening timers. This is tricky and
    possibly expensive, so instead we currently just emit a warning that
    profiling results will be off. *)
let encountered_multi_success_backtracking = ref false

let warn_profile_backtracking =
  CWarnings.create ~name:"profile-backtracking" ~category:"ltac"
    (fun () -> strbrk "Ltac Profiler cannot yet handle backtracking \
       into multi-success tactics; profiling results may be wildly inaccurate.")

let warn_encountered_multi_success_backtracking () =
  if !encountered_multi_success_backtracking then
    warn_profile_backtracking ()

let encounter_multi_success_backtracking () =
  if not !encountered_multi_success_backtracking
  then begin
    encountered_multi_success_backtracking := true;
    warn_encountered_multi_success_backtracking ()
  end


(* *************** tree data structure for profiling ****************** *)

type treenode = {
  name : M.key;
  total : float;
  local : float;
  ncalls : int;
  max_total : float;
  children : treenode M.t
}

let empty_treenode name = {
  name;
  total = 0.0;
  local = 0.0;
  ncalls = 0;
  max_total = 0.0;
  children = M.empty;
}

let root = "root"

module Local = Summary.Local

let stack = Local.ref ~name:"LtacProf-stack" [empty_treenode root]

let reset_profile_tmp () =
  Local.(stack := [empty_treenode root]);
  encountered_multi_success_backtracking := false

(* ************** XML Serialization  ********************* *)

let rec of_ltacprof_tactic (name, t) =
  assert (String.equal name t.name);
  let open Xml_datatype in
  let total = string_of_float t.total in
  let local = string_of_float t.local in
  let ncalls = string_of_int t.ncalls in
  let max_total = string_of_float t.max_total in
  let children = List.map of_ltacprof_tactic (M.bindings t.children) in
  Element ("ltacprof_tactic",
    [ ("name", name); ("total",total); ("local",local);
      ("ncalls",ncalls); ("max_total",max_total)],
    children)

let of_ltacprof_results t =
  let open Xml_datatype in
  assert(String.equal t.name root);
  let children = List.map of_ltacprof_tactic (M.bindings t.children) in
  Element ("ltacprof", [("total_time", string_of_float t.total)], children)

let rec to_ltacprof_tactic m xml =
  let open Xml_datatype in
  match xml with
  | Element ("ltacprof_tactic",
     [("name", name); ("total",total); ("local",local);
      ("ncalls",ncalls); ("max_total",max_total)], xs) ->
      let node = {
         name;
         total = float_of_string total;
         local = float_of_string local;
         ncalls = int_of_string ncalls;
         max_total = float_of_string max_total;
         children = List.fold_left to_ltacprof_tactic M.empty xs;
       } in
      M.add name node m
  | _ -> CErrors.anomaly Pp.(str "Malformed ltacprof_tactic XML.")

let to_ltacprof_results xml =
  let open Xml_datatype in
  match xml with
  | Element ("ltacprof", [("total_time", t)], xs) ->
     { name = root;
       total = float_of_string t;
       ncalls = 0;
       max_total = 0.0;
       local = 0.0;
       children = List.fold_left to_ltacprof_tactic M.empty xs }
  | _ -> CErrors.anomaly Pp.(str "Malformed ltacprof XML.")

let feedback_results results =
  Feedback.(feedback
    (Custom (None, "ltacprof_results", of_ltacprof_results results)))

(* ************** pretty printing ************************************* *)

let format_sec x = (Printf.sprintf "%.3fs" x)
let format_ratio x = (Printf.sprintf "%.1f%%" (100. *. x))
let padl n s = ws (max 0 (n - utf8_length s)) ++ str s
let padr_with c n s =
  let ulength = utf8_length s in
  str (utf8_sub s 0 n) ++ str (String.make (max 0 (n - ulength)) c)

let rec list_iter_is_last f = function
  | []      -> []
  | [x]     -> [f true x]
  | x :: xs -> f false x :: list_iter_is_last f xs

let header =
  str " tactic                                   local  total   calls       max " ++
  fnl () ++
  str "────────────────────────────────────────┴──────┴──────┴───────┴─────────┘" ++
  fnl ()

let rec print_node ~filter all_total indent prefix (s, e) =
  h 0 (
    padr_with '-' 40 (prefix ^ s ^ " ")
    ++ padl 7 (format_ratio (e.local /. all_total))
    ++ padl 7 (format_ratio (e.total /. all_total))
    ++ padl 8 (string_of_int e.ncalls)
    ++ padl 10 (format_sec (e.max_total))
  ) ++
  fnl () ++
  print_table ~filter all_total indent false e.children

and print_table ~filter all_total indent first_level table =
  let fold _ n l =
    let s, total = n.name, n.total in
    if filter s total then (s, n) :: l else l in
  let ls = M.fold fold table [] in
  match ls with
  | [s, n] when not first_level ->
     v 0 (print_node ~filter all_total indent (indent ^ "└") (s, n))
  | _ ->
    let ls =
      List.sort (fun (_, { total = s1 }) (_, { total = s2}) ->
                   compare s2 s1) ls in
    let iter is_last =
     let sep0 = if first_level then "" else if is_last then "  " else " │" in
     let sep1 = if first_level then "─" else if is_last then " └─" else " ├─" in
     print_node ~filter all_total (indent ^ sep0) (indent ^ sep1)
    in
    prlist (fun pr -> pr) (list_iter_is_last iter ls)

let to_string ~filter ?(cutoff=0.0) node =
  let tree = node.children in
  let all_total = M.fold (fun _ { total } a -> total +. a) node.children 0.0 in
  let flat_tree =
    let global = ref M.empty in
    let find_tactic tname l =
      try M.find tname !global
      with Not_found ->
        let e = empty_treenode tname in
        global := M.add tname e !global;
        e in
    let add_tactic tname stats = global := M.add tname stats !global in
    let sum_stats add_total
      { name; total = t1; local = l1; ncalls = n1; max_total = m1 }
      {       total = t2; local = l2; ncalls = n2; max_total = m2 } = {
          name;
          total = if add_total then t1 +. t2 else t1;
          local = l1 +. l2;
          ncalls = n1 + n2;
          max_total = if add_total then max m1 m2 else m1;
          children = M.empty;
      } in
    let rec cumulate table =
      let iter _ ({ name; children } as statistics) =
        if filter name then begin
          let stats' = find_tactic name global in
          add_tactic name (sum_stats true stats' statistics);
        end;
        cumulate children
      in
      M.iter iter table
    in
    cumulate tree;
    !global
  in
  warn_encountered_multi_success_backtracking ();
  let filter s n = filter s && (all_total <= 0.0 || n /. all_total >= cutoff /. 100.0) in
  let msg =
    h 0 (str "total time: " ++ padl 11 (format_sec (all_total))) ++
    fnl () ++
    fnl () ++
    header ++
    print_table ~filter all_total "" true flat_tree ++
    fnl () ++
    header ++
    print_table ~filter all_total "" true tree
  in
  msg

(* ******************** profiling code ************************************** *)

let get_child name node =
  try M.find name node.children
  with Not_found -> empty_treenode name

let time () =
  let times = Unix.times () in
  times.Unix.tms_utime +. times.Unix.tms_stime

let string_of_call ck =
  let s =
  string_of_ppcmds
    (match ck with
       | Tacexpr.LtacNotationCall s -> Pptactic.pr_alias_key s
       | Tacexpr.LtacNameCall cst -> Pptactic.pr_ltac_constant cst
       | Tacexpr.LtacVarCall (id, t) -> Names.Id.print id
       | Tacexpr.LtacAtomCall te ->
         (Pptactic.pr_glob_tactic (Global.env ())
            (Tacexpr.TacAtom (Loc.tag te)))
       | Tacexpr.LtacConstrInterp (c, _) ->
         pr_glob_constr_env (Global.env ()) c
       | Tacexpr.LtacMLCall te ->
         (Pptactic.pr_glob_tactic (Global.env ())
            te)
    ) in
  let s = String.map (fun c -> if c = '\n' then ' ' else c) s in
  let s = try String.sub s 0 (CString.string_index_from s 0 "(*") with Not_found -> s in
  CString.strip s

let rec merge_sub_tree name tree acc =
  try
    let t = M.find name acc in
    let t = {
      name;
      total = t.total +. tree.total;
      ncalls = t.ncalls + tree.ncalls;
      local = t.local +. tree.local;
      max_total = max t.max_total tree.max_total;
      children = M.fold merge_sub_tree tree.children t.children;
    } in
    M.add name t acc
  with Not_found -> M.add name tree acc

let merge_roots ?(disjoint=true) t1 t2 =
  assert(String.equal t1.name t2.name);
  { name = t1.name;
    ncalls = t1.ncalls + t2.ncalls;
    local = if disjoint then t1.local +. t2.local else t1.local;
    total = if disjoint then t1.total +. t2.total else t1.total;
    max_total = if disjoint then max t1.max_total t2.max_total else t1.max_total;
    children =
      M.fold merge_sub_tree t2.children t1.children }

let rec find_in_stack what acc = function
  | [] -> None
  | { name } as x :: rest when String.equal name what -> Some(acc, x, rest)
  | { name } as x :: rest -> find_in_stack what (x :: acc) rest

let exit_tactic ~count_call start_time c =
  let diff = time () -. start_time in
  match Local.(!stack) with
  | [] | [_] ->
    (* oops, our stack is invalid *)
    encounter_multi_success_backtracking ();
    reset_profile_tmp ()
  | node :: (parent :: rest as full_stack) ->
    let name = string_of_call c in
    if not (String.equal name node.name) then
      (* oops, our stack is invalid *)
      encounter_multi_success_backtracking ();
    let node = { node with
      total = node.total +. diff;
      local = node.local +. diff;
      ncalls = node.ncalls + (if count_call then 1 else 0);
      max_total = max node.max_total diff;
    } in
    (* updating the stack *)
    let parent =
      match find_in_stack node.name [] full_stack with
      | None ->
         (* no rec-call, we graft the subtree *)
         let parent = { parent with
           local = parent.local -. diff;
           children = M.add node.name node parent.children } in
         Local.(stack := parent :: rest);
         parent
      | Some(to_update, self, rest) ->
         (* we coalesce the rec-call and update the lower stack *)
         let self = merge_roots ~disjoint:false self node in
         let updated_stack =
           List.fold_left (fun s x ->
             (try M.find x.name (List.hd s).children
              with Not_found -> x) :: s) (self :: rest) to_update in
         Local.(stack := updated_stack);
         List.hd Local.(!stack)
    in
    (* Calls are over, we reset the stack and send back data *)
    if rest == [] && get_profiling () then begin
      assert(String.equal root parent.name);
      reset_profile_tmp ();
      feedback_results parent
    end

let tclFINALLY tac (finally : unit Proofview.tactic) =
  let open Proofview.Notations in
  Proofview.tclIFCATCH
    tac
    (fun v -> finally <*> Proofview.tclUNIT v)
    (fun (exn, info) -> finally <*> Proofview.tclZERO ~info exn)

let do_profile s call_trace ?(count_call=true) tac =
  let open Proofview.Notations in
  Proofview.tclLIFT (Proofview.NonLogical.make (fun () ->
  if !is_profiling then
    match call_trace, Local.(!stack) with
      | (_, c) :: _, parent :: rest ->
        let name = string_of_call c in
        let node = get_child name parent in
        Local.(stack := node :: parent :: rest);
        Some (time ())
      | _ :: _, [] -> assert false
      | _ -> None
  else None)) >>= function
  | Some start_time ->
    tclFINALLY
      tac
      (Proofview.tclLIFT (Proofview.NonLogical.make (fun () ->
        (match call_trace with
        | (_, c) :: _ -> exit_tactic ~count_call start_time c
        | [] -> ()))))
  | None -> tac

(* ************** Accumulation of data from workers ************************* *)

let get_local_profiling_results () = List.hd Local.(!stack)

(* We maintain our own cache of document data, given that the
   semantics of the STM implies that synchronized state for opaque
   proofs will be lost on QED. This provides some complications later
   on as we will have to simulate going back on the document on our
   own. *)
module DData = struct
    type t = Feedback.doc_id * Stateid.t
    let compare x y = Pervasives.compare x y
end

module SM = Map.Make(DData)

let data = ref SM.empty

let _ =
  Feedback.(add_feeder (function
    | { doc_id = d;
        span_id = s;
        contents = Custom (_, "ltacprof_results", xml) } ->
        let results = to_ltacprof_results xml in
        let other_results = (* Multi success can cause this *)
          try SM.find (d,s) !data
          with Not_found -> empty_treenode root in
        data := SM.add (d,s) (merge_roots results other_results) !data
    | _ -> ()))

let reset_profile () =
  reset_profile_tmp ();
  data := SM.empty

(* ****************************** Named timers ****************************** *)

let timer_data = ref M.empty

let timer_name = function
  | Some v -> v
  | None -> ""

let restart_timer name =
  timer_data := M.add (timer_name name) (System.get_time ()) !timer_data

let get_timer name =
  try M.find (timer_name name) !timer_data
  with Not_found -> System.get_time ()

let finish_timing ~prefix name =
  let tend = System.get_time () in
  let tstart = get_timer name in
  Feedback.msg_info(str prefix ++ pr_opt str name ++ str " ran for " ++
                    System.fmt_time_difference tstart tend)

(* ******************** *)

let print_results_filter ~cutoff ~filter =
  (* The STM doesn't provide yet a proper document query and traversal
     API, thus we need to re-check if some states are current anymore
     (due to backtracking) using the `state_of_id` API. *)
  let valid (did,id) _ = Stm.(state_of_id ~doc:(get_doc did) id) <> `Expired in
  data := SM.filter valid !data;
  let results =
    SM.fold (fun _ -> merge_roots ~disjoint:true) !data (empty_treenode root) in
  let results = merge_roots results Local.(CList.last !stack) in
  Feedback.msg_info (to_string ~cutoff ~filter results)
;;

let print_results ~cutoff =
  print_results_filter ~cutoff ~filter:(fun _ -> true)

let print_results_tactic tactic =
  print_results_filter ~cutoff:!Flags.profile_ltac_cutoff ~filter:(fun s ->
    String.(equal tactic (sub (s ^ ".") 0 (min (1+length s) (length tactic)))))

let do_print_results_at_close () =
  if get_profiling () then print_results ~cutoff:!Flags.profile_ltac_cutoff

let _ = Declaremods.append_end_library_hook do_print_results_at_close

let _ =
  let open Goptions in
  declare_bool_option
    { optdepr  = false;
      optname  = "Ltac Profiling";
      optkey   = ["Ltac"; "Profiling"];
      optread  = get_profiling;
      optwrite = set_profiling }
