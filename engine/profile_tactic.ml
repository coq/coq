(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Unicode
open Pp
open Util

module M = CString.Map

let profile_ltac = ref false
let profile_ltac_cutoff = ref 2.0

(** [is_profiling] and the profiling info ([stack]) should be synchronized with
    the document; the rest of the ref cells are either local to individual
    tactic invocations, or global flags, and need not be synchronized, since no
    document-level backtracking happens within tactics. We synchronize
    is_profiling via an option. *)
let is_profiling = profile_ltac

let set_profiling b = is_profiling := b
let get_profiling () = !is_profiling

let get_profiling_cutoff () = string_of_float !profile_ltac_cutoff
let set_profiling_cutoff s =
  try profile_ltac_cutoff := float_of_string s
  with Failure _ -> CErrors.user_err Pp.(str "Ltac Profiling Cutoff must be interpretable as a float.")

let encountered_invalid_stack_no_self = ref false

let warn_invalid_stack_no_self =
  CWarnings.create ~name:"profile-invalid-stack-no-self" ~category:CWarnings.CoreCategories.ltac
    (fun () -> strbrk
        "Ltac Profiler encountered an invalid stack (no self \
         node). This can happen if you reset the profile during \
         tactic execution.")

let encounter_invalid_stack_no_self () =
  if not !encountered_invalid_stack_no_self
  then begin
    encountered_invalid_stack_no_self := true;
    warn_invalid_stack_no_self ()
  end


(* *************** tree data structure for profiling ****************** *)

type treenode = {
  name : string;
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


let stack = Summary.ref ~name:"LtacProf-stack" ~local:true [empty_treenode root]

let reset_profile_tmp () = stack := [empty_treenode root]

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
  if Int.equal n ulength then str s
  else if n < ulength then str (utf8_sub s 0 n)
  else str s ++ str (String.make (n - ulength) c)

let rec list_map_is_last f = function
  | []      -> []
  | [x]     -> [f true x]
  | x :: xs -> f false x :: list_map_is_last f xs

let repeat_str n s =
  if String.is_empty s then s
  else
    let len = String.length s in
    String.init (n * len) (fun i -> s.[i mod len])

let header_name = " tactic"
let header_name_width = utf8_length header_name

let header_rest = "┴──────┴──────┴───────┴─────────┘"
let header_rest_width = utf8_length header_rest

let header name_width =
  str " tactic" ++ str (String.make (name_width - header_name_width) ' ') ++ str "  local  total   calls       max" ++
  fnl () ++
  str (repeat_str name_width "─") ++ str header_rest ++
  fnl ()

module Line = struct
  type t = {
    prefix : string;
    tac_name : string;
    local : float;
    total : float;
    calls : int;
    maxtime : float;
  }

  let pr ~name_width l =
    h (
      padr_with '-' name_width (l.prefix ^ l.tac_name ^ " ")
      ++ padl 7 (format_ratio l.local)
      ++ padl 7 (format_ratio l.total)
      ++ padl 8 (string_of_int l.calls)
      ++ padl 10 (format_sec l.maxtime))
end

let rec linearize_node ~filter all_total indent prefix (s, e) =
  { Line.prefix; tac_name=s;
    local = (e.local /. all_total);
    total = (e.total /. all_total);
    calls = e.ncalls;
    maxtime = e.max_total;
  } :: linearize_table ~filter all_total indent false e.children

and linearize_table ~filter all_total indent first_level table =
  let fold _ n l =
    let s, total = n.name, n.total in
    if filter s total then (s, n) :: l else l in
  let ls = M.fold fold table [] in
  match ls with
  | [s, n] when not first_level ->
    linearize_node ~filter all_total indent (indent ^ "└") (s, n)
  | _ ->
    let ls =
      List.sort (fun (_, { total = s1 }) (_, { total = s2}) ->
          compare s2 s1) ls in
    let iter is_last =
      let sep0 = if first_level then "" else if is_last then "  " else " │" in
      let sep1 = if first_level then "─" else if is_last then " └─" else " ├─" in
      linearize_node ~filter all_total (indent ^ sep0) (indent ^ sep1)
    in
    List.concat (list_map_is_last iter ls)

let get_printing_width = ref (fun () -> Format.pp_get_margin Format.std_formatter ())

let set_get_printing_width f = get_printing_width := f
let get_printing_width () = !get_printing_width ()

let print_table ~filter all_total table =
  let lines = linearize_table ~filter all_total "" true table in
  let name_width = List.fold_left (fun acc (l:Line.t) ->
      max acc (utf8_length (l.prefix ^ l.tac_name)))
      0
      lines
  in
  let name_width = name_width + 1 (* +1 for a space at the end *) in
  (* respect Printing Width unless it's so short that we can't print the header correctly *)
  let name_width = min (get_printing_width() - header_rest_width) name_width in
  let name_width = max header_name_width name_width in
  header name_width ++
  prlist_with_sep fnl (Line.pr ~name_width) lines

let to_string ~filter ~cutoff node =
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
  let filter s n = filter s && (all_total <= 0.0 || n /. all_total >= cutoff /. 100.0) in
  let msg =
    h (str "total time: " ++ padl 11 (format_sec (all_total))) ++
    fnl () ++
    fnl () ++
    print_table ~filter all_total flat_tree ++
    fnl () ++ fnl () ++
    print_table ~filter all_total tree
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
  let s = string_of_ppcmds ck in
  let s = String.map (fun c -> if c = '\n' then ' ' else c) s in
  let s = try String.sub s 0 (CString.string_index_from s 0 "(*") with Not_found -> s in
  String.trim s

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

let exit_tactic ~count_call start_time name =
  let diff = time () -. start_time in
  match !stack with
  | [] | [_] ->
    (* oops, our stack is invalid *)
    encounter_invalid_stack_no_self ();
    reset_profile_tmp ()
  | node :: (parent :: rest as full_stack) ->
    if not (String.equal name node.name) then
      (* oops, our stack is invalid *)
      CErrors.anomaly
        (Pp.strbrk "Ltac Profiler encountered an invalid stack (wrong self node) \
                    likely due to backtracking into multi-success tactics.");
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
         stack := parent :: rest;
         parent
      | Some(to_update, self, rest) ->
         (* we coalesce the rec-call and update the lower stack *)
         let self = merge_roots ~disjoint:false self node in
         let updated_stack =
           List.fold_left (fun s x ->
             (try M.find x.name (List.hd s).children
              with Not_found -> x) :: s) (self :: rest) to_update in
         stack := updated_stack;
         List.hd !stack
    in
    (* Calls are over, we reset the stack and send back data *)
    if rest == [] && get_profiling () then begin
      assert(String.equal root parent.name);
      encountered_invalid_stack_no_self := false;
      reset_profile_tmp ();
      feedback_results parent
    end

(** [tclWRAPFINALLY before tac finally] runs [before] before each
    entry-point of [tac] and passes the result of [before] to
    [finally], which is then run at each exit-point of [tac],
    regardless of whether it succeeds or fails.  Said another way, if
    [tac] succeeds, then it behaves as [before >>= fun v -> tac >>= fun
    ret -> finally v <*> tclUNIT ret]; otherwise, if [tac] fails with
    [e], it behaves as [before >>= fun v -> finally v <*> tclZERO
    e]. *)
let rec tclWRAPFINALLY before tac finally =
  let open Proofview in
  let open Proofview.Notations in
  before >>= fun v -> tclCASE tac >>= function
  | Fail (e, info) -> finally v >>= fun () -> tclZERO ~info e
  | Next (ret, tac') -> tclOR
                          (finally v >>= fun () -> tclUNIT ret)
                          (fun e -> tclWRAPFINALLY before (tac' e) finally)

let do_profile_gen pp_call call_trace ?(count_call=true) tac =
  let open Proofview.Notations in
  (* We do an early check to [is_profiling] so that we save the
     overhead of [tclWRAPFINALLY] when profiling is not set
     *)
  Proofview.tclLIFT (Proofview.NonLogical.make (fun () -> !is_profiling)) >>= function
  | false -> tac
  | true ->
    tclWRAPFINALLY
      (Proofview.tclLIFT (Proofview.NonLogical.make (fun () ->
             match pp_call call_trace, !stack with
             | Some c, parent :: rest ->
               let name = string_of_call c in
               let node = get_child name parent in
               stack := node :: parent :: rest;
               Some (name, time ())
             | Some _, [] -> assert false
             | _ -> None
           )))
      tac
      (function
        | Some (name, start_time) ->
          (Proofview.tclLIFT (Proofview.NonLogical.make (fun () ->
               exit_tactic ~count_call start_time name)))
        | None -> Proofview.tclUNIT ())

(* ************** Accumulation of data from workers ************************* *)

let get_local_profiling_results () = List.hd !stack

(* We maintain our own cache of document data, given that the
   semantics of the STM implies that synchronized state for opaque
   proofs will be lost on QED. This provides some complications later
   on as we will have to simulate going back on the document on our
   own. *)
module DData = struct
    type t = Feedback.doc_id * Stateid.t
    let compare x y = compare x y
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
  encountered_invalid_stack_no_self := false;
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
  Feedback.msg_notice(str prefix ++ pr_opt str name ++ str " ran for " ++
                    System.fmt_time_difference tstart tend)

(* ******************** *)

let print_results_filter ~cutoff ~filter =
  let cutoff = Option.default !profile_ltac_cutoff cutoff in
  data := SM.filter (fun (doc,id) _ -> Stateid.is_valid ~doc id) !data;
  let results =
    SM.fold (fun _ -> merge_roots ~disjoint:true) !data (empty_treenode root) in
  let results = merge_roots results (CList.last !stack) in
  Feedback.msg_notice (to_string ~cutoff ~filter results)
;;

let print_results ~cutoff =
  print_results_filter ~cutoff ~filter:(fun _ -> true)

let print_results_tactic tactic =
  print_results_filter ~cutoff:None ~filter:(fun s ->
    String.(equal tactic (sub (s ^ ".") 0 (min (1+length s) (length tactic)))))

let do_print_results_at_close () =
  if get_profiling () then print_results ~cutoff:None

let () =
  let open Goptions in
  declare_bool_option
    { optstage = Summary.Stage.Interp;
      optdepr  = None;
      optkey   = ["Ltac"; "Profiling"];
      optread  = get_profiling;
      optwrite = set_profiling }

let () =
  let open Goptions in
  declare_string_option
    { optstage = Summary.Stage.Interp;
      optdepr  = None;
      optkey   = ["Ltac"; "Profiling"; "Cutoff"];
      optread  = get_profiling_cutoff;
      optwrite = set_profiling_cutoff }
