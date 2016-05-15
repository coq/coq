open Pp
open Printer
open Util


(** [is_profiling] and the profiling info ([stack]) should be synchronized with the document; the rest of the ref cells are either local to individual tactic invocations, or global flags, and need not be synchronized, since no document-level backtracking happens within tactics.  We synchronize is_profiling via an option. *)
let is_profiling = ref false

let set_profiling b = is_profiling := b
let get_profiling () = !is_profiling

let should_display_profile_at_close = ref false
let set_display_profile_at_close b = should_display_profile_at_close := b


let new_call = ref false
let entered_call() = new_call := true
let is_new_call() = let b = !new_call in new_call := false; b

(** LtacProf cannot yet handle backtracking into multi-success tactics.  To properly support this, we'd have to somehow recreate our location in the call-stack, and stop/restart the intervening timers.  This is tricky and possibly expensive, so instead we currently just emit a warning that profiling results will be off. *)
let encountered_multi_success_backtracking = ref false
let warn_encountered_multi_success_backtracking() =
  if !encountered_multi_success_backtracking
  then msg_warning (str "Ltac Profiler cannot yet handle backtracking into multi-success tactics; profiling results may be wildly inaccurate.")
let encounter_multi_success_backtracking() =
  if not !encountered_multi_success_backtracking
  then begin
    encountered_multi_success_backtracking := true;
    warn_encountered_multi_success_backtracking()
  end


type entry = {mutable total : float; mutable local : float; mutable ncalls : int; mutable max_total : float}
let empty_entry() = {total = 0.; local = 0.; ncalls = 0; max_total = 0.}
let add_entry e add_total {total; local; ncalls; max_total} =
  if add_total then e.total <- e.total +. total;
  e.local <- e.local +. local;
  e.ncalls <- e.ncalls + ncalls;
  if add_total then e.max_total <- max e.max_total max_total

type treenode = {entry : entry; children : (string, treenode) Hashtbl.t}

(** Tobias Tebbi wrote some tricky code involving mutation.  Rather than rewriting it in a functional style, we simply freeze the state when we need to by issuing a deep copy of the profiling data. *)
let deepcopy_entry {total; local; ncalls; max_total} =
  {total; local; ncalls; max_total}

let rec deepcopy_treenode {entry; children} =
  {entry = deepcopy_entry entry;
   children =
      (let children' = Hashtbl.create (Hashtbl.length children) in
       Hashtbl.iter
	 (fun key subtree -> Hashtbl.add children' key (deepcopy_treenode subtree))
	 children;
       children')}

let stack = Summary.ref ~freeze:(fun _ -> List.map deepcopy_treenode) [{entry=empty_entry(); children=Hashtbl.create 20}] ~name:"LtacProf-stack"

let on_stack = Hashtbl.create 5

let get_node c table =
  try Hashtbl.find table c
  with Not_found ->
    let new_node = {entry=empty_entry(); children=Hashtbl.create 5} in
    Hashtbl.add table c new_node;
    new_node

let rec add_node node node' =
  add_entry node.entry true node'.entry;
  Hashtbl.iter
    (fun s node' -> add_node (get_node s node.children) node')
    node'.children

let time() =
  let times = Unix.times() in
  times.Unix.tms_utime +. times.Unix.tms_stime

let rec print_treenode indent (tn : treenode) =
  msgnl(str(indent^"{ entry = {"));
  msg(str(indent^"total = "));
  msgnl(str (indent^(string_of_float (tn.entry.total))));
  msg(str(indent^"local = "));
  msgnl(str (indent^(string_of_float tn.entry.local)));
  msg(str(indent^"ncalls = "));
  msgnl(str (indent^(string_of_int tn.entry.ncalls)));
  msg(str(indent^"max_total = "));
  msgnl(str (indent^(string_of_float tn.entry.max_total)));
  msgnl(str(indent^"}"));
  msgnl(str(indent^"children = {"));
  Hashtbl.iter
    (fun s node ->
      msgnl(str(indent^" "^s^" |-> "));
      print_treenode (indent^"  ") node
    )
    tn.children;
  msgnl(str(indent^"} }"))

let rec print_stack (st : treenode list) =
  (match st with
    | [] -> msgnl(str "[]")
    | x::xs -> print_treenode "" x; msgnl(str("::")); print_stack xs)


let string_of_call ck =
  let s =
  string_of_ppcmds
    (match ck with
       | Proof_type.LtacNotationCall s -> Names.KerName.print s
       | Proof_type.LtacNameCall cst -> Pptactic.pr_ltac_constant cst
       | Proof_type.LtacVarCall (id,t) -> Nameops.pr_id id
       | Proof_type.LtacAtomCall te ->
	 (Pptactic.pr_glob_tactic (Global.env())
	    (Tacexpr.TacAtom (Loc.ghost,te)))
       | Proof_type.LtacConstrInterp (c,_) ->
	 pr_glob_constr_env (Global.env()) c
       | Proof_type.LtacMLCall te ->
	 (Pptactic.pr_glob_tactic (Global.env())
            te)
    ) in
  for i = 0 to String.length s - 1 do if s.[i] = '\n' then s.[i] <- ' ' done;
  let s = try String.sub s 0 (CString.string_index_from s 0 "(*") with Not_found -> s in
  CString.strip s

let exit_tactic start_time add_total c =
  try
    let node :: stack' = !stack in
    let parent = List.hd stack' in
    stack := stack';
    if add_total then Hashtbl.remove on_stack (string_of_call c);
    let diff = time() -. start_time in
    parent.entry.local <- parent.entry.local -. diff;
    add_entry node.entry add_total {total = diff; local = diff; ncalls = 1; max_total = diff};
  with Failure("hd") -> (* oops, our stack is invalid *)
    encounter_multi_success_backtracking()

let tclFINALLY tac (finally : unit Proofview.tactic) =
  let open Proofview.Notations in
  Proofview.tclIFCATCH
    tac
    (fun v -> finally <*> Proofview.tclUNIT v)
    (fun (exn,info) -> finally <*> Proofview.tclZERO ~info exn)

let do_profile s call_trace tac =
  let open Proofview.Notations in
  Proofview.tclLIFT (Proofview.NonLogical.make (fun () ->
  if !is_profiling && is_new_call() then
    match call_trace with
      | (_, c) :: _ ->
	let s = string_of_call c in
	let parent = List.hd !stack in
	let node, add_total = try Hashtbl.find on_stack s, false
			      with Not_found ->
				   let node = get_node s parent.children in
				   Hashtbl.add on_stack s node;
				   node, true
	in
	if not add_total && node = List.hd !stack then None else (
	  stack := node :: !stack;
	  let start_time = time() in
          Some (start_time, add_total)
	)
      | [] -> None
  else None)) >>= function
  | Some (start_time, add_total) ->
    tclFINALLY
      tac
      (Proofview.tclLIFT (Proofview.NonLogical.make (fun () ->
	(match call_trace with
	| (_, c) :: _ ->
          exit_tactic start_time add_total c
	| [] -> ()))))
  | None -> tac



let format_sec x = (Printf.sprintf "%.3fs" x)
let format_ratio x = (Printf.sprintf "%.1f%%" (100. *. x))
let padl n s = ws (max 0 (n - utf8_length s)) ++ str s
let padr n s = str s ++ ws (max 0 (n - utf8_length s))
let padr_with c n s =
  let ulength = utf8_length s in
  str (utf8_sub s 0 n) ++ str(String.make (max 0 (n - ulength)) c)

let rec list_iter_is_last f = function
  | []      -> ()
  | [x]     -> f true x
  | x :: xs -> f false x; list_iter_is_last f xs

let header() =
  msgnl(str" tactic                                    self  total   calls       max");
  msgnl(str"────────────────────────────────────────┴──────┴──────┴───────┴─────────┘")

let rec print_node all_total indent prefix (s,n) =
  let e = n.entry in
  msgnl(
    h 0(
      padr_with '-' 40 (prefix ^ s ^ " ")
      ++padl 7 (format_ratio (e.local /. all_total))
      ++padl 7 (format_ratio (e.total /. all_total))
      ++padl 8 (string_of_int e.ncalls)
      ++padl 10 (format_sec(e.max_total))
    )
    );
  print_table all_total indent false n.children

and print_table all_total indent first_level table =
  let ls = Hashtbl.fold
	     (fun s n l -> if n.entry.total /. all_total < 0.02 then l else (s, n) :: l)
      table [] in
  match ls with
  | [(s,n)]  when (not first_level) ->
     print_node all_total indent (indent^"└") (s,n)
  | _ ->
     let ls = List.sort (fun (_, n1) (_, n2) -> compare n2.entry.total n1.entry.total) ls in
     list_iter_is_last
       (fun is_last ->
	print_node
	  all_total
	  (indent^if first_level then "" else if is_last then "  " else " │")
	  (indent^if first_level then "─" else if is_last then " └─" else " ├─")
       )
       ls

let print_results() =
  let tree = (List.hd !stack).children in
  let all_total = -. (List.hd !stack).entry.local in
  let global = Hashtbl.create 20 in
  let rec cumulate table =
    Hashtbl.iter
      (fun s node ->
	let node' = get_node s global in
	add_entry node'.entry true node.entry;
	cumulate node.children
      )
      table
  in
  cumulate tree;
  warn_encountered_multi_success_backtracking();
  msgnl(str"");
  msgnl(h 0(
      str"total time: "++padl 11 (format_sec(all_total))
    )
       );
  msgnl(str"");
  header();
  print_table all_total "" true global;
  msgnl(str"");
  header();
  print_table all_total "" true tree
  (* FOR DEBUGGING *)
  (* ;
     msgnl(str"");
     print_stack(!stack)
  *)

let print_results_tactic tactic =
  let tree = (List.hd !stack).children in
  let table_tactic = Hashtbl.create 20 in
  let rec cumulate table =
    Hashtbl.iter
      (fun s node ->
       if String.sub (s^".") 0 (min (1+String.length s) (String.length tactic)) = tactic
       then add_node (get_node s table_tactic) node
       else cumulate node.children
      )
      table
  in
  cumulate tree;
  let all_total = -. (List.hd !stack).entry.local in
  let tactic_total =
    Hashtbl.fold
      (fun _ node all_total -> node.entry.total +. all_total)
      table_tactic 0. in
  warn_encountered_multi_success_backtracking();
  msgnl(str"");
   msgnl(h 0(
      str"total time:           "++padl 11 (format_sec(all_total))
    )
	);
   msgnl(h 0(
      str"time spent in tactic: "++padl 11 (format_sec(tactic_total))
    )
       );
  msgnl(str"");
  header();
  print_table tactic_total "" true table_tactic

let reset_profile() =
  stack := [{entry=empty_entry(); children=Hashtbl.create 20}];
  encountered_multi_success_backtracking := false

let do_print_results_at_close () =
  if !should_display_profile_at_close
  then print_results ()
  else ()

let _ = Declaremods.append_end_library_hook do_print_results_at_close
