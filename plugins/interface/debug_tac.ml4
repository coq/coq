(*i camlp4deps: "parsing/grammar.cma" i*)

open Tacmach;;
open Tacticals;;
open Proof_trees;;
open Pp;;
open Pptactic;;
open Util;;
open Proof_type;;
open Tacexpr;;
open Genarg;;
open Extrawit;;

let pr_glob_tactic = Pptactic.pr_glob_tactic (Global.env())

(* Compacting and uncompacting proof commands *)

type report_tree =
    Report_node of bool *int * report_tree list
  | Mismatch of int * int
  | Tree_fail of report_tree
  | Failed of int;;

type report_card =
    Ngoals of int
  | Goals_mismatch of int
  | Recursive_fail of report_tree
  | Fail;;

type card_holder = report_card ref;;
type report_holder = report_tree list ref;;

(* This tactical receives an integer and a tactic and checks that the
   tactic produces that number of goals.  It never fails but signals failure
   by updating the boolean reference given as third argument to false.
   It is especially suited for use in checked_thens below. *)

let check_subgoals_count : card_holder -> int -> bool ref -> tactic -> tactic =
  fun card_holder count flag t g ->
    try
      let (gls, v) as result = t g in
      let len = List.length (sig_it gls) in
      card_holder :=
      (if len = count then
	  (flag := true;
	  Ngoals count)
       else
          (flag := false;
          Goals_mismatch len));
      result
    with
      e -> card_holder := Fail;
           flag := false;
           tclIDTAC g;;

let no_failure = function
    [Report_node(true,_,_)] -> true
  | _ -> false;;

let check_subgoals_count2 
    : card_holder -> int -> bool ref -> (report_holder -> tactic) -> tactic =
  fun card_holder count flag t g ->
    let new_report_holder = ref ([] : report_tree list) in
    let (gls, v) as result = t new_report_holder g in
    let succeeded = no_failure !new_report_holder in
    let len = List.length (sig_it gls) in
    card_holder :=
      (if (len = count) & succeeded then
	(flag := true;
	 Ngoals count)
      else
	(flag := false;
	 Recursive_fail (List.hd !new_report_holder)));
    result;;

let traceable = function
  | TacThen _ | TacThens _ -> true
  | _ -> false;;

let rec collect_status = function
    Report_node(true,_,_)::tl -> collect_status tl
  | [] -> true
  | _ -> false;;

(* This tactical receives a tactic and executes it, reporting information
   about success in the report holder and a boolean reference. *)

let count_subgoals : card_holder -> bool ref -> tactic -> tactic =
  fun card_holder flag t g ->
    try
      let (gls, _) as result = t g in
      card_holder := (Ngoals(List.length (sig_it gls)));
      flag := true;
      result
    with
      e -> card_holder := Fail;
           flag := false;
           tclIDTAC g;;
   
let count_subgoals2
    : card_holder -> bool ref -> (report_holder -> tactic) -> tactic =
  fun card_holder flag t g ->
    let new_report_holder = ref([] : report_tree list) in
    let (gls, v) as result = t new_report_holder g in
    let succeeded = no_failure !new_report_holder in
    if succeeded then
      (flag := true;
       card_holder := Ngoals (List.length (sig_it gls)))
    else
      (flag := false;
       card_holder := Recursive_fail(List.hd !new_report_holder));
    result;;

let rec local_interp : glob_tactic_expr -> report_holder -> tactic = function
    TacThens (a,l) ->
      (fun report_holder -> checked_thens report_holder a l)
  | TacThen (a,[||],b,[||]) ->
      (fun report_holder -> checked_then report_holder a b)
  | t ->
      (fun report_holder g ->
	try
	  let (gls, _) as result = Tacinterp.eval_tactic t g in
	  report_holder := (Report_node(true, List.length (sig_it gls), []))
			    ::!report_holder;
	  result
	with e -> (report_holder := (Failed 1)::!report_holder;
		   tclIDTAC g))


(* This tactical receives a tactic and a list of tactics as argument.
   It applies the first tactic and then maps the list of tactics to
   various produced sub-goals.  This tactic will never fail, but reports
   are added in the report_holder in the following way:
   - In case of partial success, a new report_tree is added to the report_holder
   - In case of failure of the first tactic, with no more indications
     then Failed 0 is added to the report_holder,
   - In case of partial failure of the first tactic then (Failed n) is added to
     the report holder.
   - In case of success of the first tactic, but count mismatch, then
     Mismatch n is added to the report holder. *)

and checked_thens: report_holder -> glob_tactic_expr -> glob_tactic_expr list -> tactic = 
  (fun report_holder t1 l g ->
    let flag = ref true in
    let traceable_t1 = traceable t1 in
    let card_holder = ref Fail in
    let new_holder = ref ([]:report_tree list) in
    let tac_t1 = 
      if traceable_t1 then
	(check_subgoals_count2 card_holder (List.length l)
           flag (local_interp t1))
      else
	(check_subgoals_count card_holder (List.length l)
           flag (Tacinterp.eval_tactic t1)) in
    let (gls, _) as result = 
      tclTHEN_i tac_t1
	(fun i ->
	  if !flag then
	    (fun g -> 
              let tac_i = (List.nth l i) in
	      if traceable tac_i then
                 local_interp tac_i new_holder g
              else
		 try
		   let (gls,_) as result = Tacinterp.eval_tactic tac_i g in
		   let len = List.length (sig_it gls) in
				   new_holder :=
		     (Report_node(true, len, []))::!new_holder;
		   result
		 with
			       e -> (new_holder := (Failed 1)::!new_holder;
			 tclIDTAC g))
	  else
	    tclIDTAC) g in
      let new_goal_list = sig_it gls in
      (if !flag then
	report_holder := 
	  (Report_node(collect_status !new_holder,
		    (List.length new_goal_list),
		    List.rev !new_holder))::!report_holder
      else
	report_holder :=
	  (match !card_holder with
	    Goals_mismatch(n) -> Mismatch(n, List.length l)
	  | Recursive_fail tr -> Tree_fail tr
	  | Fail -> Failed 1
	  | _ -> errorlabstrm "check_thens"
                  (str "this case should not happen in check_thens"))::
	  !report_holder);
      result)

(* This tactical receives two tactics as argument, it executes the
   first tactic and applies the second one to all the produced goals,
   reporting information about the success of all tactics in the report
   holder. It never fails. *)

and checked_then: report_holder -> glob_tactic_expr -> glob_tactic_expr -> tactic =
  (fun report_holder t1 t2 g ->
    let flag = ref true in
    let card_holder = ref Fail in
    let tac_t1 =
      if traceable t1 then
	(count_subgoals2 card_holder flag (local_interp t1))
      else
	(count_subgoals card_holder flag (Tacinterp.eval_tactic t1)) in
    let new_tree_holder = ref ([] : report_tree list) in
    let (gls, _) as result =
      tclTHEN tac_t1
	(fun (g:goal sigma) -> 
	  if !flag then
	    if traceable t2 then
	      local_interp t2 new_tree_holder g
	    else
	      try
		let (gls, _) as result = Tacinterp.eval_tactic t2 g in
	      	new_tree_holder :=
		  (Report_node(true, List.length (sig_it gls),[]))::
		  !new_tree_holder;
		result
	      with
		e ->
		  (new_tree_holder := ((Failed 1)::!new_tree_holder);
		   tclIDTAC g)
	  else
	    tclIDTAC g) g in
    (if !flag then
      report_holder :=
	(Report_node(collect_status !new_tree_holder,
		     List.length (sig_it gls),
		     List.rev !new_tree_holder))::!report_holder
    else
      report_holder :=
	(match !card_holder with
	  Recursive_fail tr -> Tree_fail tr
	| Fail -> Failed 1
	| _ -> error "this case should not happen in check_then")::!report_holder);
    result);;

(* This tactic applies the given tactic only to those subgoals designated
   by the list of integers given as extra arguments.
 *)

let rawwit_main_tactic = rawwit_tactic tactic_main_level
let globwit_main_tactic = globwit_tactic tactic_main_level
let wit_main_tactic = wit_tactic tactic_main_level


let on_then = function [t1;t2;l] ->
  let t1 = out_gen wit_main_tactic t1 in
  let t2 = out_gen wit_main_tactic t2 in
  let l = out_gen (wit_list0 wit_int) l in
  tclTHEN_i (Tacinterp.eval_tactic t1)
    (fun i ->
      if List.mem (i + 1) l then
      	(Tacinterp.eval_tactic t2)
      else
	tclIDTAC)
  | _ -> anomaly "bad arguments for on_then";;

let mkOnThen t1 t2 selected_indices =
  let a = in_gen rawwit_main_tactic t1 in
  let b = in_gen rawwit_main_tactic t2 in
  let l = in_gen (wit_list0 rawwit_int) selected_indices in
  TacAtom (dummy_loc, TacExtend (dummy_loc, "OnThen", [a;b;l]));;

(* Analyzing error reports *)

let rec select_success n = function
    [] -> []
  | Report_node(true,_,_)::tl -> n::select_success (n+1) tl
  | _::tl -> select_success (n+1) tl;;

let rec reconstruct_success_tac (tac:glob_tactic_expr) =
  match tac with
    TacThens (a,l) ->
      (function 
	  Report_node(true, n, l) -> tac
      	| Report_node(false, n, rl) ->
	    TacThens (a,List.map2 reconstruct_success_tac l rl)
      	| Failed n -> TacId []
      	| Tree_fail r -> reconstruct_success_tac a r
      	| Mismatch (n,p) -> a)
  | TacThen (a,[||],b,[||]) ->
      (function
	  Report_node(true, n, l) -> tac
	| Report_node(false, n, rl) ->
	    let selected_indices = select_success 1 rl in
	    TacAtom (dummy_loc,TacExtend (dummy_loc,"OnThen",
	      [in_gen globwit_main_tactic a;
	       in_gen globwit_main_tactic b;
	       in_gen (wit_list0 globwit_int) selected_indices]))
	| Failed n -> TacId []
	| Tree_fail r -> reconstruct_success_tac a r
	| _ -> error "this error case should not happen in a THEN tactic")
  | _ -> 
      (function
	  Report_node(true, n, l) -> tac
	| Failed n -> TacId []
	| _ ->
	    errorlabstrm
	      "this error case should not happen on an unknown tactic"
              (str "error in reconstruction with " ++ fnl () ++
	       (pr_glob_tactic tac)));;
	  

let rec path_to_first_error = function
| Report_node(true, _, l) ->
  let rec find_first_error n = function
  | (Report_node(true, _, _))::tl -> find_first_error (n + 1) tl
  | it::tl -> n, it
  | [] -> error "no error detected" in
  let p, t = find_first_error 1 l in
    p::(path_to_first_error t)
| _ -> [];;

let debug_tac = function
    [(Tacexp ast)] ->
      (fun g -> 
      	let report = ref ([] : report_tree list) in
      	let result = local_interp ast report g in
      	let clean_ast = (* expand_tactic *) ast in
      	let report_tree =
          try List.hd !report with
	    Failure "hd" -> (msgnl (str "report is empty"); Failed 1) in
      	let success_tac = 
	  reconstruct_success_tac clean_ast report_tree in
        let compact_success_tac = (* flatten_then *) success_tac in
      	msgnl (fnl () ++
	       str "=========    Successful tactic    =============" ++
               fnl () ++
	       pr_glob_tactic compact_success_tac ++ fnl () ++
	       str "========= End of successful tactic ============");
      	result)
  | _ -> error "wrong arguments for debug_tac";;

(* TODO ... used ?
add_tactic "DebugTac" debug_tac;;
*)

Tacinterp.add_tactic "OnThen" on_then;;

let rec clean_path tac l = 
  match tac, l with
  | TacThen (a,[||],b,[||]), fst::tl ->
      fst::(clean_path (if fst = 1 then a else b) tl)
  | TacThens (a,l), 1::tl ->
      1::(clean_path a tl)
  | TacThens (a,tacs), 2::fst::tl ->
      2::fst::(clean_path (List.nth tacs (fst - 1)) tl)
  | _, [] -> []
  | _, _ -> failwith "this case should not happen in clean_path";;

let rec report_error
    : glob_tactic_expr -> goal sigma option ref -> glob_tactic_expr ref -> int list ref -> 
      int list -> tactic =
  fun tac the_goal the_ast returned_path path -> 
    match tac with
      TacThens (a,l) ->
      let the_card_holder = ref Fail in
      let the_flag = ref false in
      let the_exn = ref (Failure "") in
      tclTHENS
	(fun g ->
	  let result =
	    check_subgoals_count 
	      the_card_holder
	      (List.length l) 
	      the_flag
	      (fun g2 -> 
		try 
		  (report_error a the_goal the_ast returned_path (1::path) g2)
	  	with
		  e -> (the_exn := e; raise e))
	      g in
	  if !the_flag then
	    result
	  else
	    (match !the_card_holder with
			Fail -> 
			  the_ast := TacThens (!the_ast, l);
			  raise !the_exn
	    | Goals_mismatch p -> 
		the_ast := tac;
		returned_path := path;
		error ("Wrong number of tactics: expected " ^
		       (string_of_int (List.length l)) ^ " received " ^
		       (string_of_int p))
	    | _ -> error "this should not happen"))
        (let rec fold_num n = function
	    [] -> []
	  | t::tl -> (report_error t the_goal the_ast returned_path (n::2::path))::
	      (fold_num (n + 1) tl) in
	fold_num 1 l)
    | TacThen (a,[||],b,[||]) ->
	let the_count = ref 1 in
	tclTHEN
	  (fun g ->
	    try
	      report_error a the_goal the_ast returned_path (1::path) g
	    with
	      e ->
		(the_ast := TacThen (!the_ast,[||], b,[||]);
		 raise e))
	  (fun g ->
	    try
	      let result = 
		report_error b the_goal the_ast returned_path (2::path) g in
	      the_count := !the_count + 1;
	      result
	    with
	      e ->
		if !the_count > 1 then
		  msgnl
		    (str "in branch no " ++ int !the_count ++
		     str " after tactic " ++ pr_glob_tactic a);
		raise e)
    | tac ->
	(fun g ->
	  try
	   Tacinterp.eval_tactic tac g
	  with
	    e ->
	      (the_ast := tac;
	       the_goal := Some g;
	       returned_path := path;
	       raise e));;

let strip_some = function
    Some n -> n
  | None -> failwith "No optional value";;

let descr_first_error tac =
      (fun g ->
	let the_goal = ref (None : goal sigma option) in
	let the_ast = ref tac in
	let the_path = ref ([] : int list) in
	try
	  let result = report_error tac the_goal the_ast the_path [] g in
	  msgnl (str "no Error here");
	  result
	with
	  e ->
	    (msgnl (str "Execution of this tactic raised message " ++ fnl () ++
		    fnl () ++ Cerrors.explain_exn e ++ fnl () ++
		    fnl () ++ str "on goal"  ++ fnl () ++
		    Printer.pr_goal (sig_it (strip_some !the_goal)) ++
                    fnl () ++ str "faulty tactic is" ++ fnl () ++ fnl () ++
		    pr_glob_tactic ((*flatten_then*) !the_ast) ++ fnl ());
	     tclIDTAC g))

(* TODO ... used ??
add_tactic "DebugTac2" descr_first_error;;
*)

(*
TACTIC EXTEND DebugTac2
  [ ??? ] -> [ descr_first_error tac ]
END
*)
