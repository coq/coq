open Ast;;
open Coqast;;
open Tacmach;;
open Proof_trees;;
open Pp;;
open Printer;;
open Util;;
open Proof_type;;

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
    Node(_, "TACTICLIST", a::b::tl) -> true
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

let rec local_interp : Coqast.t -> report_holder -> tactic = function
    Node(_, "TACTICLIST", [a;Node(_, "TACLIST", l)]) ->
      (fun report_holder -> checked_thens report_holder a l)
  | Node(_, "TACTICLIST", a::((Node(_, "TACLIST", l))as b)::c::tl) ->
      local_interp(ope ("TACTICLIST", (ope("TACTICLIST", [a;b]))::c::tl))
  | Node(_, "TACTICLIST", [a;b]) ->
      (fun report_holder -> checked_then report_holder a b)
  | Node(_, "TACTICLIST", a::b::c::tl) ->
	local_interp(ope ("TACTICLIST", (ope("TACTICLIST", [a;b]))::c::tl))
  | ast ->
      (fun report_holder g ->
	try
	  let (gls, _) as result = Tacinterp.interp ast g in
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

and checked_thens: report_holder -> Coqast.t -> Coqast.t list -> tactic = 
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
           flag (Tacinterp.interp t1)) in
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
		   let (gls,_) as result = Tacinterp.interp tac_i g in
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

and checked_then: report_holder -> Coqast.t -> Coqast.t -> tactic =
  (fun report_holder t1 t2 g ->
    let flag = ref true in
    let card_holder = ref Fail in
    let tac_t1 =
      if traceable t1 then
	(count_subgoals2 card_holder flag (local_interp t1))
      else
	(count_subgoals card_holder flag (Tacinterp.interp t1)) in
    let new_tree_holder = ref ([] : report_tree list) in
    let (gls, _) as result =
      tclTHEN tac_t1
	(fun (g:goal sigma) -> 
	  if !flag then
	    if traceable t2 then
	      local_interp t2 new_tree_holder g
	    else
	      try
		let (gls, _) as result = Tacinterp.interp t2 g in
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

let on_then : tactic_arg list -> tactic = function
  (Tacexp t1)::(Tacexp t2)::l ->
  tclTHEN_i (Tacinterp.interp t1)
    (fun i ->
      if List.mem (Integer (i + 1)) l then
      	(Tacinterp.interp t2)
      else
	tclIDTAC)
  | _ -> error "bad arguments for on_then";;

(* Analyzing error reports *)

let rec select_success n = function
    [] -> []
  | Report_node(true,_,_)::tl -> (Num((0,0),n))::select_success (n+1) tl
  | _::tl -> select_success (n+1) tl;;

let rec expand_tactic = function
    Node(loc1, "TACTICLIST", [a;Node(loc2,"TACLIST", l)]) ->
      Node(loc1, "TACTICLIST",
	   [expand_tactic a;
	     Node(loc2, "TACLIST", List.map expand_tactic l)])
  | Node(loc1, "TACTICLIST", a::((Node(loc2, "TACLIST", l))as b)::c::tl) ->
      expand_tactic (Node(loc1, "TACTICLIST",
			  (Node(loc1, "TACTICLIST", [a;b]))::c::tl))
  | Node(loc1, "TACTICLIST", [a;b]) ->
      Node(loc1, "TACTICLIST",[expand_tactic a;expand_tactic b])
  | Node(loc1, "TACTICLIST", a::b::c::tl) ->
      expand_tactic (Node(loc1, "TACTICLIST",
			  (Node(loc1, "TACTICLIST", [a;b]))::c::tl))
  | any -> any;;

let rec reconstruct_success_tac ast = 
  match ast with
    Node(_, "TACTICLIST", [a;Node(_,"TACLIST",l)]) ->
      (function 
	  Report_node(true, n, l) -> ast
      	| Report_node(false, n, rl) ->
	    ope("TACTICLIST",[a;ope("TACLIST", 
				    List.map2 reconstruct_success_tac l rl)])
      	| Failed n -> ope("Idtac",[])
      	| Tree_fail r -> reconstruct_success_tac a r
      	| Mismatch (n,p) -> a)
  | Node(_, "TACTICLIST", [a;b]) ->
      (function
	  Report_node(true, n, l) -> ast
	| Report_node(false, n, rl) ->
	    let selected_indices = select_success 1 rl in
	    ope("OnThen", a::b::selected_indices)
	| Failed n -> ope("Idtac",[])
	| Tree_fail r -> reconstruct_success_tac a r
	| _ -> error "this error case should not happen in a THEN tactic")
  | _ -> 
      (function
	  Report_node(true, n, l) -> ast
	| Failed n -> ope("Idtac",[])
	| _ ->
	    errorlabstrm
	      "this error case should not happen on an unknown tactic"
              (str "error in reconstruction with " ++ fnl () ++
	       (gentacpr ast)));;
	  

let rec path_to_first_error = function
| Report_node(true, _, l) ->
  let rec find_first_error n = function
  | (Report_node(true, _, _))::tl -> find_first_error (n + 1) tl
  | it::tl -> n, it
  | [] -> error "no error detected" in
  let p, t = find_first_error 1 l in
    p::(path_to_first_error t)
| _ -> [];;

let rec flatten_then_list tail = function
  | Node(_, "TACTICLIST", [a;b]) ->
      flatten_then_list ((flatten_then b)::tail) a
  | ast -> ast::tail
and flatten_then = function
    Node(_, "TACTICLIST", [a;b]) ->
      ope("TACTICLIST", flatten_then_list [flatten_then b] a)
  | Node(_, "TACLIST", l) ->
      ope("TACLIST", List.map flatten_then l)
  | Node(_, "OnThen", t1::t2::l) ->
      ope("OnThen", (flatten_then t1)::(flatten_then t2)::l)
  | ast -> ast;;

let debug_tac = function
    [(Tacexp ast)] ->
      (fun g -> 
      	let report = ref ([] : report_tree list) in
      	let result = local_interp ast report g in
      	let clean_ast = expand_tactic ast in
      	let report_tree =
          try List.hd !report with
	    Failure "hd" -> (msgnl (str "report is empty"); Failed 1) in
      	let success_tac = 
	  reconstruct_success_tac clean_ast report_tree in
        let compact_success_tac =
	  flatten_then success_tac in
      	msgnl (fnl () ++
	       str "=========    Successful tactic    =============" ++
               fnl () ++
	       gentacpr compact_success_tac ++ fnl () ++
	       str "========= End of successful tactic ============");
      	result)
  | _ -> error "wrong arguments for debug_tac";;

add_tactic "DebugTac" debug_tac;;

hide_tactic "OnThen" on_then;;

let rec clean_path p ast l = 
  match ast, l with
    Node(_, "TACTICLIST", ([_;_] as tacs)), fst::tl ->
       fst::(clean_path 0 (List.nth tacs (fst - 1)) tl)
  | Node(_, "TACTICLIST", tacs), 2::tl ->
     let rank = (List.length tacs) - p in
     rank::(clean_path 0 (List.nth tacs (rank - 1)) tl)
  | Node(_, "TACTICLIST", tacs), 1::tl ->
      clean_path (p+1) ast tl
  | Node(_, "TACLIST", tacs), fst::tl ->
      fst::(clean_path 0 (List.nth tacs (fst - 1)) tl)
  | _, [] -> []
  | _, _ -> failwith "this case should not happen in clean_path";;



let rec report_error
    : Coqast.t -> goal sigma option ref -> Coqast.t ref -> int list ref -> 
      int list -> tactic =
  fun ast the_goal the_ast returned_path path -> 
    match ast with
      Node(loc1, "TACTICLIST", [a;(Node(loc2, "TACLIST", l)) as tail]) ->
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
			  the_ast := ope("TACTICLIST", [!the_ast; tail]);
			  raise !the_exn
	    | Goals_mismatch p -> 
		the_ast := ast;
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
    | Node(_, "TACTICLIST", a::((Node(_, "TACLIST", l)) as b)::c::tl) ->
	report_error(ope("TACTICLIST", (ope("TACTICLIST", [a;b]))::c::tl))
	  the_goal the_ast returned_path path
    | Node(_, "TACTICLIST", [a;b]) ->
	let the_count = ref 1 in
	tclTHEN
	  (fun g ->
	    try
	      report_error a the_goal the_ast returned_path (1::path) g
	    with
	      e ->
		(the_ast := ope("TACTICLIST", [!the_ast; b]);
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
		     str " after tactic " ++ gentacpr a);
		raise e)
    | Node(_, "TACTICLIST", a::b::c::tl) ->
	report_error (ope("TACTICLIST", (ope("TACTICLIST", [a;b]))::c::tl))
	  the_goal the_ast returned_path path
    | ast ->
	(fun g ->
	  try
	   Tacinterp.interp ast g
	  with
	    e ->
	      (the_ast := ast;
	       the_goal := Some g;
	       returned_path := path;
	       raise e));;

let strip_some = function
    Some n -> n
  | None -> failwith "No optional value";;

let descr_first_error = function
    [(Tacexp ast)] ->
      (fun g ->
	let the_goal = ref (None : goal sigma option) in
	let the_ast = ref ast in
	let the_path = ref ([] : int list) in
	try
	  let result = report_error ast the_goal the_ast the_path [] g in
	  msgnl (str "no Error here");
	  result
	with
	  e ->
	    (msgnl (str "Execution of this tactic raised message " ++ fnl () ++
		    fnl () ++ Cerrors.explain_exn e ++ fnl () ++
		    fnl () ++ str "on goal"  ++ fnl () ++
		    pr_goal (sig_it (strip_some !the_goal)) ++ fnl () ++
		    str "faulty tactic is" ++ fnl () ++ fnl () ++
		    gentacpr (flatten_then !the_ast) ++ fnl ());
	     tclIDTAC g))
  | _ -> error "wrong arguments for descr_first_error";;

add_tactic "DebugTac2" descr_first_error;;
