(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open CErrors
open Util
open Goptions

type s_info=
    {mutable created_steps     : int; (* node count*)
     mutable pruned_steps      : int;
     mutable created_branches  : int; (* path count *)
     mutable pruned_branches   : int;
     mutable created_hyps      : int; (* hyps count *)
     mutable pruned_hyps       : int;
     mutable branch_failures   : int;
     mutable branch_successes  : int;
     mutable nd_branching      : int}

let s_info=
    {created_steps    = 0; (* node count*)
     pruned_steps     = 0;
     created_branches = 0; (* path count *)
     pruned_branches  = 0;
     created_hyps     = 0; (* hyps count *)
     pruned_hyps      = 0;
     branch_failures  = 0;
     branch_successes = 0;
     nd_branching     = 0}

let reset_info () =
     s_info.created_steps    <- 0; (* node count*)
     s_info.pruned_steps     <- 0;
     s_info.created_branches <- 0; (* path count *)
     s_info.pruned_branches  <- 0;
     s_info.created_hyps     <- 0; (* hyps count *)
     s_info.pruned_hyps      <- 0;
     s_info.branch_failures  <- 0;
     s_info.branch_successes <- 0;
     s_info.nd_branching     <- 0

let pruning = ref true

let opt_pruning=
  {optdepr=false;
   optname="Rtauto Pruning";
   optkey=["Rtauto";"Pruning"];
   optread=(fun () -> !pruning);
   optwrite=(fun b -> pruning:=b)}

let _ = declare_bool_option opt_pruning

type form=
    Atom of int
  | Arrow of form * form
  | Bot
  | Conjunct of form * form
  | Disjunct of form * form

module FOrd = struct
  type t = form
  let rec compare x y =
    match x, y with
    | Bot, Bot -> 0
    | Bot, _ -> -1
    | Atom _, Bot -> 1
    | Atom a1, Atom a2 -> Int.compare a1 a2
    | Atom _, _ -> -1
    | Arrow _, (Bot | Atom _) -> 1
    | Arrow (f1, g1), Arrow (f2, g2) ->
        let cmp = compare f1 f2 in
        if cmp = 0 then compare g1 g2 else cmp
    | Arrow _, _ -> -1
    | Conjunct _, (Bot | Atom _ | Arrow _) -> 1
    | Conjunct (f1, g1), Conjunct (f2, g2) ->
        let cmp = compare f1 f2 in
        if cmp = 0 then compare g1 g2 else cmp
    | Conjunct _, _ -> -1
    | Disjunct _, (Bot | Atom _ | Arrow _ | Conjunct _) -> 1
    | Disjunct (f1, g1), Disjunct (f2, g2) ->
        let cmp = compare f1 f2 in
        if cmp = 0 then compare g1 g2 else cmp
end
module Fmap = Map.Make(FOrd)

type sequent =
    {rev_hyps: form Int.Map.t;
     norev_hyps: form Int.Map.t;
     size:int;
     left:int Fmap.t;
     right:(int*form) list Fmap.t;
     cnx:(int*int*form*form) list;
     abs:int option;
     gl:form}

let add_one_arrow i f1 f2 m=
  try Fmap.add f1 ((i,f2)::(Fmap.find f1 m)) m with
      Not_found ->
	Fmap.add f1 [i,f2] m

type proof =
    Ax of int
  | I_Arrow of proof
  | E_Arrow of int*int*proof
  | D_Arrow of int*proof*proof
  | E_False of int
  | I_And of proof*proof
  | E_And of int*proof
  | D_And of int*proof
  | I_Or_l of proof
  | I_Or_r of proof
  | E_Or of int*proof*proof
  | D_Or of int*proof
  | Pop of int*proof

type rule =
    SAx of int
  | SI_Arrow
  | SE_Arrow of int*int
  | SD_Arrow of int
  | SE_False of int
  | SI_And
  | SE_And of int
  | SD_And of int
  | SI_Or_l
  | SI_Or_r
  | SE_Or of int
  | SD_Or of int

let add_step s sub =
  match s,sub with
      SAx i,[] -> Ax i
    | SI_Arrow,[p] -> I_Arrow p
    | SE_Arrow(i,j),[p] -> E_Arrow (i,j,p)
    | SD_Arrow i,[p1;p2] -> D_Arrow (i,p1,p2)
    | SE_False i,[] -> E_False i
    | SI_And,[p1;p2] -> I_And(p1,p2)
    | SE_And i,[p] -> E_And(i,p)
    | SD_And i,[p] -> D_And(i,p)
    | SI_Or_l,[p] -> I_Or_l p
    | SI_Or_r,[p] -> I_Or_r p
    | SE_Or i,[p1;p2] -> E_Or(i,p1,p2)
    | SD_Or i,[p] -> D_Or(i,p)
    | _,_ -> anomaly ~label:"add_step" (Pp.str "wrong arity.")

type 'a with_deps =
    {dep_it:'a;
     dep_goal:bool;
     dep_hyps:Int.Set.t}

type slice=
    {proofs_done:proof list;
     proofs_todo:sequent with_deps list;
     step:rule;
     needs_goal:bool;
     needs_hyps:Int.Set.t;
     changes_goal:bool;
     creates_hyps:Int.Set.t}

type state =
    Complete of proof
  | Incomplete of sequent * slice list

let project = function
    Complete prf -> prf
  | Incomplete (_,_) -> anomaly (Pp.str "not a successful state.")

let pop n prf =
  let nprf=
    match prf.dep_it with
	Pop (i,p) -> Pop (i+n,p)
      | p -> Pop(n,p) in
    {prf with dep_it = nprf}

let rec fill stack proof =
  match stack with
      [] -> Complete proof.dep_it
    | slice::super ->
	if
	  !pruning &&
	  List.is_empty slice.proofs_done &&
	  not (slice.changes_goal && proof.dep_goal) &&
	  not (Int.Set.exists
		 (fun i -> Int.Set.mem i proof.dep_hyps)
		 slice.creates_hyps)
	then
	  begin
	    s_info.pruned_steps<-s_info.pruned_steps+1;
	    s_info.pruned_branches<- s_info.pruned_branches +
	    List.length slice.proofs_todo;
	    let created_here=Int.Set.cardinal slice.creates_hyps in
	      s_info.pruned_hyps<-s_info.pruned_hyps+
	      List.fold_left
		(fun sum dseq -> sum + Int.Set.cardinal dseq.dep_hyps)
		created_here slice.proofs_todo;
	    fill super (pop (Int.Set.cardinal slice.creates_hyps) proof)
	  end
	else
	  let dep_hyps=
	    Int.Set.union slice.needs_hyps
	      (Int.Set.diff proof.dep_hyps slice.creates_hyps) in
	  let dep_goal=
	    slice.needs_goal ||
	    ((not slice.changes_goal) && proof.dep_goal) in
	  let proofs_done=
	    proof.dep_it::slice.proofs_done in
	    match slice.proofs_todo with
		[] ->
		  fill super {dep_it =
				add_step slice.step (List.rev proofs_done);
			      dep_goal = dep_goal;
			      dep_hyps = dep_hyps}
	      | current::next ->
		  let nslice=
		    {proofs_done=proofs_done;
		     proofs_todo=next;
		     step=slice.step;
		     needs_goal=dep_goal;
		     needs_hyps=dep_hyps;
		     changes_goal=current.dep_goal;
		     creates_hyps=current.dep_hyps} in
		    Incomplete (current.dep_it,nslice::super)

let append stack (step,subgoals) =
  s_info.created_steps<-s_info.created_steps+1;
  match subgoals with
      [] ->
	s_info.branch_successes<-s_info.branch_successes+1;
	fill stack {dep_it=add_step step.dep_it [];
		    dep_goal=step.dep_goal;
		    dep_hyps=step.dep_hyps}
    | hd :: next ->
	s_info.created_branches<-
	s_info.created_branches+List.length next;
	let slice=
	  {proofs_done=[];
	   proofs_todo=next;
	   step=step.dep_it;
	   needs_goal=step.dep_goal;
	   needs_hyps=step.dep_hyps;
	   changes_goal=hd.dep_goal;
	   creates_hyps=hd.dep_hyps} in
	  Incomplete(hd.dep_it,slice::stack)

let embed seq=
  {dep_it=seq;
   dep_goal=false;
   dep_hyps=Int.Set.empty}

let change_goal seq gl=
    {seq with
       dep_it={seq.dep_it with gl=gl};
       dep_goal=true}

let add_hyp seqwd f=
  s_info.created_hyps<-s_info.created_hyps+1;
  let seq=seqwd.dep_it in
  let num = seq.size+1 in
  let left = Fmap.add f num seq.left in
  let cnx,right=
    try
      let l=Fmap.find f seq.right in
	List.fold_right (fun (i,f0) l0 -> (num,i,f,f0)::l0) l seq.cnx,
	Fmap.remove f seq.right
    with Not_found -> seq.cnx,seq.right in
  let nseq=
    match f with
	Bot ->
	  {seq with
	     left=left;
	     right=right;
	     size=num;
	     abs=Some num;
	     cnx=cnx}
      | Atom _ ->
	  {seq with
	     size=num;
	     left=left;
	     right=right;
	     cnx=cnx}
      | Conjunct (_,_) | Disjunct (_,_) ->
	  {seq with
	     rev_hyps=Int.Map.add num f seq.rev_hyps;
	     size=num;
	     left=left;
	     right=right;
	     cnx=cnx}
      | Arrow (f1,f2) ->
	  let ncnx,nright=
	    try
	      let i = Fmap.find f1 seq.left in
		(i,num,f1,f2)::cnx,right
	    with Not_found ->
	      cnx,(add_one_arrow num f1 f2 right) in
	    match f1 with
		Conjunct (_,_) | Disjunct (_,_) ->
		  {seq with
		     rev_hyps=Int.Map.add num f seq.rev_hyps;
		     size=num;
		     left=left;
		     right=nright;
		     cnx=ncnx}
	      | Arrow(_,_) ->
		  {seq with
		     norev_hyps=Int.Map.add num f seq.norev_hyps;
		     size=num;
		     left=left;
		     right=nright;
		     cnx=ncnx}
	      | _ ->
		  {seq with
		     size=num;
		     left=left;
		     right=nright;
		     cnx=ncnx} in
    {seqwd with
       dep_it=nseq;
       dep_hyps=Int.Set.add num seqwd.dep_hyps}

exception Here_is of (int*form)

let choose m=
  try
    Int.Map.iter (fun i f -> raise (Here_is (i,f))) m;
    raise Not_found
  with
      Here_is (i,f) -> (i,f)


let search_or seq=
  match seq.gl with
      Disjunct (f1,f2) ->
	[{dep_it = SI_Or_l;
	  dep_goal = true;
	  dep_hyps = Int.Set.empty},
	 [change_goal (embed seq) f1];
	 {dep_it = SI_Or_r;
	  dep_goal = true;
	  dep_hyps = Int.Set.empty},
	 [change_goal (embed seq) f2]]
    | _ -> []

let search_norev seq=
  let goals=ref (search_or seq) in
  let add_one i f=
    match f with
	Arrow (Arrow (f1,f2),f3) ->
	  let nseq =
	    {seq with norev_hyps=Int.Map.remove i seq.norev_hyps} in
	    goals:=
	      ({dep_it=SD_Arrow(i);
		dep_goal=false;
		dep_hyps=Int.Set.singleton i},
	       [add_hyp
		  (add_hyp
		     (change_goal (embed nseq) f2)
		     (Arrow(f2,f3)))
		  f1;
		add_hyp (embed nseq) f3]):: !goals
      | _ -> anomaly ~label:"search_no_rev" (Pp.str "can't happen.") in
    Int.Map.iter add_one seq.norev_hyps;
    List.rev !goals

let search_in_rev_hyps seq=
  try
    let i,f=choose seq.rev_hyps in
    let make_step step=
      {dep_it=step;
       dep_goal=false;
       dep_hyps=Int.Set.singleton i} in
    let nseq={seq with rev_hyps=Int.Map.remove i seq.rev_hyps} in
      match f with
	  Conjunct (f1,f2) ->
	    [make_step (SE_And(i)),
	     [add_hyp (add_hyp (embed nseq) f1) f2]]
	| Disjunct (f1,f2) ->
	    [make_step (SE_Or(i)),
	     [add_hyp (embed nseq) f1;add_hyp (embed nseq) f2]]
	| Arrow (Conjunct (f1,f2),f0) ->
	    [make_step (SD_And(i)),
	     [add_hyp (embed nseq) (Arrow (f1,Arrow (f2,f0)))]]
	| Arrow (Disjunct (f1,f2),f0) ->
	    [make_step (SD_Or(i)),
	     [add_hyp (add_hyp (embed nseq) (Arrow(f1,f0))) (Arrow (f2,f0))]]
	| _ -> anomaly ~label:"search_in_rev_hyps" (Pp.str "can't happen.")
  with
      Not_found -> search_norev seq

let search_rev seq=
  match seq.cnx with
      (i,j,f1,f2)::next ->
	let nseq=
	  match f1 with
	      Conjunct (_,_) | Disjunct (_,_) ->
		{seq with cnx=next;
		   rev_hyps=Int.Map.remove j seq.rev_hyps}
	    | Arrow (_,_) ->
		{seq with cnx=next;
		   norev_hyps=Int.Map.remove j seq.norev_hyps}
	    | _ ->
		{seq with cnx=next} in
	  [{dep_it=SE_Arrow(i,j);
	    dep_goal=false;
	    dep_hyps=Int.Set.add i (Int.Set.singleton j)},
	   [add_hyp (embed nseq) f2]]
    | [] ->
	match seq.gl with
	    Arrow (f1,f2) ->
	      [{dep_it=SI_Arrow;
		dep_goal=true;
		dep_hyps=Int.Set.empty},
	       [add_hyp (change_goal (embed seq) f2) f1]]
	  | Conjunct (f1,f2) ->
	      [{dep_it=SI_And;
		dep_goal=true;
		dep_hyps=Int.Set.empty},[change_goal (embed seq) f1;
					change_goal (embed seq) f2]]
	  | _ -> search_in_rev_hyps seq

let search_all seq=
  match seq.abs with
      Some i ->
	[{dep_it=SE_False (i);
	  dep_goal=false;
	  dep_hyps=Int.Set.singleton i},[]]
    | None ->
	try
	  let ax = Fmap.find seq.gl seq.left in
	    [{dep_it=SAx (ax);
	      dep_goal=true;
	      dep_hyps=Int.Set.singleton ax},[]]
	with Not_found -> search_rev seq

let bare_sequent = embed
		     {rev_hyps=Int.Map.empty;
		      norev_hyps=Int.Map.empty;
		      size=0;
		      left=Fmap.empty;
		      right=Fmap.empty;
		      cnx=[];
		      abs=None;
		      gl=Bot}

let init_state hyps gl=
  let init = change_goal bare_sequent gl in
  let goal=List.fold_right (fun (_,f,_) seq ->add_hyp seq f) hyps init in
    Incomplete (goal.dep_it,[])

let success= function
    Complete _ -> true
  | Incomplete (_,_) -> false

let branching = function
    Incomplete (seq,stack) ->
      Control.check_for_interrupt ();
      let successors = search_all seq in
      let _ =
	match successors with
	    [] -> s_info.branch_failures<-s_info.branch_failures+1
	  | _::next ->
	      s_info.nd_branching<-s_info.nd_branching+List.length next in
	List.map (append stack) successors
  | Complete prf -> anomaly (Pp.str "already succeeded.")

open Pp

let rec pp_form =
  function
      Arrow(f1,f2) -> (pp_or f1) ++ (str " -> ") ++ (pp_form f2)
    | f -> pp_or f
and pp_or = function
    Disjunct(f1,f2) ->
      (pp_or f1) ++ (str " \\/ ") ++ (pp_and f2)
  | f -> pp_and f
and pp_and = function
    Conjunct(f1,f2) ->
      (pp_and f1) ++ (str " /\\ ") ++ (pp_atom f2)
  | f -> pp_atom f
and pp_atom= function
    Bot -> str "#"
  | Atom n -> int n
  | f -> str "(" ++ hv 2 (pp_form f) ++ str ")"

let pr_form f = pp_form f

let pp_intmap map =
  let pp=ref (str "") in
   Int.Map.iter (fun i obj -> pp:= (!pp ++
		pp_form obj ++ cut ())) map;
    str "{ " ++ v 0 (!pp) ++ str " }"

let pp_list pp_obj l=
let pp=ref (str "") in
  List.iter (fun o -> pp := !pp ++ (pp_obj o) ++ str ", ") l;
  str "[ " ++ !pp ++ str "]"

let pp_mapint map =
  let pp=ref (str "") in
   Fmap.iter (fun obj l -> pp:= (!pp ++
		pp_form obj ++ str " => " ++
				 pp_list (fun (i,f) -> pp_form f) l ++
				 cut ()) ) map;
    str "{ " ++ hv 0 (!pp ++ str " }")

let pp_connect (i,j,f1,f2) = pp_form f1 ++ str " => " ++ pp_form f2

let pp_gl gl= cut () ++
  str "{ " ++ hv 0 (
	      begin
		match gl.abs with
		    None -> str ""
		  | Some i -> str "ABSURD" ++ cut ()
	      end ++
  str "rev   =" ++ pp_intmap gl.rev_hyps ++ cut () ++
  str "norev =" ++ pp_intmap gl.norev_hyps ++ cut () ++
  str "arrows=" ++ pp_mapint gl.right ++ cut () ++
  str "cnx   =" ++ pp_list pp_connect gl.cnx ++ cut () ++
  str "goal  =" ++ pp_form gl.gl ++ str " }")

let pp =
  function
      Incomplete(gl,ctx) -> pp_gl gl ++ fnl ()
    | _ -> str "<complete>"

let pp_info () =
  let count_info =
    if !pruning then
	str "Proof steps : " ++
	int s_info.created_steps ++ str " created / " ++
	int s_info.pruned_steps ++ str " pruned" ++ fnl () ++
	str "Proof branches : " ++
	int s_info.created_branches ++ str " created / " ++
	int s_info.pruned_branches ++ str " pruned" ++ fnl () ++
	str "Hypotheses : " ++
	int s_info.created_hyps ++ str " created / " ++
	int s_info.pruned_hyps ++ str " pruned" ++ fnl ()
    else
	str "Pruning is off" ++ fnl () ++
	str "Proof steps : " ++
	int s_info.created_steps ++ str " created" ++ fnl () ++
	str "Proof branches : " ++
	int s_info.created_branches ++ str " created" ++ fnl () ++
	str "Hypotheses : " ++
	int s_info.created_hyps ++ str " created" ++ fnl () in
    Feedback.msg_info
      ( str "Proof-search statistics :" ++ fnl () ++
	count_info ++
	str "Branch ends: " ++
	int s_info.branch_successes ++ str " successes / " ++
	int s_info.branch_failures ++ str " failures" ++ fnl () ++
	str "Non-deterministic choices : " ++
	int s_info.nd_branching ++ str " branches")



