(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

module Search = Explore.Make(Proof_search)

open Errors
open Util
open Term
open Tacmach
open Proof_search

let force count lazc = incr count;Lazy.force lazc

let step_count = ref 0

let node_count = ref 0

let logic_constant =
  Coqlib.gen_constant "refl_tauto" ["Init";"Logic"]

let li_False = lazy (destInd (logic_constant "False"))
let li_and = lazy (destInd (logic_constant "and"))
let li_or =  lazy (destInd (logic_constant "or"))

let pos_constant =
  Coqlib.gen_constant "refl_tauto" ["Numbers";"BinNums"]

let l_xI = lazy (pos_constant "xI")
let l_xO = lazy (pos_constant "xO")
let l_xH = lazy (pos_constant "xH")

let store_constant =
  Coqlib.gen_constant "refl_tauto" ["rtauto";"Bintree"]

let l_empty = lazy (store_constant "empty")
let l_push = lazy (store_constant "push")

let constant=
  Coqlib.gen_constant "refl_tauto" ["rtauto";"Rtauto"]

let l_Reflect = lazy (constant "Reflect")

let l_Atom = lazy (constant "Atom")
let l_Arrow = lazy (constant "Arrow")
let l_Bot = lazy (constant "Bot")
let l_Conjunct = lazy (constant "Conjunct")
let l_Disjunct = lazy (constant "Disjunct")

let l_Ax = lazy (constant "Ax")
let l_I_Arrow = lazy (constant "I_Arrow")
let l_E_Arrow = lazy (constant "E_Arrow")
let l_D_Arrow = lazy (constant "D_Arrow")
let l_E_False = lazy (constant "E_False")
let l_I_And = lazy (constant "I_And")
let l_E_And = lazy (constant "E_And")
let l_D_And = lazy (constant "D_And")
let l_I_Or_l = lazy (constant "I_Or_l")
let l_I_Or_r = lazy (constant "I_Or_r")
let l_E_Or = lazy (constant "E_Or")
let l_D_Or = lazy (constant "D_Or")


let special_whd gl=
  let infos=Closure.create_clos_infos Closure.betadeltaiota (pf_env gl) in
    (fun t -> Closure.whd_val infos (Closure.inject t))

let special_nf gl=
  let infos=Closure.create_clos_infos Closure.betaiotazeta (pf_env gl) in
    (fun t -> Closure.norm_val infos (Closure.inject t))

type atom_env=
    {mutable next:int;
     mutable env:(constr*int) list}

let make_atom atom_env term=
  try
    let (_,i)=
      List.find (fun (t,_)-> eq_constr term t) atom_env.env
    in Atom i
  with Not_found ->
    let i=atom_env.next in
      atom_env.env <- (term,i)::atom_env.env;
      atom_env.next<- i + 1;
      Atom i

let rec make_form atom_env gls term =
  let normalize=special_nf gls in
  let cciterm=special_whd gls term  in
    match kind_of_term cciterm with
	Prod(_,a,b) ->
	  if not (Termops.dependent (mkRel 1) b) &&
	    Retyping.get_sort_family_of
	    (pf_env gls) (Tacmach.project gls) a == InProp
	  then
	    let fa=make_form atom_env gls a in
	    let fb=make_form atom_env gls b in
	      Arrow (fa,fb)
	  else
	    make_atom atom_env (normalize term)
      | Cast(a,_,_) ->
	  make_form atom_env gls a
      | Ind (ind, _) ->
	  if Names.eq_ind ind (fst (Lazy.force li_False)) then
	    Bot
	  else
	    make_atom atom_env (normalize term)
      | App(hd,argv) when Int.equal (Array.length argv) 2 ->
	  begin
	    try
	      let ind, _ = destInd hd in
		if Names.eq_ind ind (fst (Lazy.force li_and)) then
		  let fa=make_form atom_env gls argv.(0) in
		  let fb=make_form atom_env gls argv.(1) in
		    Conjunct (fa,fb)
		else if Names.eq_ind ind (fst (Lazy.force li_or)) then
		  let fa=make_form atom_env gls argv.(0) in
		  let fb=make_form atom_env gls argv.(1) in
		    Disjunct (fa,fb)
		else make_atom atom_env (normalize term)
	    with DestKO -> make_atom atom_env (normalize term)
	  end
      | _ -> make_atom atom_env (normalize term)

let rec make_hyps atom_env gls lenv = function
    [] -> []
  | (_,Some body,typ)::rest ->
      make_hyps atom_env gls (typ::body::lenv) rest
  | (id,None,typ)::rest ->
      let hrec=
	make_hyps atom_env gls (typ::lenv) rest in
	if List.exists (Termops.dependent (mkVar id)) lenv ||
	  (Retyping.get_sort_family_of
	     (pf_env gls) (Tacmach.project gls) typ != InProp)
	then
	  hrec
	else
	  (id,make_form atom_env gls typ)::hrec

let rec build_pos n =
  if n<=1 then force node_count l_xH
  else if Int.equal (n land 1) 0 then
    mkApp (force node_count l_xO,[|build_pos (n asr 1)|])
  else
    mkApp (force node_count l_xI,[|build_pos (n asr 1)|])

let rec build_form = function
    Atom n -> mkApp (force node_count l_Atom,[|build_pos n|])
  | Arrow (f1,f2) ->
      mkApp (force node_count l_Arrow,[|build_form f1;build_form f2|])
  | Bot -> force node_count l_Bot
  | Conjunct (f1,f2) ->
      mkApp (force node_count l_Conjunct,[|build_form f1;build_form f2|])
  | Disjunct (f1,f2) ->
      mkApp (force node_count l_Disjunct,[|build_form f1;build_form f2|])

let rec decal k = function
    [] -> k
  | (start,delta)::rest ->
      if k>start then
	k - delta
      else
	decal k rest

let add_pop size d pops=
  match pops with
      [] -> [size+d,d]
    | (_,sum)::_ -> (size+sum,sum+d)::pops

let rec build_proof pops size =
  function
      Ax i ->
	mkApp (force step_count l_Ax,
	       [|build_pos (decal i pops)|])
      | I_Arrow p ->
	  mkApp (force step_count l_I_Arrow,
		 [|build_proof pops (size + 1) p|])
      | E_Arrow(i,j,p) ->
	  mkApp (force step_count l_E_Arrow,
		 [|build_pos (decal i pops);
		   build_pos (decal j pops);
		   build_proof pops (size + 1) p|])
      | D_Arrow(i,p1,p2) ->
	  mkApp (force step_count l_D_Arrow,
		 [|build_pos (decal i pops);
		   build_proof pops (size + 2) p1;
		   build_proof pops (size + 1) p2|])
      | E_False i ->
	  mkApp (force step_count l_E_False,
		 [|build_pos (decal i pops)|])
      | I_And(p1,p2) ->
	  mkApp (force step_count l_I_And,
		 [|build_proof pops size p1;
		   build_proof pops size p2|])
      | E_And(i,p) ->
	  mkApp (force step_count l_E_And,
		 [|build_pos (decal i pops);
		   build_proof pops (size + 2) p|])
      | D_And(i,p) ->
	  mkApp (force step_count l_D_And,
		 [|build_pos (decal i pops);
		   build_proof pops (size + 1) p|])
      | I_Or_l(p) ->
	  mkApp (force step_count l_I_Or_l,
		 [|build_proof pops size p|])
      | I_Or_r(p) ->
	  mkApp (force step_count l_I_Or_r,
		 [|build_proof pops size p|])
      | E_Or(i,p1,p2) ->
	  mkApp (force step_count l_E_Or,
		 [|build_pos (decal i pops);
		   build_proof pops (size + 1) p1;
		   build_proof pops (size + 1) p2|])
      | D_Or(i,p) ->
	  mkApp (force step_count l_D_Or,
		 [|build_pos (decal i pops);
		   build_proof pops (size + 2) p|])
      | Pop(d,p) ->
	  build_proof (add_pop size d pops) size p

let build_env gamma=
  List.fold_right (fun (p,_) e ->
		     mkApp(force node_count l_push,[|mkProp;p;e|]))
    gamma.env (mkApp (force node_count l_empty,[|mkProp|]))

open Goptions

let verbose = ref false

let opt_verbose=
  {optsync=true;
   optdepr=false;
   optname="Rtauto Verbose";
   optkey=["Rtauto";"Verbose"];
   optread=(fun () -> !verbose);
   optwrite=(fun b -> verbose:=b)}

let _ = declare_bool_option opt_verbose

let check = ref false

let opt_check=
  {optsync=true;
   optdepr=false;
   optname="Rtauto Check";
   optkey=["Rtauto";"Check"];
   optread=(fun () -> !check);
   optwrite=(fun b -> check:=b)}

let _ = declare_bool_option opt_check

open Pp

let rtauto_tac gls=
  Coqlib.check_required_library ["Coq";"rtauto";"Rtauto"];
  let gamma={next=1;env=[]} in
  let gl=pf_concl gls in
  let _=
    if Retyping.get_sort_family_of
      (pf_env gls) (Tacmach.project gls) gl != InProp
    then errorlabstrm "rtauto" (Pp.str "goal should be in Prop") in
  let glf=make_form gamma gls gl in
  let hyps=make_hyps gamma gls [gl] (pf_hyps gls) in
  let formula=
    List.fold_left (fun gl (_,f)-> Arrow (f,gl)) glf hyps in
  let search_fun = match Tacinterp.get_debug() with
  | Tactic_debug.DebugOn 0 -> Search.debug_depth_first
  | _ -> Search.depth_first
  in
  let _ =
    begin
      reset_info ();
      if !verbose then
	msg_info (str "Starting proof-search ...");
    end in
  let search_start_time = System.get_time () in
  let prf =
    try project (search_fun (init_state [] formula))
    with Not_found ->
      errorlabstrm "rtauto" (Pp.str "rtauto couldn't find any proof") in
  let search_end_time = System.get_time () in
  let _ = if !verbose then
    begin
      msg_info (str "Proof tree found in " ++
	     System.fmt_time_difference search_start_time search_end_time);
      pp_info ();
      msg_info (str "Building proof term ... ")
    end in
  let build_start_time=System.get_time () in
  let _ = step_count := 0; node_count := 0 in
  let main = mkApp (force node_count l_Reflect,
		    [|build_env gamma;
		      build_form formula;
		      build_proof [] 0 prf|]) in
  let term=
    applist (main,List.rev_map (fun (id,_) -> mkVar id) hyps) in
  let build_end_time=System.get_time () in
  let _ = if !verbose then
    begin
      msg_info (str "Proof term built in " ++
	     System.fmt_time_difference build_start_time build_end_time ++
	     fnl () ++
	     str "Proof size : " ++ int !step_count ++
	     str " steps" ++ fnl () ++
	     str "Proof term size : " ++ int (!step_count+ !node_count) ++
	     str " nodes (constants)" ++ fnl () ++
	     str "Giving proof term to Coq ... ")
    end in
  let tac_start_time = System.get_time () in
  let result=
    if !check then
      Proofview.V82.of_tactic (Tactics.exact_check term) gls
    else
      Tactics.exact_no_check term gls in
  let tac_end_time = System.get_time () in
  let _ =
    if !check then msg_info (str "Proof term type-checking is on");
    if !verbose then
      msg_info (str "Internal tactic executed in " ++
	     System.fmt_time_difference tac_start_time tac_end_time) in
    result

