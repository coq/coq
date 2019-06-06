(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)


module Search = Explore.Make(Proof_search)

open Ltac_plugin
open CErrors
open Util
open Term
open Constr
open Context
open Proof_search
open Context.Named.Declaration

let force count lazc = incr count;Lazy.force lazc

let step_count = ref 0

let node_count = ref 0

let li_False = lazy (destInd (UnivGen.constr_of_monomorphic_global @@ Coqlib.lib_ref "core.False.type"))
let li_and   = lazy (destInd (UnivGen.constr_of_monomorphic_global @@ Coqlib.lib_ref "core.and.type"))
let li_or    = lazy (destInd (UnivGen.constr_of_monomorphic_global @@ Coqlib.lib_ref "core.or.type"))

let gen_constant n = lazy (UnivGen.constr_of_monomorphic_global (Coqlib.lib_ref n))

let l_xI = gen_constant "num.pos.xI"
let l_xO = gen_constant "num.pos.xO"
let l_xH = gen_constant "num.pos.xH"

let l_empty = gen_constant "plugins.rtauto.empty"
let l_push = gen_constant "plugins.rtauto.push"

let l_Reflect = gen_constant "plugins.rtauto.Reflect"

let l_Atom = gen_constant "plugins.rtauto.Atom"
let l_Arrow = gen_constant "plugins.rtauto.Arrow"
let l_Bot = gen_constant "plugins.rtauto.Bot"
let l_Conjunct = gen_constant "plugins.rtauto.Conjunct"
let l_Disjunct = gen_constant "plugins.rtauto.Disjunct"

let l_Ax = gen_constant "plugins.rtauto.Ax"
let l_I_Arrow = gen_constant "plugins.rtauto.I_Arrow"
let l_E_Arrow = gen_constant "plugins.rtauto.E_Arrow"
let l_D_Arrow = gen_constant "plugins.rtauto.D_Arrow"
let l_E_False = gen_constant "plugins.rtauto.E_False"
let l_I_And = gen_constant "plugins.rtauto.I_And"
let l_E_And = gen_constant "plugins.rtauto.E_And"
let l_D_And = gen_constant "plugins.rtauto.D_And"
let l_I_Or_l = gen_constant "plugins.rtauto.I_Or_l"
let l_I_Or_r = gen_constant "plugins.rtauto.I_Or_r"
let l_E_Or = gen_constant "plugins.rtauto.E_Or"
let l_D_Or = gen_constant "plugins.rtauto.D_Or"

let special_whd env sigma c =
  Reductionops.clos_whd_flags CClosure.all env sigma c

let special_nf env sigma c =
  Reductionops.clos_norm_flags CClosure.betaiotazeta env sigma c

type atom_env=
    {mutable next:int;
     mutable env:(constr*int) list}

let make_atom atom_env term=
  let term = EConstr.Unsafe.to_constr term in
  try
    let (_,i)=
      List.find (fun (t,_)-> Constr.equal term t) atom_env.env
    in Atom i
  with Not_found ->
    let i=atom_env.next in
      atom_env.env <- (term,i)::atom_env.env;
      atom_env.next<- i + 1;
      Atom i

let rec make_form env sigma atom_env term =
  let open EConstr in
  let open Vars in
  let normalize = special_nf env sigma in
  let cciterm = special_whd env sigma term  in
  match EConstr.kind sigma cciterm with
    Prod(_,a,b) ->
    if noccurn sigma 1 b &&
       Retyping.get_sort_family_of env sigma a == InProp
    then
      let fa = make_form env sigma atom_env a in
      let fb = make_form env sigma atom_env b in
      Arrow (fa,fb)
    else
      make_atom atom_env (normalize term)
  | Cast(a,_,_) ->
    make_form env sigma atom_env a
  | Ind (ind, _) ->
    if Names.eq_ind ind (fst (Lazy.force li_False)) then
      Bot
    else
      make_atom atom_env (normalize term)
  | App(hd,argv) when Int.equal (Array.length argv) 2 ->
    begin
      try
        let ind, _ = destInd sigma hd in
        if Names.eq_ind ind (fst (Lazy.force li_and)) then
          let fa = make_form env sigma atom_env argv.(0) in
          let fb = make_form env sigma atom_env argv.(1) in
          Conjunct (fa,fb)
        else if Names.eq_ind ind (fst (Lazy.force li_or)) then
          let fa = make_form env sigma atom_env argv.(0) in
          let fb = make_form env sigma atom_env argv.(1) in
          Disjunct (fa,fb)
        else make_atom atom_env (normalize term)
      with DestKO -> make_atom atom_env (normalize term)
    end
  | _ -> make_atom atom_env (normalize term)

let rec make_hyps env sigma atom_env lenv = function
    [] -> []
  | LocalDef (_,body,typ)::rest ->
    make_hyps env sigma atom_env (typ::body::lenv) rest
  | LocalAssum (id,typ)::rest ->
    let hrec=
      make_hyps env sigma atom_env (typ::lenv) rest in
    if List.exists (fun c -> Termops.local_occur_var Evd.empty (* FIXME *) id.binder_name c) lenv ||
       (Retyping.get_sort_family_of env sigma typ != InProp)
    then
      hrec
    else
      (id,make_form env sigma atom_env typ)::hrec

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
  {optdepr=false;
   optname="Rtauto Verbose";
   optkey=["Rtauto";"Verbose"];
   optread=(fun () -> !verbose);
   optwrite=(fun b -> verbose:=b)}

let () = declare_bool_option opt_verbose

let check = ref false

let opt_check=
  {optdepr=false;
   optname="Rtauto Check";
   optkey=["Rtauto";"Check"];
   optread=(fun () -> !check);
   optwrite=(fun b -> check:=b)}

let () = declare_bool_option opt_check

open Pp

let rtauto_tac =
  Proofview.Goal.enter begin fun gl ->
    let hyps = Proofview.Goal.hyps gl in
    let concl = Proofview.Goal.concl gl in
    let env = Proofview.Goal.env gl in
    let sigma = Proofview.Goal.sigma gl in
    Coqlib.check_required_library ["Coq";"rtauto";"Rtauto"];
    let gamma={next=1;env=[]} in
    let () =
      if Retyping.get_sort_family_of env sigma concl != InProp
      then user_err ~hdr:"rtauto" (Pp.str "goal should be in Prop") in
    let glf = make_form env sigma gamma concl in
    let hyps = make_hyps env sigma gamma [concl] hyps in
    let formula=
      List.fold_left (fun gl (_,f)-> Arrow (f,gl)) glf hyps in
    let search_fun = match Tacinterp.get_debug() with
      | Tactic_debug.DebugOn 0 -> Search.debug_depth_first
      | _ -> Search.depth_first
    in
    let () =
      begin
        reset_info ();
        if !verbose then
          Feedback.msg_info (str "Starting proof-search ...");
      end in
    let search_start_time = System.get_time () in
    let prf =
      try project (search_fun (init_state [] formula))
      with Not_found ->
        user_err ~hdr:"rtauto" (Pp.str "rtauto couldn't find any proof") in
    let search_end_time = System.get_time () in
    let () = if !verbose then
        begin
          Feedback.msg_info (str "Proof tree found in " ++
                             System.fmt_time_difference search_start_time search_end_time);
          pp_info ();
          Feedback.msg_info (str "Building proof term ... ")
        end in
    let build_start_time=System.get_time () in
    let () = step_count := 0; node_count := 0 in
    let main = mkApp (force node_count l_Reflect,
                      [|build_env gamma;
                        build_form formula;
                        build_proof [] 0 prf|]) in
    let term=
      applistc main (List.rev_map (fun (id,_) -> mkVar id.binder_name) hyps) in
    let build_end_time=System.get_time () in
    let () = if !verbose then
        begin
          Feedback.msg_info (str "Proof term built in " ++
                             System.fmt_time_difference build_start_time build_end_time ++
                             fnl () ++
                             str "Proof size : " ++ int !step_count ++
                             str " steps" ++ fnl () ++
                             str "Proof term size : " ++ int (!step_count+ !node_count) ++
                             str " nodes (constants)" ++ fnl () ++
                             str "Giving proof term to Coq ... ")
        end in
    let tac_start_time = System.get_time () in
    let term = EConstr.of_constr term in
    let result=
      if !check then
        Tactics.exact_check term
      else
        Tactics.exact_no_check term in
    let tac_end_time = System.get_time () in
    let () =
      if !check then Feedback.msg_info (str "Proof term type-checking is on");
      if !verbose then
        Feedback.msg_info (str "Internal tactic executed in " ++
                           System.fmt_time_difference tac_start_time tac_end_time) in
    result
  end
