(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Util
open Pp
open Evd

open Refiner
open Proof_type
open Proof_trees
open Tacmach
open Tacinterp
open Decl_expr
open Decl_mode
open Decl_interp
open Rawterm
open Names
open Declarations
open Tactics
open Tacticals
open Term
open Termops
open Reductionops
open Goptions

(* Strictness option *)

let get_its_info gls = get_info gls.it

let get_strictness,set_strictness = 
  let strictness = ref false in
    (fun () -> (!strictness)),(fun b -> strictness:=b)

let _ =
  declare_bool_option 
    { optsync  = true;
      optname  = "strict mode";
      optkey   = (SecondaryTable ("Strict","Proofs"));
      optread  = get_strictness;
      optwrite = set_strictness }

let tcl_change_info_gen info_gen = 
  (fun gls ->
  let gl =sig_it gls in  
    {it=[{gl with evar_extra=info_gen}];sigma=sig_sig gls}, 
  function 
      [pftree] ->
	{pftree with
	   goal=gl;
	   ref=Some (Prim Change_evars,[pftree])} 
    | _ -> anomaly "change_info : Wrong number of subtrees")

let tcl_change_info info gls =  tcl_change_info_gen (Some (pm_in info)) gls

let tcl_erase_info gls =  tcl_change_info_gen None gls

let special_whd gl=
  let infos=Closure.create_clos_infos Closure.betadeltaiota (pf_env gl) in
    (fun t -> Closure.whd_val infos (Closure.inject t))

let special_nf gl=
  let infos=Closure.create_clos_infos Closure.betaiotazeta (pf_env gl) in
    (fun t -> Closure.norm_val infos (Closure.inject t))

let is_good_inductive env ind =
  let mib,oib = Inductive.lookup_mind_specif env ind in
    oib.mind_nrealargs = 0 && not (Inductiveops.mis_is_recursive (ind,mib,oib))

let check_not_per pts =
  if not (Proof_trees.is_complete_proof (proof_of_pftreestate pts)) then
    match get_stack pts with
	Per (_,_,_,_)::_ -> 
	  error "You are inside a proof per cases/induction.\n\
Please \"suppose\" something or \"end\" it now."
      | _ -> ()

let get_thesis gls0 = 
 let info = get_its_info gls0 in  
    match info.pm_subgoals with
	[m,thesis] -> thesis
      | _ -> error "Thesis is split"

let mk_evd metalist gls =
  let evd0= create_evar_defs (sig_sig gls) in
  let add_one (meta,typ) evd = 
    meta_declare meta typ evd in
    List.fold_right add_one metalist evd0

let set_last cpl gls = 
  let info = get_its_info gls in
    tclTHEN 
      begin 
	match info.pm_last with 
	    Some (lid,false) when 
	      not (occur_id [] lid info.pm_partial_goal) -> 
		tclTRY (clear [lid])
	  | _ -> tclIDTAC
      end
      begin
	tcl_change_info 
	  {info with 
	    pm_last=Some cpl }
      end gls
	  
(* start a proof *)

let start_proof_tac gls=
  let gl=sig_it gls in
  let info={pm_last=None;
	    pm_partial_goal=mkMeta 1; 
	    pm_subgoals= [1,gl.evar_concl];
	    pm_stack=[]} in
    {it=[{gl with evar_extra=Some (pm_in info)}];sigma=sig_sig gls}, 
  function 
      [pftree] ->
	{pftree with
	   goal=gl;
	   ref=Some (Decl_proof true,[pftree])} 
    | _ -> anomaly "Dem : Wrong number of subtrees"

let go_to_proof_mode () = 
  Pfedit.mutate 
    (fun pts -> nth_unproven 1 (solve_pftreestate start_proof_tac pts))

(* closing gaps *)

let daimon_tac gls =
  set_daimon_flag ();
  ({it=[];sigma=sig_sig gls}, 
   function 
       [] ->
	 {open_subgoals=0;
	    goal=sig_it gls;
	    ref=Some (Daimon,[])} 
     | _ -> anomaly "Daimon: Wrong number of subtrees")
    
let daimon _ pftree =
  set_daimon_flag ();
  {pftree with
     open_subgoals=0;
     ref=Some (Daimon,[])}

let daimon_subtree = map_pftreestate (fun _ ->  frontier_mapi daimon )

(* marking closed blocks *)

let rec is_focussing_instr = function
    Pthus i | Pthen i | Phence i -> is_focussing_instr i
  | Pescape | Pper _ | Pclaim _ | Pfocus _ 
  | Psuppose _ | Pcase (_,_,_)  -> true
  | _ -> false

let mark_rule_as_done = function
    Decl_proof true -> Decl_proof false
  | Decl_proof false ->
      anomaly "already marked as done"
  | Nested(Proof_instr (lock_focus,instr),spfl) -> 
      if lock_focus then
	Nested(Proof_instr (false,instr),spfl)
      else
	anomaly "already marked as done"
  | _ -> anomaly "mark_rule_as_done"

let mark_proof_tree_as_done pt =
  match pt.ref with
      None -> anomaly "mark_proof_tree_as_done"
    | Some (r,spfl) -> 
	{pt with ref= Some (mark_rule_as_done r,spfl)}

let mark_as_done pts = 
  map_pftreestate 
    (fun _ -> mark_proof_tree_as_done) 
    (traverse 0 pts) 

(* post-instruction focus management *)

let goto_current_focus pts = up_until_matching_rule is_focussing_command pts

let goto_current_focus_or_top pts = 
  try 
    up_until_matching_rule is_focussing_command pts
  with Not_found -> top_of_tree pts

(* return *)

let close_tactic_mode pts =
    let pts1=  
      try goto_current_focus pts 
      with Not_found -> 
	error "\"return\" cannot be used outside of Declarative Proof Mode" in
    let pts2 = daimon_subtree pts1 in
    let pts3 = mark_as_done pts2 in 
      goto_current_focus pts3 
	  
let return_from_tactic_mode () = Pfedit.mutate close_tactic_mode

(* end proof/claim *)

let close_block bt pts =
  let stack =
    if Proof_trees.is_complete_proof (proof_of_pftreestate pts) then
      get_top_stack pts
    else
      get_stack pts in
    match bt,stack with
	B_claim, Claim::_ | B_focus, Focus_claim::_ | B_proof, [] -> 
	  daimon_subtree (goto_current_focus pts)
      | _, Claim::_ -> 
	  error "\"end claim\" expected" 
      | _, Focus_claim::_ -> 
	  error "\"end focus\" expected" 
      | _, [] ->
 	  error "\"end proof\" expected" 
      | _, (Per (et,_,_,_)::_|Suppose_case::Per (et,_,_,_)::_) ->
	  begin
	    match et with
		ET_Case_analysis -> error "\"end cases\" expected"
	      | ET_Induction ->  error "\"end induction\" expected"
	  end
      | _,_ -> anomaly "lonely suppose on stack"

(* utility for suppose / suppose it is *)

let close_previous_case pts = 
  if 
    Proof_trees.is_complete_proof (proof_of_pftreestate pts) 
  then
    match get_top_stack pts with
	Per (et,_,_,_) :: _ -> anomaly "Weird case occured ..."  
      | Suppose_case :: Per (et,_,_,_) :: _ -> 
	  goto_current_focus (mark_as_done pts)
      | _ -> error "Not inside a proof per cases or induction."   
  else
    match get_stack pts with
	Per (et,_,_,_) :: _ -> pts 
      | Suppose_case :: Per (et,_,_,_) :: _ ->
	  goto_current_focus (mark_as_done (daimon_subtree pts))
      | _ -> error "Not inside a proof per cases or induction."

(* Proof instructions *)

(* automation *)

let filter_hyps f gls =
  let filter_aux (id,_,_) = 
    if f id then 
      tclIDTAC
    else 
      tclTRY (clear [id])  in
    tclMAP filter_aux (Environ.named_context_of_val gls.it.evar_hyps) gls

let local_hyp_prefix = id_of_string "___"

let add_justification_hyps keep items gls =
  let add_aux c gls=
    match kind_of_term c with 
	Var id -> 
	  keep:=Idset.add id !keep;
	  tclIDTAC gls 
      | _ -> 
	  let id=pf_get_new_id local_hyp_prefix gls in 
	    keep:=Idset.add id !keep; 
	    letin_tac false (Names.Name id) c Tacexpr.nowhere gls in 
    tclMAP add_aux items gls   

let prepare_goal items gls =
  let tokeep = ref Idset.empty in
  let auxres = add_justification_hyps tokeep items gls in
   tclTHENLIST
     [ (fun _ -> auxres);
       filter_hyps (let keep = !tokeep in fun id -> Idset.mem id keep)] gls

let my_automation_tac = ref 
  (fun gls -> anomaly "No automation registered")

let register_automation_tac tac = my_automation_tac:= tac

let automation_tac gls = !my_automation_tac gls

let justification tac gls= 
    tclORELSE 
      (tclSOLVE [tclTHEN tac assumption]) 
      (fun gls -> 
	 if get_strictness () then 
	   error "insufficient justification" 
	 else
	   begin
	     msgnl (str "Warning: insufficient justification");  
	     daimon_tac gls
	   end) gls

let default_justification elems gls=
  justification (tclTHEN (prepare_goal elems) automation_tac) gls

(* code for have/then/thus/hence *)

type stackd_elt =
{se_meta:metavariable;
 se_type:types;
 se_last_meta:metavariable;
 se_meta_list:(metavariable*types) list;
 se_evd: evar_defs}

let rec replace_in_list m l = function
    [] -> raise Not_found
  | c::q -> if m=fst c then l@q else c::replace_in_list m l q

let enstack_subsubgoals env se stack gls=
  let hd,params = decompose_app (special_whd gls se.se_type) in
    match kind_of_term hd with
	Ind ind when is_good_inductive env ind ->
	  let mib,oib=
	    Inductive.lookup_mind_specif env ind in
          let gentypes=
            Inductive.arities_of_constructors ind (mib,oib) in
	  let process i gentyp = 
	    let constructor = mkConstruct(ind,succ i) 
	      (* constructors numbering*) in
	    let appterm = applist (constructor,params) in
	    let apptype = Term.prod_applist gentyp params in
	    let rc,_ = Reduction.dest_prod env apptype in
	    let rec meta_aux last lenv = function 
		[] -> (last,lenv,[])
	      | (nam,_,typ)::q ->
		  let nlast=succ last in
		  let (llast,holes,metas) =
		    meta_aux nlast (mkMeta nlast :: lenv) q in
		    (llast,holes,(nlast,special_nf gls (substl lenv typ))::metas) in
	    let (nlast,holes,nmetas) = 
		meta_aux se.se_last_meta [] (List.rev rc) in
	    let refiner = applist (appterm,List.rev holes) in
	    let evd = meta_assign se.se_meta refiner se.se_evd in
	    let ncreated = replace_in_list 
	      se.se_meta nmetas se.se_meta_list in
	    let evd0 = List.fold_left 
	      (fun evd (m,typ) -> meta_declare m typ evd) evd nmetas in  
	      List.iter (fun (m,typ) -> 
			   Stack.push 
			     {se_meta=m;
			      se_type=typ;
			      se_evd=evd0;
			      se_meta_list=ncreated;
			      se_last_meta=nlast} stack) (List.rev nmetas) 
	  in
	    Array.iteri process gentypes
      | _ -> ()

let find_subsubgoal env c ctyp skip evd metas submetas gls =
  let stack = Stack.create () in
  let max_meta = 
    let tmp = List.fold_left (fun a (m,_) -> max a m) 0 metas in
      List.fold_left (fun a (m,_) -> max a m) tmp submetas in
  let _ = 
    List.iter (fun (m,typ) -> 
		 Stack.push 
		   {se_meta=m;
		    se_type=typ;
		    se_last_meta=max_meta;
		    se_meta_list=metas;
		    se_evd=evd} stack) (List.rev metas) in
  let rec dfs n = 
    let se = Stack.pop stack in
      try 
	let unifier = 
	  Unification.w_unify true env Reduction.CUMUL 
	    ctyp se.se_type se.se_evd in
	  if n <= 0 then 
	    {se with 
	       se_evd=meta_assign se.se_meta c unifier;
	       se_meta_list=replace_in_list 
		se.se_meta submetas se.se_meta_list}
	  else
	      dfs (pred n)
      with _ -> 
	begin
	  enstack_subsubgoals env se stack gls;
	  dfs n
	end in
  let nse= try dfs skip with Stack.Empty -> raise Not_found in
    nse.se_meta_list,nse.se_evd

let rec nf_list evd = 
  function
      [] -> []  
    | (m,typ)::others -> 
	if meta_defined evd m then 
	    nf_list evd others
	else
	  (m,nf_meta evd typ)::nf_list evd others

let rec max_linear_context meta_one c =
  if !meta_one = None then
     if isMeta c then
       	begin
	  meta_one:= Some c;
          mkMeta 1
	end
     else
       try
	 map_constr (max_linear_context meta_one) c
       with Not_found -> 
	 begin
	   meta_one:= Some c;
           mkMeta 1
	 end
  else   
    if isMeta c then 
      raise Not_found
    else
      map_constr (max_linear_context meta_one) c

let thus_tac c ctyp submetas gls =  
  let info = get_its_info gls in
  let evd0 = mk_evd (info.pm_subgoals@submetas) gls in
  let list,evd = 
    try
      find_subsubgoal (pf_env gls) c ctyp 0 evd0 info.pm_subgoals submetas gls
    with Not_found -> 
      error "I could not relate this statement to the thesis" in
  let nflist = nf_list evd list in
  let nfgoal = nf_meta evd info.pm_partial_goal in
(*  let _ = msgnl (str "Partial goal : " ++ 
		   print_constr_env (pf_env gls) nfgoal) in *)
  let rgl = ref None in
  let refiner = max_linear_context rgl nfgoal in
    match !rgl with
	None -> exact_check refiner gls
      | Some pgl when not (isMeta refiner) ->
	  let ninfo={info with
		       pm_partial_goal = pgl;
		       pm_subgoals = nflist} in
	    tclTHEN
	      (Tactics.refine refiner)
	      (tcl_change_info ninfo) 
	      gls
      | _ -> 
	  let ninfo={info with
		       pm_partial_goal = nfgoal;
		       pm_subgoals = nflist} in
	    tcl_change_info ninfo gls

let anon_id_base = id_of_string "__" 


let mk_stat_or_thesis info = function  
    This c -> c
  | Thesis (For _ ) -> 
      error "\"thesis for ...\" is not applicable here" 
  | Thesis (Sub n) ->
      begin
	try List.assoc n info.pm_subgoals 
	with Not_found -> error "No such part in thesis."
      end
  | Thesis Plain ->   
      match info.pm_subgoals with
	  [_,c] -> c
	| _ -> error 
	    "\"thesis\" is split, please specify which part you refer to."

let just_tac _then cut info gls0 =
  let items_tac gls =
    match cut.cut_by with
	None -> tclIDTAC gls
      | Some items -> 
	  let items_ = 
	    if _then then
	      match info.pm_last with
		  None -> error "no previous statement to use"
		| Some (id,_) -> (mkVar id)::items
	    else items
	  in prepare_goal items_ gls in
  let method_tac gls = 
    match cut.cut_using with
        None ->	
	  automation_tac gls
      | Some tac -> 
	  (Tacinterp.eval_tactic tac) gls in
    justification (tclTHEN items_tac method_tac) gls0
			
let instr_cut mkstat _thus _then cut gls0 = 
  let info = get_its_info gls0 in 
  let stat = cut.cut_stat in
  let (c_id,_) as cpl = match stat.st_label with 
      Anonymous -> 
	pf_get_new_id (id_of_string "_fact") gls0,false 
    | Name id -> id,true in
  let c_stat = mkstat info stat.st_it in
  let thus_tac gls= 
    if _thus then 
      thus_tac (mkVar c_id) c_stat [] gls
    else tclIDTAC gls in
    tclTHENS (internal_cut c_id c_stat) 
      [tclTHEN tcl_erase_info (just_tac _then cut info);
       tclTHEN (set_last cpl) thus_tac] gls0



(* iterated equality *)
let _eq = Libnames.constr_of_reference (Coqlib.glob_eq)

let decompose_eq id gls =
  let typ = pf_get_hyp_typ gls id in
  let whd =  (special_whd gls typ) in
    match kind_of_term whd with
	App (f,args)->
	  if eq_constr f _eq && (Array.length args)=3 
	  then (args.(0),
		args.(1), 
		args.(2)) 
	  else error "previous step is not an equality"
      | _ -> error "previous step is not an equality"
	  
let instr_rew _thus rew_side cut gls0 = 
  let info = get_its_info gls0 in
  let last_id = 	    
    match info.pm_last with
	None -> error "no previous equality"
      | Some (id,_) -> id in
  let typ,lhs,rhs = decompose_eq last_id gls0 in  
  let items_tac gls =
    match cut.cut_by with
	None -> tclIDTAC gls
      | Some items -> prepare_goal items gls in
  let method_tac gls = 
    match cut.cut_using with
        None ->	
	  automation_tac gls
      | Some tac -> 
	  (Tacinterp.eval_tactic tac) gls in
  let just_tac gls =
    justification (tclTHEN items_tac method_tac) gls in
  let (c_id,_) as cpl = match cut.cut_stat.st_label with 
      Anonymous -> 
	pf_get_new_id (id_of_string "_eq") gls0,false 
    | Name id -> id,true in
  let thus_tac new_eq gls= 
    if _thus then 
      thus_tac (mkVar c_id) new_eq [] gls
    else tclIDTAC gls in
    match rew_side with 
	Lhs ->
	  let new_eq = mkApp(_eq,[|typ;cut.cut_stat.st_it;rhs|]) in
	    tclTHENS (internal_cut c_id new_eq) 
	      [tclTHEN tcl_erase_info 
		 (tclTHENS (transitivity lhs) 
		    [just_tac;exact_check (mkVar last_id)]);
	       tclTHEN (set_last cpl) (thus_tac new_eq)] gls0
      | Rhs ->
	  let new_eq = mkApp(_eq,[|typ;lhs;cut.cut_stat.st_it|]) in
	    tclTHENS (internal_cut c_id new_eq) 
	      [tclTHEN tcl_erase_info 
		 (tclTHENS (transitivity rhs) 
		    [exact_check (mkVar last_id);just_tac]);
	       tclTHEN (set_last cpl) (thus_tac new_eq)] gls0
	      


(* tactics for claim/focus *)

let instr_claim _thus st gls0 = 
  let info = get_its_info gls0 in  
  let (id,_) as cpl = match st.st_label with 
      Anonymous -> pf_get_new_id (id_of_string "_claim") gls0,false 
    | Name id -> id,true in
  let thus_tac gls= 
    if _thus then 
      thus_tac (mkVar id) st.st_it [] gls
    else tclIDTAC gls in
  let ninfo1 = {info with 
		  pm_stack=
      (if _thus then Focus_claim else Claim)::info.pm_stack;
		  pm_partial_goal=mkMeta 1;
	          pm_subgoals = [1,st.st_it]} in
    tclTHENS (internal_cut id st.st_it) 
      [tcl_change_info ninfo1;
       tclTHEN (set_last cpl) thus_tac] gls0

(* tactics for assume *)

let reset_concl gls =
  let info = get_its_info gls in
    tcl_change_info 
      {info with 
	 pm_partial_goal=mkMeta 1;
	 pm_subgoals= [1,gls.it.evar_concl]} gls


let intro_pm id gls=
  let info = get_its_info gls in
    match info.pm_subgoals with
	[(_,typ)] -> 
	  tclTHEN (intro_mustbe_force id) reset_concl gls
      | _ -> error "Goal is split"

let push_intro_tac coerce nam gls = 
      let (hid,_) as cpl =
	match nam with 
	    Anonymous -> pf_get_new_id (id_of_string "_hyp") gls,false 
	  | Name id -> id,true in
	tclTHENLIST 
	  [intro_pm hid;
	   coerce hid;
	   set_last cpl]
	  gls 

let assume_tac hyps gls = 
  List.fold_right 
    (fun (Hvar st | Hprop st) -> 
       tclTHEN 
	 (push_intro_tac 
	    (fun id -> 
	       convert_hyp (id,None,st.st_it)) st.st_label))
	 hyps tclIDTAC gls 

let assume_hyps_or_theses hyps gls = 
  List.fold_right 
    (function 
	 (Hvar {st_label=nam;st_it=c} | Hprop {st_label=nam;st_it=This c}) -> 
	   tclTHEN 
	     (push_intro_tac 
		(fun id -> 
		   convert_hyp (id,None,c)) nam)
       | Hprop {st_label=nam;st_it=Thesis (tk)} -> 
	   tclTHEN 
	     (push_intro_tac 
		(fun id -> tclIDTAC) nam))
    hyps tclIDTAC gls 

let assume_st hyps gls = 
  List.fold_right 
    (fun st -> 
       tclTHEN 
	 (push_intro_tac 
	    (fun id -> convert_hyp (id,None,st.st_it)) st.st_label))
	 hyps tclIDTAC gls 

let assume_st_letin hyps gls = 
  List.fold_right 
    (fun st -> 
       tclTHEN 
	 (push_intro_tac 
	    (fun id -> 
	       convert_hyp (id,Some (fst st.st_it),snd st.st_it)) st.st_label))
	 hyps tclIDTAC gls 

(* suffices *)

let free_meta info = 
  let max_next (i,_) j  = if j <= i then succ i else j in
  List.fold_right max_next info.pm_subgoals 1

let rec metas_from n hyps = 
  match hyps with
      _ :: q -> n :: metas_from (succ n) q
    | [] -> []
 
let rec build_product args body =
  match args with 
      (Hprop st| Hvar st )::rest -> 
	let pprod= lift 1 (build_product rest body) in
	let lbody =
	  match st.st_label with
	      Anonymous -> pprod
	    | Name id -> subst_term (mkVar id) pprod in
	  mkProd (st.st_label, st.st_it, lbody)
    | [] -> body 

let rec build_applist prod = function
    [] -> [],prod
  | n::q -> 
      let (_,typ,_) = destProd prod in
      let ctx,head = build_applist (Term.prod_applist prod [mkMeta n]) q in
	(n,typ)::ctx,head

let instr_suffices _then cut gls0 = 
  let info = get_its_info gls0 in 
  let c_id = pf_get_new_id (id_of_string "_cofact") gls0 in 
  let ctx,hd = cut.cut_stat in
  let c_stat = build_product ctx (mk_stat_or_thesis info hd) in
  let metas = metas_from (free_meta info) ctx in
  let c_ctx,c_head = build_applist c_stat metas in
  let c_term = applist (mkVar c_id,List.map mkMeta metas) in  
  let thus_tac gls= 
    thus_tac c_term c_head c_ctx gls in
   tclTHENS (internal_cut c_id c_stat) 
     [tclTHENLIST 
	 [ tcl_change_info 
	     {info with 
	       pm_partial_goal=mkMeta 1;
	       pm_subgoals=[1,c_stat]};
	   assume_tac ctx;   
	   tcl_erase_info;
	   just_tac _then cut info];
      tclTHEN (set_last (c_id,false)) thus_tac] gls0

(* tactics for consider/given *)

let update_goal_info gls =
  let info = get_its_info gls in
    match info.pm_subgoals with
	[m,_] -> tcl_change_info {info with pm_subgoals =[m,pf_concl gls]} gls
      | _ -> error "thesis is split"

let conjunction_arity id gls =
  let typ = pf_get_hyp_typ gls id  in
  let hd,params = decompose_app (special_whd gls typ) in
  let env =pf_env gls in 
    match kind_of_term hd with
	Ind ind when is_good_inductive env ind ->
	  let mib,oib=
	    Inductive.lookup_mind_specif env ind in
          let gentypes=
            Inductive.arities_of_constructors ind (mib,oib) in
	  let _ = if Array.length gentypes <> 1 then raise Not_found in
	  let apptype = Term.prod_applist gentypes.(0) params in
	  let rc,_ = Reduction.dest_prod env apptype in
	    List.length rc
      | _ -> raise Not_found

let rec intron_then n ids ltac gls = 
  if n<=0 then 
    tclTHEN
    (fun gls -> 
       if List.exists (fun id -> occur_id [] id (pf_concl gls)) ids  then 
	 update_goal_info gls
       else 
	 tclIDTAC gls)
    (ltac ids)
      gls
  else  
    let id = pf_get_new_id (id_of_string "_tmp") gls in 
      tclTHEN 
	(intro_mustbe_force id) 
	(intron_then (pred n) (id::ids) ltac) gls 

let pm_rename_hyp id hid gls =
  if occur_id [] id (pf_concl gls) then
    tclTHEN (rename_hyp id hid) update_goal_info gls
  else
    rename_hyp id hid gls 

let rec consider_match may_intro introduced available expected gls =
  match available,expected with 
      [],[] ->
	  set_last (List.hd introduced) gls
    | _,[] -> error "last statements do not match a complete hypothesis" 
	(* should tell which ones *)
    | [],hyps -> 
	if may_intro then
	  begin
 	    let id = pf_get_new_id (id_of_string "_tmp") gls in
	      tclIFTHENELSE 
		(intro_pm id)
		(consider_match true [] [id] hyps) 
		(fun _ -> 
		   error "not enough sub-hypotheses to match statements")
		gls 
          end 
	else
	  error "not enough sub-hypotheses to match statements" 
	    (* should tell which ones *)
    | id::rest_ids,(Hvar st | Hprop st)::rest ->
	tclIFTHENELSE (convert_hyp (id,None,st.st_it))
	  begin
	    match st.st_label with 
		Anonymous -> 
		  consider_match may_intro ((id,false)::introduced) rest_ids rest
	      | Name hid -> 
		  tclTHENLIST 
		    [pm_rename_hyp id hid;
		     consider_match may_intro ((hid,true)::introduced) rest_ids rest]
	  end
	  begin
	    (fun gls -> 
	       let nhyps =
		 try conjunction_arity id gls with 
		     Not_found -> error "matching hypothesis not found" in 
		 tclTHENLIST 
		   [general_case_analysis (mkVar id,NoBindings);
		    intron_then nhyps []
		      (fun l -> consider_match may_intro introduced 
			 (List.rev_append l rest_ids) expected)] gls)
	  end
	  gls
	  
let consider_tac c hyps gls =
  match kind_of_term (strip_outer_cast c) with
      Var id ->
	consider_match false [] [id] hyps gls 
    | _ -> 
	let id = pf_get_new_id (id_of_string "_tmp") gls in
	tclTHEN 
	  (forward None (Genarg.IntroIdentifier id) c)
 	  (consider_match false [] [id] hyps) gls 
	  

let given_tac hyps gls =
  consider_match true [] [] hyps gls

(* tactics for take *)

let rec take_tac wits gls =
  match wits with
      [] -> tclIDTAC gls
    | wit::rest ->  
	let typ = pf_type_of gls wit in  
	  tclTHEN (thus_tac wit typ []) (take_tac rest)  gls


(* tactics for define *)

let rec build_function args body =
  match args with 
      st::rest -> 
	let pfun= lift 1 (build_function rest body) in
	let id = match st.st_label with
	    Anonymous -> assert false
	  | Name id -> id in
	  mkLambda (Name id, st.st_it, subst_term (mkVar id) pfun)
    | [] -> body 

let define_tac id args body gls =
  let t = build_function args body in
    letin_tac true (Name id) t Tacexpr.nowhere gls

(* tactics for reconsider *)

let cast_tac id_or_thesis typ gls = 
  let info = get_its_info gls in
  match id_or_thesis with
      This id ->
	let (_,body,_) = pf_get_hyp gls id in
	  convert_hyp (id,body,typ) gls
    | Thesis (For _ ) -> 
	error "\"thesis for ...\" is not applicable here" 
    | Thesis (Sub n) ->
	begin
	  let old_typ = 
	    try List.assoc n info.pm_subgoals 
	    with Not_found -> error "No such part in thesis." in
	  if is_conv_leq (pf_env gls) (sig_sig gls) typ old_typ then
	    let new_sg = List.merge  
	      (fun (n,_) (p,_) -> Pervasives.compare n p) 
	      [n,typ] (List.remove_assoc n info.pm_subgoals) in
	      tcl_change_info {info with pm_subgoals=new_sg} gls
	  else 
	    error "not convertible"
	end
    | Thesis Plain ->   
	match info.pm_subgoals with 
	    [m,c] -> 
	      tclTHEN 
		(convert_concl typ DEFAULTcast) 
	        (tcl_change_info {info with pm_subgoals= [m,typ]}) gls
	  | _ -> error 
	      "\"thesis\" is split, please specify which part you refer to."
  
      
(* per cases *)

let start_tree env ind = 
  let constrs = (snd (Inductive.lookup_mind_specif env ind)).mind_consnames in
    Split (Idset.empty,ind,Array.map (fun _ -> None) constrs)

let build_per_info etype casee gls = 
  let concl=get_thesis gls in
  let env=pf_env gls in
  let ctyp=pf_type_of gls casee in
  let is_dep = dependent casee concl in 
  let hd,args = decompose_app (special_whd gls ctyp) in
  let ind = 
    try
      destInd hd 
    with _ -> 
      error "Case analysis must be done on an inductive object" in
  let nparams =
    let mind = fst (Global.lookup_inductive ind) in
     match etype with
	 ET_Induction -> mind.mind_nparams_rec
       | _ -> mind.mind_nparams in
  let params,real_args = list_chop nparams args in
  let abstract_obj c body = 
    let typ=pf_type_of gls c in 
      lambda_create env (typ,subst_term c body) in
  let pred= List.fold_right abstract_obj    
    real_args (lambda_create env (ctyp,subst_term casee concl)) in
    is_dep,
  {per_casee=casee;
   per_ctype=ctyp;
   per_ind=ind;
   per_pred=pred;
   per_args=real_args;
   per_params=params;
   per_nparams=nparams}

let per_tac etype casee gls=
  let env=pf_env gls in
  let info = get_its_info gls in
    match casee with
	Real c ->
	  let is_dep,per_info = build_per_info etype c gls in
	  let ek = 
	    if is_dep then
	      EK_dep (start_tree env per_info.per_ind)
	    else EK_unknown in
	    tcl_change_info 
	      {info with 
		 pm_stack=
		  Per(etype,per_info,ek,[])::info.pm_stack} gls
      | Virtual cut ->
	  assert (cut.cut_stat.st_label=Anonymous);
	  let id = pf_get_new_id (id_of_string "_matched") gls in
	  let c = mkVar id in
	  let modified_cut = 
	    {cut with cut_stat={cut.cut_stat with st_label=Name id}} in
	    tclTHEN 
	      (instr_cut (fun _ c -> c) false false modified_cut)
	      (fun gls0 ->
		 let is_dep,per_info = build_per_info etype c gls0 in
		   assert (not is_dep);
		   tcl_change_info 
		     {info with pm_stack=
			 Per(etype,per_info,EK_unknown,[])::info.pm_stack} gls0)
	      gls

(* suppose *)

let register_nodep_subcase id= function
    Per(et,pi,ek,clauses)::s ->
      begin
	match ek with
	    EK_unknown -> clauses,Per(et,pi,EK_nodep,id::clauses)::s
	  | EK_nodep -> clauses,Per(et,pi,EK_nodep,id::clauses)::s
	  | EK_dep _ -> error "Do not mix \"suppose\" with \"suppose it is\"."
      end
  | _ -> anomaly "wrong stack state"

let suppose_tac hyps gls0 = 
  let info = get_its_info gls0 in
  let thesis = get_thesis gls0 in
  let id = pf_get_new_id (id_of_string "_subcase") gls0 in
  let clause = build_product hyps thesis in
  let ninfo1 = {info with 
		  pm_stack=Suppose_case::info.pm_stack;
		  pm_partial_goal=mkMeta 1;
		  pm_subgoals = [1,clause]} in
  let old_clauses,stack = register_nodep_subcase id info.pm_stack in
  let ninfo2 = {info with 
		  pm_stack=stack} in
    tclTHENS (internal_cut id clause) 
      [tclTHENLIST [tcl_change_info ninfo1;
		    assume_tac hyps;
		    clear old_clauses];
       tcl_change_info ninfo2] gls0

(* suppose it is ... *) 

(* pattern matching compiling *)

let rec nb_prod_after n c=
  match kind_of_term c with
    | Prod (_,_,b) ->if n>0 then nb_prod_after (n-1) b else 
	1+(nb_prod_after 0 b)
    | _ -> 0

let constructor_arities env ind =
  let nparams = (fst (Global.lookup_inductive ind)).mind_nparams in
  let constr_types = Inductiveops.arities_of_constructors env ind in 
  let hyp = nb_prod_after nparams in	
    Array.map hyp constr_types

let rec n_push rest ids n = 
  if n<=0 then Pop rest else Push (ids,n_push rest ids (pred n)) 

let explode_branches ids env ind rest=
  Array.map (fun n -> Some (Idset.empty,n_push rest ids n)) (constructor_arities env ind)

let rec tree_of_pats env ((id,_) as cpl) pats =
  match pats with 
      [] -> End_of_branch cpl
    | args::stack ->
	match args with
	    [] -> Pop (tree_of_pats env cpl stack)
	  | patt :: rest_args ->
	      match patt with
		  PatVar (_,v) -> 
		    Push (Idset.singleton id,
			  tree_of_pats env cpl (rest_args::stack))
		|  PatCstr (_,(ind,cnum),args,nam) ->
		     let _,mind = Inductive.lookup_mind_specif env ind in
		     let br= Array.map (fun _ -> None) mind.mind_consnames in
		       br.(pred cnum) <- 
			 Some (Idset.singleton id,
			       tree_of_pats env cpl (args::rest_args::stack));
		       Split(Idset.empty,ind,br)

let rec add_branch env ((id,_) as cpl) pats tree=
  match pats with 
      [] -> 
	begin
	  match tree with
	      End_of_branch cpl0 -> End_of_branch cpl0 
		(* this ensures precedence *) 
	    | _ -> anomaly "tree is expected to end here"
	end
    | args::stack ->
	match args with 
	    [] ->
	      begin
		match tree with 
		    Pop t -> Pop (add_branch env cpl stack t)
		  | _ -> anomaly "we should pop here" 
	      end
	  | patt :: rest_args ->
	      match patt with
		  PatVar (_,v) ->
		    begin
		      match tree with 
			  Push (ids,t) -> 
			    Push (Idset.add id ids,
				  add_branch env cpl (rest_args::stack) t)
			| Split (ids,ind,br) ->
			    Split (Idset.add id ids,
				   ind,array_map2 
				     (append_branch env cpl 1 
					(rest_args::stack)) 
				     (constructor_arities env ind) br)
			| _ -> anomaly "No pop/stop expected here"  
		    end
		| PatCstr (_,(ind,cnum),args,nam) ->
		    match tree with
			Push (ids,t) ->
			  let br = explode_branches ids env ind t in
			  let _ =
			    br.(pred cnum)<- 
			      option_map
			      (fun (ids,tree) -> 
				 Idset.add id ids,
				 add_branch env cpl 
				   (args::rest_args::stack) tree) 
			      br.(pred cnum) in
			    Split (ids,ind,br)
		      | Split (ids,ind0,br0) ->
			  if (ind <> ind0) then error
			    (* this can happen with coercions *)
	                      "Case pattern belongs to wrong inductive type";
			  let br=Array.copy br0 in
			  let ca = constructor_arities env ind in
			  let _= br.(pred cnum)<-
			    append_branch env cpl 0 (args::rest_args::stack) 
			    ca.(pred cnum) br.(pred cnum) in 
			    Split (ids,ind,br)
		      | _ -> anomaly "No pop/stop expected here"
and append_branch env ((id,_) as cpl) depth pats nargs = function
    Some (ids,tree) -> 
      Some (Idset.add id ids,append_tree env cpl depth pats tree)
  | None ->
      Some (* (n_push (tree_of_pats env cpl pats) 
	      (Idset.singleton id) nargs) *)
	   (Idset.singleton id,tree_of_pats env cpl pats)
and append_tree env ((id,_) as cpl) depth pats tree =
  if depth<=0 then add_branch env cpl pats tree
  else match tree with
      Pop t -> Pop (append_tree env cpl (pred depth) pats t)
    | Push (ids,t) -> Push (Idset.add id ids,
				   append_tree env cpl depth pats t)
    | End_of_branch _ -> anomaly "Premature end of branch"
    | Split (ids,ind,branches) -> 
	Split (Idset.add id ids,ind,
	       array_map2 
		 (append_branch env cpl (succ depth) pats) 
		 (constructor_arities env ind)
		 branches)

(* suppose it is *)

let rec st_assoc id = function
    [] -> raise Not_found
  | st::_ when st.st_label = id  -> st.st_it
  | _ :: rest -> st_assoc id rest

let thesis_for obj typ per_info env=
  let rc,hd1=decompose_prod typ in
  let cind,all_args=decompose_app typ in
  let ind = destInd cind in
  let _ = if ind <> per_info.per_ind then
    errorlabstrm "thesis_for" 
      ((Printer.pr_constr_env env obj) ++ spc () ++ 
	 str "cannot give an induction hypothesis (wrong inductive type)") in  
  let params,args = list_chop per_info.per_nparams all_args in
  let _ = if not (List.for_all2 eq_constr params per_info.per_params) then
    errorlabstrm "thesis_for" 
      ((Printer.pr_constr_env env obj) ++ spc () ++ 
	 str "cannot give an induction hypothesis (wrong parameters)") in
  let hd2 = (applist ((lift (List.length rc) per_info.per_pred),args@[obj])) in
    compose_prod rc (whd_beta hd2)

let rec build_product_dep pat_info per_info args body gls =
  match args with 
      (Hprop {st_label=nam;st_it=This c} 
      | Hvar {st_label=nam;st_it=c})::rest -> 
	let pprod= 
	  lift 1 (build_product_dep pat_info per_info rest body gls) in
	let lbody =
	  match nam with
	      Anonymous -> body
	    | Name id -> subst_var id pprod in
	  mkProd (nam,c,lbody)
    | Hprop ({st_it=Thesis tk} as st)::rest ->
	let pprod= 
	  lift 1 (build_product_dep pat_info per_info rest body gls) in
	let lbody =
	  match st.st_label with
	      Anonymous -> body
	    | Name id -> subst_var id pprod in
	let ptyp =
	  match tk with
	      For id ->
		let obj = mkVar id in
		let typ = 
		  try st_assoc (Name id) pat_info.pat_vars 
		  with Not_found -> 
		    snd (st_assoc (Name id) pat_info.pat_aliases) in
		  thesis_for obj typ per_info (pf_env gls)
	    | Plain -> get_thesis gls 
	    | Sub n -> anomaly "Subthesis in cases" in
	  mkProd (st.st_label,ptyp,lbody)
    | [] -> body 

let build_dep_clause params pat_info per_info hyps gls =
  let concl=
    thesis_for pat_info.pat_constr pat_info.pat_typ per_info (pf_env gls) in
  let open_clause =
    build_product_dep pat_info per_info hyps concl gls in
  let prod_one st body =
    match st.st_label with
	Anonymous -> mkProd(Anonymous,st.st_it,lift 1 body)
      | Name id -> mkNamedProd id st.st_it (lift 1 body) in
  let let_one_in st body =
    match st.st_label with
	Anonymous -> mkLetIn(Anonymous,fst st.st_it,snd st.st_it,lift 1 body)
      | Name id -> 
	  mkNamedLetIn id (fst st.st_it) (snd st.st_it) (lift 1 body) in
  let aliased_clause = 
    List.fold_right let_one_in pat_info.pat_aliases open_clause in
    List.fold_right prod_one (params@pat_info.pat_vars) aliased_clause

let rec register_dep_subcase id env per_info pat = function
    EK_nodep -> error  "Only \"suppose it is\" can be used here."
  | EK_unknown -> 
      register_dep_subcase id env per_info pat
	(EK_dep (start_tree env per_info.per_ind))
  | EK_dep tree -> EK_dep (add_branch env id [[pat]] tree)
  
let case_tac params pat_info hyps gls0 =
  let info = get_its_info gls0 in
  let id = pf_get_new_id (id_of_string "_subcase") gls0 in
  let et,per_info,ek,old_clauses,rest =
    match info.pm_stack with
	Per (et,pi,ek,old_clauses)::rest -> (et,pi,ek,old_clauses,rest) 
      | _ -> anomaly "wrong place for cases" in
  let clause = build_dep_clause params pat_info per_info hyps gls0 in
  let ninfo1 = {info with 
		  pm_stack=Suppose_case::info.pm_stack;
		  pm_partial_goal=mkMeta 1;
		  pm_subgoals = [1,clause]} in
  let nek = 
    register_dep_subcase (id,List.length hyps) (pf_env gls0) per_info 
      pat_info.pat_pat ek in  
  let ninfo2 = {info with 
		  pm_stack=Per(et,per_info,nek,id::old_clauses)::rest} in
    tclTHENS (internal_cut id clause) 
      [tclTHENLIST 
	 [tcl_change_info ninfo1; 
	  assume_st (params@pat_info.pat_vars);
	  assume_st_letin pat_info.pat_aliases;
	  assume_hyps_or_theses hyps;
	  clear old_clauses];
       tcl_change_info ninfo2] gls0

(* end cases *)

type instance_stack =
    (constr option*bool*(constr list) list) list

let initial_instance_stack ids =
  List.map (fun id -> id,[None,false,[]]) ids

let push_one_arg arg = function 
    [] -> anomaly "impossible"
  | (head,is_rec,args) :: ctx -> 
      ((head,is_rec,(arg::args)) :: ctx)

let push_arg arg stacks =
  List.map (fun (id,stack) -> (id,push_one_arg arg stack)) stacks
  

let push_one_head c is_rec ids (id,stack) = 
  let head = if Idset.mem id ids then Some c else None in
    id,(head,is_rec,[]) :: stack

let push_head c is_rec ids stacks =
  List.map (push_one_head c is_rec ids) stacks

let pop_one rec_flag (id,stack) =  
  let nstack=
    match stack with
	[] -> anomaly "impossible"
      | [c] as l -> l
      | (Some head,is_rec,args)::(head0,is_rec0,args0)::ctx ->
	  let arg = applist (head,(List.rev args)) in
	    rec_flag:= !rec_flag || is_rec;
	    (head0,is_rec0,(arg::args0))::ctx
     | (None,is_rec,args)::(head0,is_rec0,args0)::ctx ->
	 rec_flag:= !rec_flag || is_rec;
	 (head0,is_rec0,(args@args0))::ctx
  in id,nstack

let pop_stacks stacks =
  let rec_flag= ref false in 
  let nstacks = List.map (pop_one rec_flag) stacks in
    !rec_flag , nstacks

let patvar_base = id_of_string "__"

let test_fun (str:string) = ()

let hrec_for obj_id fix_id per_info gls=
  let obj=mkVar obj_id in
  let typ=pf_get_hyp_typ gls obj_id in
  let rc,hd1=decompose_prod typ in
  let cind,all_args=decompose_app typ in
    match kind_of_term cind with
	Ind ind when ind=per_info.per_ind ->
	  let params,args= list_chop per_info.per_nparams all_args in 
	    if try 
	      (List.for_all2 eq_constr params per_info.per_params)
	    with Invalid_argument _ -> false then
	      let hd2 = applist (mkVar fix_id,args@[obj]) in
		Some (compose_lam rc (whd_beta hd2))
	    else None
      | _ -> None


(* custom elim performs the case analysis of hypothesis id from the local 
context, 

- generalizing hypotheses below id
- computing the elimination predicate (abstract inductive predicate) 
- build case analysis term 
- generalize rec_calls (use wf_paths)
- vector of introduced identifiers per branch 

match id in t return p with
 C1 ... => ?1 
|C2 ... => ?2
...
end*)


    






let rec execute_cases at_top fix_name per_info kont0 stacks tree gls = 
	      match tree with
      Pop t ->  
	let is_rec,nstacks =  pop_stacks stacks in
	  if is_rec then
	    let _ = test_fun "is_rec=true" in
	     let c_id = pf_get_new_id (id_of_string "_hrec") gls in
	       tclTHEN 
		 (intro_mustbe_force c_id)
		 (execute_cases false fix_name per_info kont0 nstacks t) gls
	  else
	    execute_cases false fix_name per_info kont0 nstacks t gls
    | Push (_,t) -> 
	let id = pf_get_new_id patvar_base gls in
	let nstacks = push_arg (mkVar id) stacks in
	let kont = execute_cases false fix_name per_info kont0 nstacks t in
	  tclTHEN
	    (intro_mustbe_force id)
	    begin
	      match fix_name with
		  Anonymous -> kont
		| Name fix_id ->  
		    (fun gls -> 
		       if at_top then
			 kont gls
		       else
			 match hrec_for id fix_id per_info gls with
			     None -> kont gls
			   | Some c_obj ->
			       let c_id = 
				 pf_get_new_id (id_of_string "_hrec") gls in
				 tclTHENLIST 
				   [generalize [c_obj];
				    intro_mustbe_force c_id;
				    kont] gls)
	    end gls
    | Split(ids,ind,br) ->
	let (_,typ,_)= 
	  try destProd (pf_concl gls) with Invalid_argument _ ->
  	    anomaly "Sub-object not found." in
	let hd,args=decompose_app (special_whd gls typ) in
	  if try ind <> destInd hd with Invalid_argument _ -> true then
	      (* argument of an inductive family : intro + discard *)
	      tclTHEN intro
  		(execute_cases at_top fix_name per_info kont0 stacks tree) gls
	    else
	      begin
		let nparams = (fst (Global.lookup_inductive ind)).mind_nparams in
		let params = list_firstn nparams args in
		let constr i =applist (mkConstruct(ind,succ i),params) in
		let next_tac is_rec i = function
		    Some (sub_ids,tree) ->
		      let br_stacks =
			List.filter (fun (id,_) -> Idset.mem id sub_ids) stacks in
		      let p_stacks = 
			push_head (constr i) is_rec ids br_stacks in
			execute_cases false fix_name per_info kont0 p_stacks tree 
		  | None -> 
		      msgnl (str "Warning : missing case");
		      kont0 (mkMeta 1) 
		in
		let id = pf_get_new_id patvar_base gls in
		let kont is_rec = 			
		  tclTHENSV
		    (general_case_analysis (mkVar id,NoBindings))
		    (Array.mapi (next_tac is_rec) br) in
		  tclTHEN 
		    (intro_mustbe_force id)
		    begin
		      match fix_name with
			  Anonymous -> kont false
			| Name fix_id ->  
			    (fun gls -> 
			      if at_top then
				kont false gls
			    else
				match hrec_for id fix_id per_info gls with
				    None -> kont false gls
				  | Some c_obj ->
				      tclTHENLIST 
					[generalize [c_obj];
					 kont true] gls)
		    end gls
	      end
    | End_of_branch (id,nhyps) -> 
	match List.assoc id stacks with
	    [None,_,args] -> 
	      let metas = list_tabulate (fun n -> mkMeta (succ n)) nhyps in
		kont0 (applist (mkVar id,List.rev_append args metas)) gls
	  | _ -> anomaly "wrong stack size"

let end_tac et2 gls =
  let info = get_its_info gls in
  let et1,pi,ek,clauses = 
    match info.pm_stack with
	Suppose_case::_ -> 
	  anomaly "This case should already be trapped"
      | Claim::_ ->  
	  error "\"end claim\" expected."
      | Focus_claim::_ ->
	  error "\"end focus\" expected."
      | Per(et',pi,ek,clauses)::_ -> (et',pi,ek,clauses) 
      | [] -> 
	  anomaly "This case should already be trapped" in
  let et = 
    if et1 <> et2 then
      match et1 with 
	  ET_Case_analysis -> 
	    error "\"end cases\" expected."
	| ET_Induction ->
	    error "\"end induction\" expected."
    else et1 in
    tclTHEN 
      tcl_erase_info
      begin
	match et,ek with
	    _,EK_unknown -> 
	      tclSOLVE [simplest_elim pi.per_casee]	
	  | ET_Case_analysis,EK_nodep ->
	      tclTHEN 
		(general_case_analysis (pi.per_casee,NoBindings))
		(default_justification (List.map mkVar clauses))
	  | ET_Induction,EK_nodep ->
	      tclTHENLIST
		[generalize (pi.per_args@[pi.per_casee]); 
		 simple_induct (AnonHyp (succ (List.length pi.per_args)));
		 default_justification (List.map mkVar clauses)]
	  | ET_Case_analysis,EK_dep tree ->
	      tclTHENLIST 
		[generalize (pi.per_args@[pi.per_casee]);
		 execute_cases true Anonymous pi 
		   (fun c -> tclTHENLIST 
		      [refine c;
		       clear clauses;
		       justification assumption])
		   (initial_instance_stack clauses) tree]	
	  | ET_Induction,EK_dep tree ->
	      tclTHEN (generalize (pi.per_args@[pi.per_casee]))
		begin
		  fun gls0 -> 
		    let fix_id = pf_get_new_id (id_of_string "_fix") gls0 in
		      tclTHEN 
			(fix (Some fix_id) (succ (List.length pi.per_args))) 
			(execute_cases true (Name fix_id) pi 
			   (fun c ->
			      tclTHENLIST 
				[clear [fix_id];
				 refine c;
				 clear clauses;
				 justification assumption
				 (* justification automation_tac *)])
			   (initial_instance_stack clauses) tree) gls0
		end	
      end gls

(* escape *)

let rec abstract_metas n avoid head = function
    [] -> 1,head,[]
  | (meta,typ)::rest -> 
      let id = Nameops.next_ident_away (id_of_string "_sbgl") avoid in
      let p,term,args = abstract_metas (succ n) (id::avoid) head rest in 
	succ p,mkLambda(Name id,typ,subst_meta [meta,mkRel p] term),
      (mkMeta n)::args 

let build_refining_context gls =
  let info = get_its_info gls in
  let avoid=pf_ids_of_hyps gls in
  let _,fn,args=abstract_metas 1 avoid info.pm_partial_goal info.pm_subgoals in
    applist (fn,args)
    
let escape_command pts =
  let pts1 = nth_unproven 1 pts in
  let gls = top_goal_of_pftreestate pts1 in
  let term = build_refining_context gls in
  let tac = tclTHEN 
    (abstract_operation (Proof_instr (true,{emph=0;instr=Pescape})) tcl_erase_info)
    (Tactics.refine term) in
    traverse 1 (solve_pftreestate tac pts1)

(* General instruction engine *)

let rec do_proof_instr_gen _thus _then instr = 
  match instr with 
      Pthus i -> 
	assert (not _thus);
	do_proof_instr_gen true _then i
    | Pthen i -> 	
	assert (not _then);
	do_proof_instr_gen _thus true i
    | Phence i -> 
	assert (not (_then || _thus));
	do_proof_instr_gen true true i
    | Pcut c ->
	instr_cut mk_stat_or_thesis _thus _then c
    | Psuffices c ->
	instr_suffices _then c 
    | Prew (s,c) ->
	assert (not _then);
	instr_rew _thus s c
    | Pconsider (c,hyps)    -> consider_tac c hyps
    | Pgiven hyps            -> given_tac hyps
    | Passume hyps           -> assume_tac hyps
    | Plet hyps              -> assume_tac hyps
    | Pclaim st              -> instr_claim false st 
    | Pfocus st              -> instr_claim true st
    | Ptake witl             -> take_tac witl
    | Pdefine (id,args,body) -> define_tac id args body
    | Pcast (id,typ)         -> cast_tac id typ 
    | Pper (et,cs)           -> per_tac et cs 
    | Psuppose hyps      -> suppose_tac hyps
    | Pcase (params,pat_info,hyps) -> case_tac params pat_info hyps
    | Pend (B_elim et) -> end_tac et
    | Pend _ | Pescape -> anomaly "Not applicable"
 
let eval_instr {instr=instr} =
  do_proof_instr_gen false false instr   

let rec preprocess pts instr =
  match instr with
    Phence i |Pthus i | Pthen i -> preprocess pts i
  | Psuffices _ | Pcut _ |  Passume _ | Plet _ | Pclaim _ | Pfocus _ 
  | Pconsider (_,_) | Pcast (_,_) | Pgiven _ | Ptake _ 
  | Pdefine (_,_,_) | Pper _ | Prew _ ->
      check_not_per pts;
      true,pts
  | Pescape -> 
      check_not_per pts;
      false,pts
  | Pcase _ | Psuppose _ | Pend (B_elim _) -> 
      true,close_previous_case pts
  | Pend bt -> 
      false,close_block bt pts 
      
let rec postprocess pts instr = 
  match instr with
      Phence i | Pthus i | Pthen i -> postprocess pts i
    | Pcut _ | Psuffices _ | Passume _ | Plet _ | Pconsider (_,_) | Pcast (_,_)
    | Pgiven _ | Ptake _ | Pdefine (_,_,_) | Prew (_,_) -> pts
    | Pclaim _ | Pfocus _ | Psuppose _ | Pcase _ | Pper _ -> nth_unproven 1 pts
    | Pescape -> escape_command pts
    | Pend (B_elim ET_Induction) ->
  	begin
	  let pf = proof_of_pftreestate pts in
	  let (pfterm,_) = extract_open_pftreestate pts in
	  let env =  Evd.evar_env (goal_of_proof pf) in
	    try 
	      Inductiveops.control_only_guard env pfterm;
	      goto_current_focus_or_top (mark_as_done pts)
 	    with 
		Type_errors.TypeError(env,
				      Type_errors.IllFormedRecBody(_,_,_)) ->
		  anomaly "\"end induction\" generated an ill-formed fixpoint"
	end
    | Pend _ -> 
	goto_current_focus_or_top (mark_as_done pts)

let do_instr raw_instr pts =
  let has_tactic,pts1 = preprocess pts raw_instr.instr in
  let pts2 = 
    if has_tactic then
      let gl = nth_goal_of_pftreestate 1 pts1 in
      let env=  pf_env gl in
      let sigma= project gl in
      let ist = {ltacvars = ([],[]); ltacrecvars = []; 
		 gsigma = sigma; genv = env} in
      let glob_instr = intern_proof_instr ist raw_instr in
      let instr = 
	interp_proof_instr (get_its_info gl) sigma env glob_instr in
      let lock_focus = is_focussing_instr instr.instr in
      let marker= Proof_instr (lock_focus,instr) in
	solve_nth_pftreestate 1 
	  (abstract_operation marker (eval_instr instr)) pts1
    else pts1 in
      postprocess pts2 raw_instr.instr

let proof_instr raw_instr =
  Pfedit.mutate (do_instr raw_instr)

(*

(* STUFF FOR ITERATED RELATIONS *)
let decompose_bin_app t= 
  let hd,args = destApp 

let identify_transitivity_lemma c =
  let varx,tx,c1 = destProd c in
  let vary,ty,c2 = destProd (pop c1) in
  let varz,tz,c3 = destProd (pop c2) in
  let _,p1,c4 = destProd (pop c3) in
  let _,lp2,lp3 = destProd (pop c4) in
  let p2=pop lp2 in
  let p3=pop lp3 in
*)
    
