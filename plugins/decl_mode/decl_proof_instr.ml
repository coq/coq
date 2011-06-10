(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util
open Pp
open Evd

open Refiner
open Proof_type
open Tacmach
open Tacinterp
open Decl_expr
open Decl_mode
open Decl_interp
open Glob_term
open Names
open Nameops
open Declarations
open Tactics
open Tacticals
open Term
open Termops
open Namegen
open Reductionops
open Goptions


(* Strictness option *)

let get_its_info gls = get_info gls.sigma gls.it

let get_strictness,set_strictness =
  let strictness = ref false in
    (fun () -> (!strictness)),(fun b -> strictness:=b)

let _ =
  declare_bool_option
    { optsync  = true;
      optname  = "strict mode";
      optkey   = ["Strict";"Proofs"];
      optread  = get_strictness;
      optwrite = set_strictness }

let tcl_change_info_gen info_gen =
  (fun gls ->
     let concl = pf_concl gls in
     let hyps = Goal.V82.hyps (project gls) (sig_it gls) in
     let extra = Goal.V82.extra (project gls) (sig_it gls) in
     let (gl,ev,sigma) = Goal.V82.mk_goal (project gls) hyps concl (info_gen extra) in
     let sigma = Goal.V82.partial_solution sigma (sig_it gls) ev in
     { it = [gl] ; sigma= sigma } )

open Store.Field

let tcl_change_info info gls =  
  let info_gen = Decl_mode.info.set info in
  tcl_change_info_gen info_gen gls

let tcl_erase_info gls =  tcl_change_info_gen (Decl_mode.info.remove) gls

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
  if not (Proof.is_done pts) then
    match get_stack pts with
	Per (_,_,_,_)::_ ->
	  error "You are inside a proof per cases/induction.\n\
Please \"suppose\" something or \"end\" it now."
      | _ -> ()

let mk_evd metalist gls =
  let evd0= create_goal_evar_defs (sig_sig gls) in
  let add_one (meta,typ) evd =
    meta_declare meta typ evd in
    List.fold_right add_one metalist evd0

let is_tmp id = (string_of_id id).[0] = '_'

let tmp_ids gls =
  let ctx = pf_hyps gls in
    match ctx with
	[] -> []
      | _::q -> List.filter is_tmp (ids_of_named_context q)

let clean_tmp gls =
  let clean_id id0 gls0 =
      tclTRY (clear [id0]) gls0 in
  let rec clean_all = function
      [] -> tclIDTAC
    | id :: rest -> tclTHEN (clean_id id) (clean_all rest)
  in
    clean_all (tmp_ids gls) gls

let assert_postpone id t =
  assert_tac (Name id) t

(* start a proof *)


let start_proof_tac gls=
  let info={pm_stack=[]} in
  tcl_change_info info gls

let go_to_proof_mode () =
  Pfedit.by start_proof_tac;
  let p = Proof_global.give_me_the_proof () in
  Decl_mode.focus p

(* closing gaps *)

let daimon_tac gls =
  set_daimon_flag ();
  {it=[];sigma=sig_sig gls}


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
  | _ -> anomaly "mark_rule_as_done"


(* post-instruction focus management *)

(* spiwack: This used to fail if there was no focusing command
   above, but I don't think it ever happened. I hope it doesn't mess
   things up*)
let goto_current_focus pts = 
  Decl_mode.maximal_unfocus pts

let goto_current_focus_or_top pts =
  goto_current_focus pts

(* return *)

let close_tactic_mode pts =
  try goto_current_focus pts
  with Not_found ->
    error "\"return\" cannot be used outside of Declarative Proof Mode."

let return_from_tactic_mode () =
  close_tactic_mode (Proof_global.give_me_the_proof ())

(* end proof/claim *)

let close_block bt pts =
    if Proof.no_focused_goal pts then
      goto_current_focus pts
    else
      let stack =
	if Proof.is_done pts then
	  get_top_stack pts
	else
	  get_stack pts 
      in
      match bt,stack with
	B_claim, Claim::_ | B_focus, Focus_claim::_ | B_proof, [] ->
	  (goto_current_focus pts)
      | _, Claim::_ ->
	  error "\"end claim\" expected."
      | _, Focus_claim::_ ->
	  error "\"end focus\" expected."
      | _, [] ->
 	  error "\"end proof\" expected."
      | _, (Per (et,_,_,_)::_|Suppose_case::Per (et,_,_,_)::_) ->
	  begin
	    match et with
		ET_Case_analysis -> error "\"end cases\" expected."
	      | ET_Induction ->  error "\"end induction\" expected."
	  end
      | _,_ -> anomaly "Lonely suppose on stack."


(* utility for suppose / suppose it is *)

let close_previous_case pts =
  if
    Proof.is_done pts
  then
    match get_top_stack pts with
	Per (et,_,_,_) :: _ -> anomaly "Weird case occured ..."
      | Suppose_case :: Per (et,_,_,_) :: _ ->
	  goto_current_focus (pts)
      | _ -> error "Not inside a proof per cases or induction."
  else
    match get_stack pts with
	Per (et,_,_,_) :: _ -> ()
      | Suppose_case :: Per (et,_,_,_) :: _ ->
	  goto_current_focus ((pts))
      | _ -> error "Not inside a proof per cases or induction."

(* Proof instructions *)

(* automation *)

let filter_hyps f gls =
  let filter_aux (id,_,_) =
    if f id then
      tclIDTAC
    else
      tclTRY (clear [id])  in
    tclMAP filter_aux (pf_hyps gls) gls

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
	    tclTHEN (letin_tac None (Names.Name id) c None Tacexpr.nowhere)
              (thin_body [id]) gls in
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
	   error "Insufficient justification."
	 else
	   begin
	     msg_warning (str "Insufficient justification.");
	     daimon_tac gls
	   end) gls

let default_justification elems gls=
  justification (tclTHEN (prepare_goal elems) automation_tac) gls

(* code for conclusion refining *)

let constant dir s = lazy (Coqlib.gen_constant "Declarative" dir s)

let _and       = constant ["Init";"Logic"] "and"

let _and_rect  = constant ["Init";"Logic"] "and_rect"

let _prod      = constant ["Init";"Datatypes"] "prod"

let _prod_rect = constant ["Init";"Datatypes"] "prod_rect"

let _ex        = constant ["Init";"Logic"] "ex"

let _ex_ind    = constant ["Init";"Logic"] "ex_ind"

let _sig       = constant ["Init";"Specif"] "sig"

let _sig_rect  = constant ["Init";"Specif"] "sig_rect"

let _sigT      = constant ["Init";"Specif"] "sigT"

let _sigT_rect = constant ["Init";"Specif"] "sigT_rect"

type stackd_elt =
{se_meta:metavariable;
 se_type:types;
 se_last_meta:metavariable;
 se_meta_list:(metavariable*types) list;
 se_evd: evar_map}

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
	    let evd = meta_assign se.se_meta
              (refiner,(Conv,TypeProcessed (* ? *))) se.se_evd in
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

let rec nf_list evd =
  function
      [] -> []
    | (m,typ)::others ->
	if meta_defined evd m then
	    nf_list evd others
	else
	  (m,nf_meta evd typ)::nf_list evd others

let find_subsubgoal c ctyp skip submetas gls =
  let env= pf_env gls in
  let concl = pf_concl gls in
  let evd = mk_evd ((0,concl)::submetas) gls in
  let stack = Stack.create () in
  let max_meta =
      List.fold_left (fun a (m,_) -> max a m) 0 submetas in
  let _ = Stack.push
		{se_meta=0;
		 se_type=concl;
		 se_last_meta=max_meta;
		 se_meta_list=[0,concl];
		 se_evd=evd} stack  in
  let rec dfs n =
    let se = Stack.pop stack in
      try
	let unifier =
	  Unification.w_unify env Reduction.CUMUL ~flags:Unification.elim_flags
	    ctyp se.se_type se.se_evd in
	  if n <= 0 then
	      {se with
		 se_evd=meta_assign se.se_meta
                  (c,(Conv,TypeNotProcessed (* ?? *))) unifier;
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
    nf_list nse.se_evd nse.se_meta_list,nf_meta nse.se_evd (mkMeta 0)

let concl_refiner metas body gls =
  let concl = pf_concl gls in
  let evd = sig_sig gls in
  let env = pf_env gls in
  let sort = family_of_sort (Typing.sort_of env evd concl) in
  let rec aux env avoid subst = function
      [] -> anomaly "concl_refiner: cannot happen"
    | (n,typ)::rest ->
	let _A = subst_meta subst typ in
	let x = id_of_name_using_hdchar env _A Anonymous in
	let _x = fresh_id avoid x gls in
	let nenv = Environ.push_named (_x,None,_A) env in
	let asort = family_of_sort (Typing.sort_of nenv evd _A) in
	let nsubst = (n,mkVar _x)::subst in
	  if rest = [] then
	    asort,_A,mkNamedLambda _x _A (subst_meta nsubst body)
	  else
	    let bsort,_B,nbody =
	      aux nenv (_x::avoid) ((n,mkVar _x)::subst) rest in
	    let body = mkNamedLambda _x _A nbody in
	      if occur_term (mkVar _x) _B then
	        begin
		  let _P = mkNamedLambda _x _A _B in
		    match bsort,sort with
			InProp,InProp ->
			  let _AxB = mkApp(Lazy.force _ex,[|_A;_P|]) in
			    InProp,_AxB,
			  mkApp(Lazy.force _ex_ind,[|_A;_P;concl;body|])
		    | InProp,_ ->
			let _AxB = mkApp(Lazy.force _sig,[|_A;_P|]) in
			let _P0 = mkLambda(Anonymous,_AxB,concl) in
			  InType,_AxB,
			mkApp(Lazy.force _sig_rect,[|_A;_P;_P0;body|])
		    | _,_ ->
			let _AxB = mkApp(Lazy.force _sigT,[|_A;_P|]) in
			let _P0 = mkLambda(Anonymous,_AxB,concl) in
			  InType,_AxB,
			mkApp(Lazy.force _sigT_rect,[|_A;_P;_P0;body|])
		end
	      else
		begin
		  match asort,bsort with
		      InProp,InProp ->
			let _AxB = mkApp(Lazy.force _and,[|_A;_B|]) in
			  InProp,_AxB,
		     mkApp(Lazy.force _and_rect,[|_A;_B;concl;body|])
		    |_,_ ->
		       let _AxB = mkApp(Lazy.force _prod,[|_A;_B|]) in
		       let _P0 = mkLambda(Anonymous,_AxB,concl) in
			 InType,_AxB,
			mkApp(Lazy.force _prod_rect,[|_A;_B;_P0;body|])
		end
  in
  let (_,_,prf) = aux env [] [] metas in
    mkApp(prf,[|mkMeta 1|])

let thus_tac c ctyp submetas gls =
  let list,proof =
    try
      find_subsubgoal c ctyp 0 submetas gls
    with Not_found ->
      error "I could not relate this statement to the thesis." in
  if list = [] then
    exact_check proof gls
  else
    let refiner = concl_refiner list proof gls in
      Tactics.refine refiner gls

(* general forward step *)

let mk_stat_or_thesis info gls = function
    This c -> c
  | Thesis (For _ ) ->
      error "\"thesis for ...\" is not applicable here."
  | Thesis Plain -> pf_concl gls

let just_tac _then cut info gls0 =
  let items_tac gls =
    match cut.cut_by with
	None -> tclIDTAC gls
      | Some items ->
	  let items_ =
	    if _then then
	      let last_id = get_last (pf_env gls) in
		(mkVar last_id)::items
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
  let (c_id,_) = match stat.st_label with
      Anonymous ->
	pf_get_new_id (id_of_string "_fact") gls0,false
    | Name id -> id,true in
  let c_stat = mkstat info gls0 stat.st_it in
  let thus_tac gls=
    if _thus then
      thus_tac (mkVar c_id) c_stat [] gls
    else tclIDTAC gls in
    tclTHENS (assert_postpone c_id c_stat)
      [tclTHEN tcl_erase_info (just_tac _then cut info);
       thus_tac] gls0



(* iterated equality *)
let _eq = Libnames.constr_of_global (Coqlib.glob_eq)

let decompose_eq id gls =
  let typ = pf_get_hyp_typ gls id in
  let whd =  (special_whd gls typ) in
    match kind_of_term whd with
	App (f,args)->
	  if eq_constr f _eq && (Array.length args)=3
	  then (args.(0),
		args.(1),
		args.(2))
	  else error "Previous step is not an equality."
      | _ -> error "Previous step is not an equality."

let instr_rew _thus rew_side cut gls0 =
  let last_id =
    try get_last (pf_env gls0) with _ -> error "No previous equality." in
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
  let (c_id,_) = match cut.cut_stat.st_label with
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
	    tclTHENS (assert_postpone c_id new_eq)
	      [tclTHEN tcl_erase_info
		 (tclTHENS (transitivity lhs)
		    [just_tac;exact_check (mkVar last_id)]);
	       thus_tac new_eq] gls0
      | Rhs ->
	  let new_eq = mkApp(_eq,[|typ;lhs;cut.cut_stat.st_it|]) in
	    tclTHENS (assert_postpone c_id new_eq)
	      [tclTHEN tcl_erase_info
		 (tclTHENS (transitivity rhs)
		    [exact_check (mkVar last_id);just_tac]);
	       thus_tac new_eq] gls0



(* tactics for claim/focus *)

let instr_claim _thus st gls0 =
  let info = get_its_info gls0 in
  let (id,_) = match st.st_label with
      Anonymous -> pf_get_new_id (id_of_string "_claim") gls0,false
    | Name id -> id,true in
  let thus_tac gls=
    if _thus then
      thus_tac (mkVar id) st.st_it [] gls
    else tclIDTAC gls in
  let ninfo1 = {pm_stack=
      (if _thus then Focus_claim else Claim)::info.pm_stack} in
    tclTHENS (assert_postpone id st.st_it)
      [thus_tac;
       tcl_change_info ninfo1] gls0

(* tactics for assume *)

let push_intro_tac coerce nam gls =
      let (hid,_) =
	match nam with
	    Anonymous -> pf_get_new_id (id_of_string "_hyp") gls,false
	  | Name id -> id,true in
	tclTHENLIST
	  [intro_mustbe_force hid;
	   coerce hid]
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
  let c_stat = build_product ctx (mk_stat_or_thesis info gls0 hd) in
  let metas = metas_from 1 ctx in
  let c_ctx,c_head = build_applist c_stat metas in
  let c_term = applist (mkVar c_id,List.map mkMeta metas) in
  let thus_tac gls=
    thus_tac c_term c_head c_ctx gls in
   tclTHENS (assert_postpone c_id c_stat)
     [tclTHENLIST
	 [ assume_tac ctx;
	   tcl_erase_info;
	   just_tac _then cut info];
      thus_tac] gls0

(* tactics for consider/given *)

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
    ltac ids gls
  else
    let id = pf_get_new_id (id_of_string "_tmp") gls in
      tclTHEN
	(intro_mustbe_force id)
	(intron_then (pred n) (id::ids) ltac) gls


let rec consider_match may_intro introduced available expected gls =
  match available,expected with
      [],[] ->
	  tclIDTAC gls
    | _,[] -> error "Last statements do not match a complete hypothesis."
	(* should tell which ones *)
    | [],hyps ->
	if may_intro then
	  begin
 	    let id = pf_get_new_id (id_of_string "_tmp") gls in
	      tclIFTHENELSE
		(intro_mustbe_force id)
		(consider_match true [] [id] hyps)
		(fun _ ->
		   error "Not enough sub-hypotheses to match statements.")
		gls
          end
	else
	  error "Not enough sub-hypotheses to match statements."
	    (* should tell which ones *)
    | id::rest_ids,(Hvar st | Hprop st)::rest ->
	tclIFTHENELSE (convert_hyp (id,None,st.st_it))
	  begin
	    match st.st_label with
		Anonymous ->
		  consider_match may_intro ((id,false)::introduced) rest_ids rest
	      | Name hid ->
		  tclTHENLIST
		    [rename_hyp [id,hid];
		     consider_match may_intro ((hid,true)::introduced) rest_ids rest]
	  end
	  begin
	    (fun gls ->
	       let nhyps =
		 try conjunction_arity id gls with
		     Not_found -> error "Matching hypothesis not found." in
		 tclTHENLIST
		   [general_case_analysis false (mkVar id,NoBindings);
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
	  (forward None (Some (dummy_loc, Genarg.IntroIdentifier id)) c)
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
    letin_tac None (Name id) t None Tacexpr.nowhere gls

(* tactics for reconsider *)

let cast_tac id_or_thesis typ gls =
  match id_or_thesis with
      This id ->
	let (_,body,_) = pf_get_hyp gls id in
	  convert_hyp (id,body,typ) gls
    | Thesis (For _ ) ->
	error "\"thesis for ...\" is not applicable here."
    | Thesis Plain ->
          convert_concl typ DEFAULTcast gls

(* per cases *)

let is_rec_pos (main_ind,wft) =
  match main_ind with
      None -> false
    | Some index ->
	match fst (Rtree.dest_node wft) with
	    Mrec (_,i) when i = index -> true
	  | _ -> false

let rec constr_trees (main_ind,wft) ind =
    match Rtree.dest_node wft with
      Norec,_ ->
	let itree =
	  (snd (Global.lookup_inductive ind)).mind_recargs in
	  constr_trees (None,itree) ind
    | _,constrs -> main_ind,constrs

let ind_args rp ind =
    let main_ind,constrs = constr_trees rp ind in
    let args ctree =
      Array.map (fun t -> main_ind,t) (snd (Rtree.dest_node ctree)) in
      Array.map args constrs

let init_tree ids ind rp nexti =
  let indargs = ind_args rp ind in
  let do_i i arp = (Array.map is_rec_pos arp),nexti i arp in
    Split_patt (ids,ind,Array.mapi do_i indargs)

let map_tree_rp rp id_fun mapi = function
    Split_patt (ids,ind,branches) ->
  let indargs = ind_args rp ind in
  let do_i i (recargs,bri) = recargs,mapi i indargs.(i) bri in
    Split_patt (id_fun ids,ind,Array.mapi do_i branches)
  | _ -> failwith "map_tree_rp: not a splitting node"

let map_tree id_fun mapi = function
    Split_patt (ids,ind,branches) ->
  let do_i i (recargs,bri) = recargs,mapi i bri in
    Split_patt (id_fun ids,ind,Array.mapi do_i branches)
  | _ -> failwith "map_tree: not a splitting node"


let start_tree env ind rp =
  init_tree Idset.empty ind rp (fun _ _ -> None)

let build_per_info etype casee gls =
  let concl=pf_concl gls in
  let env=pf_env gls in
  let ctyp=pf_type_of gls casee in
  let is_dep = dependent casee concl in
  let hd,args = decompose_app (special_whd gls ctyp) in
  let ind =
    try
      destInd hd
    with _ ->
      error "Case analysis must be done on an inductive object." in
  let mind,oind = Global.lookup_inductive ind in
  let nparams,index =
    match etype with
	ET_Induction -> mind.mind_nparams_rec,Some (snd ind)
      | _ -> mind.mind_nparams,None in
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
   per_nparams=nparams;
   per_wf=index,oind.mind_recargs}

let per_tac etype casee gls=
  let env=pf_env gls in
  let info = get_its_info gls in
    match casee with
	Real c ->
	  let is_dep,per_info = build_per_info etype c gls in
	  let ek =
	    if is_dep then
	      EK_dep (start_tree env per_info.per_ind per_info.per_wf)
	    else EK_unknown in
	    tcl_change_info
	      {pm_stack=
		  Per(etype,per_info,ek,[])::info.pm_stack} gls
      | Virtual cut ->
	  assert (cut.cut_stat.st_label=Anonymous);
	  let id = pf_get_new_id (id_of_string "anonymous_matched") gls in
	  let c = mkVar id in
	  let modified_cut =
	    {cut with cut_stat={cut.cut_stat with st_label=Name id}} in
	    tclTHEN
	      (instr_cut (fun _ _ c -> c) false false modified_cut)
	      (fun gls0 ->
		 let is_dep,per_info = build_per_info etype c gls0 in
		   assert (not is_dep);
		   tcl_change_info
		     {pm_stack=
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
  let thesis = pf_concl gls0 in
  let id = pf_get_new_id (id_of_string "subcase_") gls0 in
  let clause = build_product hyps thesis in
  let ninfo1 = {pm_stack=Suppose_case::info.pm_stack} in
  let old_clauses,stack = register_nodep_subcase id info.pm_stack in
  let ninfo2 = {pm_stack=stack} in
    tclTHENS (assert_postpone id clause)
      [tclTHENLIST [tcl_change_info ninfo1;
		    assume_tac hyps;
		    clear old_clauses];
       tcl_change_info ninfo2] gls0

(* suppose it is ... *)

(* pattern matching compiling *)

let rec skip_args rest ids n =
  if n <= 0 then
    Close_patt rest
  else
    Skip_patt (ids,skip_args rest ids (pred n))

let rec tree_of_pats ((id,_) as cpl) pats =
  match pats with
      [] -> End_patt cpl
    | args::stack ->
	match args with
	    [] -> Close_patt (tree_of_pats cpl stack)
	  | (patt,rp) :: rest_args ->
	      match patt with
		  PatVar (_,v) ->
		    Skip_patt (Idset.singleton id,
			       tree_of_pats cpl (rest_args::stack))
		| PatCstr (_,(ind,cnum),args,nam) ->
		    let nexti i ati =
		      if i = pred cnum then
			let nargs =
			  list_map_i (fun j a -> (a,ati.(j))) 0 args in
			  Some (Idset.singleton id,
				tree_of_pats cpl (nargs::rest_args::stack))
		      else None
		      in init_tree Idset.empty ind rp nexti

let rec add_branch ((id,_) as cpl) pats tree=
  match pats with
      [] ->
	begin
	  match tree with
	      End_patt cpl0 -> End_patt cpl0
		(* this ensures precedence for overlapping patterns *)
	    | _ -> anomaly "tree is expected to end here"
	end
    | args::stack ->
	match args with
	    [] ->
	      begin
		match tree with
		   Close_patt t ->
		     Close_patt (add_branch cpl stack t)
		  | _ -> anomaly "we should pop here"
	      end
	  | (patt,rp) :: rest_args ->
	      match patt with
		  PatVar (_,v) ->
		    begin
		      match tree with
			  Skip_patt (ids,t) ->
			    Skip_patt (Idset.add id ids,
				       add_branch cpl (rest_args::stack) t)
			| Split_patt (_,_,_) ->
			    map_tree (Idset.add id)
			      (fun i bri ->
				 append_branch cpl 1 (rest_args::stack) bri)
			      tree
			| _ -> anomaly "No pop/stop expected here"
		    end
		| PatCstr (_,(ind,cnum),args,nam) ->
		      match tree with
			Skip_patt (ids,t) ->
			  let nexti i ati =
			    if i = pred cnum then
			      let nargs =
				list_map_i (fun j a -> (a,ati.(j))) 0 args in
				Some (Idset.add id ids,
				      add_branch cpl (nargs::rest_args::stack)
					(skip_args t ids (Array.length ati)))
			    else
			      Some (ids,
				    skip_args t ids (Array.length ati))
			  in init_tree ids ind rp nexti
		      | Split_patt (_,ind0,_) ->
			  if (ind <> ind0) then error
			    (* this can happen with coercions *)
	                    "Case pattern belongs to wrong inductive type.";
			  let mapi i ati bri =
			    if i = pred cnum then
			      let nargs =
				list_map_i (fun j a -> (a,ati.(j))) 0 args in
				append_branch cpl 0
				  (nargs::rest_args::stack) bri
			    else bri in
			    map_tree_rp rp (fun ids -> ids) mapi tree
		      | _ -> anomaly "No pop/stop expected here"
and append_branch ((id,_) as cpl) depth pats = function
    Some (ids,tree) ->
      Some (Idset.add id ids,append_tree cpl depth pats tree)
  | None ->
      Some (Idset.singleton id,tree_of_pats cpl pats)
and append_tree ((id,_) as cpl) depth pats tree =
  if depth<=0 then add_branch cpl pats tree
  else match tree with
      Close_patt t ->
	Close_patt (append_tree cpl (pred depth) pats t)
    | Skip_patt (ids,t) ->
	Skip_patt (Idset.add id ids,append_tree cpl depth pats t)
    | End_patt _ -> anomaly "Premature end of branch"
    | Split_patt (_,_,_) ->
	map_tree (Idset.add id)
	  (fun i bri -> append_branch cpl (succ depth) pats bri) tree

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
	 str"cannot give an induction hypothesis (wrong inductive type).") in
  let params,args = list_chop per_info.per_nparams all_args in
  let _ = if not (List.for_all2 eq_constr params per_info.per_params) then
    errorlabstrm "thesis_for"
      ((Printer.pr_constr_env env obj) ++ spc () ++
	 str "cannot give an induction hypothesis (wrong parameters).") in
  let hd2 = (applist ((lift (List.length rc) per_info.per_pred),args@[obj])) in
    compose_prod rc (whd_beta Evd.empty hd2)

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
	    | Plain -> pf_concl gls in
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
	(EK_dep (start_tree env per_info.per_ind per_info.per_wf))
  | EK_dep tree -> EK_dep (add_branch id [[pat,per_info.per_wf]] tree)

let case_tac params pat_info hyps gls0 =
  let info = get_its_info gls0 in
  let id = pf_get_new_id (id_of_string "subcase_") gls0 in
  let et,per_info,ek,old_clauses,rest =
    match info.pm_stack with
	Per (et,pi,ek,old_clauses)::rest -> (et,pi,ek,old_clauses,rest)
      | _ -> anomaly "wrong place for cases" in
  let clause = build_dep_clause params pat_info per_info hyps gls0 in
  let ninfo1 = {pm_stack=Suppose_case::info.pm_stack} in
  let nek = 
    register_dep_subcase (id,(List.length params,List.length hyps)) 
      (pf_env gls0) per_info pat_info.pat_pat ek in  
  let ninfo2 = {pm_stack=Per(et,per_info,nek,id::old_clauses)::rest} in
    tclTHENS (assert_postpone id clause)
      [tclTHENLIST
	 [tcl_change_info ninfo1;
	  assume_st (params@pat_info.pat_vars);
	  assume_st_letin pat_info.pat_aliases;
	  assume_hyps_or_theses hyps;
	  clear old_clauses];
       tcl_change_info ninfo2] gls0

(* end cases *)

type instance_stack =
    (constr option*(constr list) list) list

let initial_instance_stack ids =
  List.map (fun id -> id,[None,[]]) ids

let push_one_arg arg = function
    [] -> anomaly "impossible"
  | (head,args) :: ctx ->
      ((head,(arg::args)) :: ctx)

let push_arg arg stacks =
  List.map (fun (id,stack) -> (id,push_one_arg arg stack)) stacks


let push_one_head c ids (id,stack) =
  let head = if Idset.mem id ids then Some c else None in
    id,(head,[]) :: stack

let push_head c ids stacks =
  List.map (push_one_head c ids) stacks

let pop_one (id,stack) =
  let nstack=
    match stack with
	[] -> anomaly "impossible"
      | [c] as l -> l
      | (Some head,args)::(head0,args0)::ctx ->
	  let arg = applist (head,(List.rev args)) in
	    (head0,(arg::args0))::ctx
     | (None,args)::(head0,args0)::ctx ->
	 (head0,(args@args0))::ctx
  in id,nstack

let pop_stacks stacks =
  List.map pop_one stacks

let hrec_for fix_id per_info gls obj_id =
  let obj=mkVar obj_id in
  let typ=pf_get_hyp_typ gls obj_id in
  let rc,hd1=decompose_prod typ in
  let cind,all_args=decompose_app typ in
  let ind = destInd cind in assert (ind=per_info.per_ind);
  let params,args= list_chop per_info.per_nparams all_args in
  assert begin
    try List.for_all2 eq_constr params per_info.per_params with
        Invalid_argument _ -> false end;
  let hd2 = applist (mkVar fix_id,args@[obj]) in
    compose_lam rc (whd_beta gls.sigma hd2)


let rec execute_cases fix_name per_info tacnext args objs nhrec tree gls =
  match tree, objs  with
      Close_patt t,_ ->
	let args0 = pop_stacks args in
	  execute_cases fix_name per_info tacnext args0 objs nhrec t gls
    | Skip_patt (_,t),skipped::next_objs ->
	let args0 = push_arg skipped args in
	  execute_cases fix_name per_info tacnext args0 next_objs nhrec t gls
    | End_patt (id,(nparams,nhyps)),[] -> 
	begin
	  match List.assoc id args with
	      [None,br_args] -> 
		let all_metas = 
		  list_tabulate (fun n -> mkMeta (succ n)) (nparams + nhyps)  in
		let param_metas,hyp_metas = list_chop nparams all_metas in
		  tclTHEN
		    (tclDO nhrec introf)
		    (tacnext 
		       (applist (mkVar id,
				 List.append param_metas 
				   (List.rev_append br_args hyp_metas)))) gls
	    | _ -> anomaly "wrong stack size"
	end
    | Split_patt (ids,ind,br), casee::next_objs ->
	let (mind,oind) as spec = Global.lookup_inductive ind in
	let nparams = mind.mind_nparams in
	let concl=pf_concl gls in
	let env=pf_env gls in
	let ctyp=pf_type_of gls casee in
	let hd,all_args = decompose_app (special_whd gls ctyp) in
	let _ = assert (destInd hd = ind) in (* just in case *)
	let params,real_args = list_chop nparams all_args in
	let abstract_obj c body =
	  let typ=pf_type_of gls c in
	    lambda_create env (typ,subst_term c body) in
	let elim_pred = List.fold_right abstract_obj
	  real_args (lambda_create env (ctyp,subst_term casee concl)) in
	let case_info = Inductiveops.make_case_info env ind RegularStyle in
	let gen_arities = Inductive.arities_of_constructors ind spec in
	let f_ids typ =
	  let sign =
	    (prod_assum (Term.prod_applist typ params)) in
	    find_intro_names sign gls in
	let constr_args_ids = Array.map f_ids gen_arities in
	let case_term =
	  mkCase(case_info,elim_pred,casee,
		 Array.mapi (fun i _ -> mkMeta (succ i)) constr_args_ids) in
	let branch_tac i (recargs,bro) gls0 =
	  let args_ids = constr_args_ids.(i) in
	  let rec aux n = function
	      [] ->
		assert (n=Array.length recargs);
		next_objs,[],nhrec
	    | id :: q ->
		let objs,recs,nrec = aux (succ n) q in
		  if recargs.(n)
		  then (mkVar id::objs),(id::recs),succ nrec
		  else (mkVar id::objs),recs,nrec in
	  let objs,recs,nhrec = aux 0 args_ids in
	    tclTHENLIST
	      [tclMAP intro_mustbe_force args_ids;
	       begin
		 fun gls1 ->
		   let hrecs =
		     List.map
		       (fun id ->
			  hrec_for (out_name fix_name) per_info gls1 id)
		       recs in
		     generalize hrecs gls1
	       end;
	       match bro with
		   None ->
		     msg_warning (str "missing case");
		     tacnext (mkMeta 1)
		 | Some (sub_ids,tree) ->
		     let br_args =
		       List.filter
			 (fun (id,_) -> Idset.mem id sub_ids) args in
		     let construct =
		       applist (mkConstruct(ind,succ i),params) in
		     let p_args =
		       push_head construct ids br_args in
		       execute_cases fix_name per_info tacnext
			 p_args objs nhrec tree] gls0 in
	  tclTHENSV
	    (refine case_term)
	    (Array.mapi branch_tac br) gls
    | Split_patt (_, _, _) , [] ->
	anomaly "execute_cases : Nothing to split"
    | Skip_patt _ , [] ->
	anomaly "execute_cases : Nothing to skip"
    | End_patt (_,_) , _ :: _  ->
	anomaly "execute_cases : End of branch with garbage left"

let understand_my_constr c gls =
  let env = pf_env gls in
  let nc = names_of_rel_context env in
  let rawc = Detyping.detype false [] nc c in
  let rec frob = function GEvar _ -> GHole (dummy_loc,QuestionMark Expand) | rc ->  map_glob_constr frob rc in
    Pretyping.Default.understand_tcc (sig_sig gls) env ~expected_type:(pf_concl gls) (frob rawc)

let my_refine c gls =
  let oc = understand_my_constr c gls in
  Refine.refine oc gls

(* end focus/claim *)

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
		(general_case_analysis false (pi.per_casee,NoBindings))
		(default_justification (List.map mkVar clauses))
	  | ET_Induction,EK_nodep ->
	      tclTHENLIST
		[generalize (pi.per_args@[pi.per_casee]);
		 simple_induct (AnonHyp (succ (List.length pi.per_args)));
		 default_justification (List.map mkVar clauses)]
	  | ET_Case_analysis,EK_dep tree ->
		 execute_cases Anonymous pi 
		   (fun c -> tclTHENLIST 
		      [my_refine c;
		       clear clauses;
		       justification assumption])
		   (initial_instance_stack clauses) [pi.per_casee] 0 tree
	  | ET_Induction,EK_dep tree ->
	      let nargs = (List.length pi.per_args) in
		tclTHEN (generalize (pi.per_args@[pi.per_casee]))
		  begin
		    fun gls0 ->
		      let fix_id =
			pf_get_new_id (id_of_string "_fix") gls0 in
		      let c_id =
			pf_get_new_id (id_of_string "_main_arg") gls0 in
			tclTHENLIST
			  [fix (Some fix_id) (succ nargs);
			   tclDO nargs introf;
			   intro_mustbe_force c_id;
			   execute_cases (Name fix_id) pi
			     (fun c ->
				tclTHENLIST
				  [clear [fix_id];
				   my_refine c;
				   clear clauses;
				   justification assumption])
			     (initial_instance_stack clauses)
			     [mkVar c_id]  0 tree] gls0
		  end
      end gls

(* escape *)

let escape_tac gls =
  (* spiwack: sets an empty info stack to avoid interferences.
     We could erase the info altogether, but that doesn't play
     well with the Decl_mode.focus (used in post_processing). *)
  let info={pm_stack=[]} in
  tcl_change_info info gls

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
    | Pend _ -> anomaly "Not applicable"
    | Pescape -> escape_tac

let eval_instr {instr=instr} =
  do_proof_instr_gen false false instr

let rec preprocess pts instr =
  match instr with
    Phence i |Pthus i | Pthen i -> preprocess pts i
  | Psuffices _ | Pcut _ |  Passume _ | Plet _ | Pclaim _ | Pfocus _
  | Pconsider (_,_) | Pcast (_,_) | Pgiven _ | Ptake _
  | Pdefine (_,_,_) | Pper _ | Prew _ ->
      check_not_per pts;
      true
  | Pescape ->
      check_not_per pts;
      true
  | Pcase _ | Psuppose _ | Pend (B_elim _) ->
      close_previous_case pts ;
      true
  | Pend bt ->
      close_block bt pts ;
      false

let rec postprocess pts instr =
  match instr with
      Phence i | Pthus i | Pthen i -> postprocess pts i
    | Pcut _ | Psuffices _ | Passume _ | Plet _ | Pconsider (_,_) | Pcast (_,_)
    | Pgiven _ | Ptake _ | Pdefine (_,_,_) | Prew (_,_) -> ()
    | Pclaim _ | Pfocus _ | Psuppose _ | Pcase _ | Pper _ ->
      Decl_mode.focus pts
    | Pescape ->
      Decl_mode.focus pts;
      Proof_global.set_proof_mode "Classic"
    | Pend (B_elim ET_Induction) ->
  	begin
	  let pfterm = List.hd (Proof.partial_proof pts) in
	  let { it = gls ; sigma = sigma } = Proof.V82.subgoals pts in
	  let env =  try
		       Goal.V82.env sigma (List.hd gls)
	             with Failure "hd" ->
		       Global.env ()
	  in
	    try
	      Inductiveops.control_only_guard env pfterm;
	      goto_current_focus_or_top pts
 	    with
		Type_errors.TypeError(env,
				      Type_errors.IllFormedRecBody(_,_,_,_,_)) ->
		  anomaly "\"end induction\" generated an ill-formed fixpoint"
	end
    | Pend _ ->
	goto_current_focus_or_top (pts)

let do_instr raw_instr pts =
  let has_tactic = preprocess pts raw_instr.instr in
  begin
    if has_tactic then
      let { it=gls ; sigma=sigma } = Proof.V82.subgoals pts in
      let gl = { it=List.hd gls ; sigma=sigma } in
      let env=  pf_env gl in
      let ist = {ltacvars = ([],[]); ltacrecvars = [];
		 gsigma = sigma; genv = env} in
      let glob_instr = intern_proof_instr ist raw_instr in
      let instr =
	interp_proof_instr (get_its_info gl) sigma env glob_instr in
      Pfedit.by (tclTHEN (eval_instr instr) clean_tmp)
    else () end;
  postprocess pts raw_instr.instr;
  (* spiwack: this should restore a compatible semantics with
     v8.3 where we never stayed focused on 0 goal. *)
  Decl_mode.maximal_unfocus pts

let proof_instr raw_instr =
  let p = Proof_global.give_me_the_proof () in
  do_instr raw_instr p

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

