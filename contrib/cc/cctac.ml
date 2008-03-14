(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4deps: "parsing/grammar.cma" i*)

(* $Id$ *)

(* This file is the interface between the c-c algorithm and Coq *)

open Evd
open Proof_type
open Names
open Libnames
open Nameops
open Inductiveops
open Declarations
open Term
open Termops
open Tacmach
open Tactics
open Tacticals
open Typing
open Ccalgo
open Tacinterp
open Ccproof
open Pp
open Util
open Format

let constant dir s = lazy (Coqlib.gen_constant "CC" dir s)

let _f_equal = constant ["Init";"Logic"] "f_equal"

let _eq_rect = constant ["Init";"Logic"] "eq_rect"

let _refl_equal = constant ["Init";"Logic"] "refl_equal"

let _sym_eq = constant ["Init";"Logic"] "sym_eq"

let _trans_eq = constant ["Init";"Logic"] "trans_eq"

let _eq = constant ["Init";"Logic"] "eq"

let _False = constant ["Init";"Logic"] "False"

(* decompose member of equality in an applicative format *)

let sf_of env sigma c = family_of_sort (destSort (type_of env sigma c))

let whd env=
  let infos=Closure.create_clos_infos Closure.betaiotazeta env in
    (fun t -> Closure.whd_val infos (Closure.inject t))

let whd_delta env=
   let infos=Closure.create_clos_infos Closure.betadeltaiota env in
    (fun t -> Closure.whd_val infos (Closure.inject t))

let rec decompose_term env sigma t=
    match kind_of_term (whd env t) with
      App (f,args)->
	let tf=decompose_term env sigma f in
	let targs=Array.map (decompose_term env sigma) args in
	  Array.fold_left (fun s t->Appli (s,t)) tf targs
    | Prod (_,a,_b) when not (dependent (mkRel 1) _b) ->
	let b = pop _b in
	let sort_b = sf_of env sigma b in
	let sort_a = sf_of env sigma a in
	Appli(Appli(Product (sort_a,sort_b) ,
		    decompose_term env sigma a),
	      decompose_term env sigma b)
    | Construct c->
	let (oib,_)=Global.lookup_inductive (fst c) in
	let nargs=mis_constructor_nargs_env env c in
	  Constructor {ci_constr=c;
		       ci_arity=nargs;
		       ci_nhyps=nargs-oib.mind_nparams}
    | _ ->if closed0 t then (Symb t) else raise Not_found
	
(* decompose equality in members and type *)
	
let atom_of_constr env sigma term =
  let wh =  (whd_delta env term) in
  let kot = kind_of_term wh in 
    match kot with
      App (f,args)->
	  if eq_constr f (Lazy.force _eq) && (Array.length args)=3 
	  then `Eq (args.(0),
		   decompose_term env sigma args.(1), 
		   decompose_term env sigma args.(2)) 
	  else `Other (decompose_term env sigma term)
    | _ -> `Other (decompose_term env sigma term)

let rec pattern_of_constr env sigma c =
  match kind_of_term (whd env c) with
      App (f,args)->
	let pf = decompose_term env sigma f in
	let pargs,lrels = List.split 
	  (array_map_to_list (pattern_of_constr env sigma) args) in
	  PApp (pf,List.rev pargs),
	List.fold_left Intset.union Intset.empty lrels
    | Prod (_,a,_b) when not (dependent (mkRel 1) _b) ->
	let b =pop _b in
	let pa,sa = pattern_of_constr env sigma a in
	let pb,sb = pattern_of_constr env sigma (pop b) in
	let sort_b = sf_of env sigma b in
	let sort_a = sf_of env sigma a in
	  PApp(Product (sort_a,sort_b),
	       [pa;pb]),(Intset.union sa sb)
    | Rel i -> PVar i,Intset.singleton i
    | _ -> 
	let pf = decompose_term env sigma c in
	  PApp (pf,[]),Intset.empty

let non_trivial = function
    PVar _ -> false
  | _ -> true

let patterns_of_constr env sigma nrels term=
  let f,args= 
    try destApp (whd_delta env term) with _ -> raise Not_found in
	if eq_constr f (Lazy.force _eq) && (Array.length args)=3 
	then 
	  let patt1,rels1 = pattern_of_constr env sigma args.(1)
	  and patt2,rels2 = pattern_of_constr env sigma args.(2) in
	  let valid1 = 
	    if Intset.cardinal rels1 <> nrels then Creates_variables
	    else if non_trivial patt1 then Normal
	    else Trivial args.(0) 
	  and valid2 =
	    if Intset.cardinal rels2 <> nrels then Creates_variables
	    else if non_trivial patt2 then Normal
	    else Trivial args.(0) in
	    if valid1 <> Creates_variables
	      || valid2 <> Creates_variables  then 
	      nrels,valid1,patt1,valid2,patt2
	    else raise Not_found
	else raise Not_found

let rec quantified_atom_of_constr env sigma nrels term =
  match kind_of_term (whd_delta env term) with
      Prod (_,atom,ff) -> 
	if eq_constr ff (Lazy.force _False) then
	  let patts=patterns_of_constr env sigma nrels atom in
	      `Nrule patts
	else 
	  quantified_atom_of_constr env sigma (succ nrels) ff
    | _ ->  
	let patts=patterns_of_constr env sigma nrels term in
	    `Rule patts	  

let litteral_of_constr env sigma term=
  match kind_of_term (whd_delta env term) with
    | Prod (_,atom,ff) -> 
	if eq_constr ff (Lazy.force _False) then
	  match (atom_of_constr env sigma atom) with
	      `Eq(t,a,b) -> `Neq(t,a,b)
	    | `Other(p) -> `Nother(p)
	else
	  begin
	    try 
	      quantified_atom_of_constr env sigma 1 ff  
	    with Not_found ->
	      `Other (decompose_term env sigma term)
	  end
    | _ -> 
	atom_of_constr env sigma term
	

(* store all equalities from the context *)
	
let rec make_prb gls depth additionnal_terms =
  let env=pf_env gls in
  let sigma=sig_sig gls in
  let state = empty depth gls in
  let pos_hyps = ref [] in
  let neg_hyps =ref [] in
    List.iter
      (fun c ->
	 let t = decompose_term env sigma c in
	   ignore (add_term state t)) additionnal_terms; 
    List.iter 
      (fun (id,_,e) ->
	 begin
	   let cid=mkVar id in
	   match litteral_of_constr env sigma e with
	       `Eq (t,a,b) -> add_equality state cid a b
	     | `Neq (t,a,b) -> add_disequality state (Hyp cid) a b
	     | `Other ph ->
		 List.iter 
		   (fun (cidn,nh) -> 
		      add_disequality state (HeqnH (cid,cidn)) ph nh) 
		   !neg_hyps;
		 pos_hyps:=(cid,ph):: !pos_hyps
	     | `Nother nh ->
		 List.iter 
		   (fun (cidp,ph) -> 
		      add_disequality state (HeqnH (cidp,cid)) ph nh) 
		   !pos_hyps;
		 neg_hyps:=(cid,nh):: !neg_hyps
	     | `Rule patts -> add_quant state id true patts
	     | `Nrule patts -> add_quant state id false patts
	 end) (Environ.named_context_of_val gls.it.evar_hyps);
    begin
      match atom_of_constr env sigma gls.it.evar_concl with
	  `Eq (t,a,b) -> add_disequality state Goal a b
	|	`Other g ->  
		  List.iter 
	      (fun (idp,ph) -> 
		 add_disequality state (HeqG idp) ph g) !pos_hyps
    end;
    state

(* indhyps builds the array of arrays of constructor hyps for (ind largs) *)

let build_projection intype outtype (cstr:constructor) special default gls=
  let env=pf_env gls in 
  let (h,argv) = 
    try destApp intype with 
	Invalid_argument _ -> (intype,[||])  in
  let ind=destInd h in 
  let types=Inductiveops.arities_of_constructors env ind in
  let lp=Array.length types in
  let ci=pred (snd cstr) in
  let branch i=
    let ti=Term.prod_appvect types.(i) argv in
    let rc=fst (Sign.decompose_prod_assum ti) in
    let head=
      if i=ci then special else default in  
      Sign.it_mkLambda_or_LetIn head rc in
  let branches=Array.init lp branch in
  let casee=mkRel 1 in
  let pred=mkLambda(Anonymous,intype,outtype) in
  let case_info=make_case_info (pf_env gls) ind RegularStyle in
  let body= mkCase(case_info, pred, casee, branches) in
  let id=pf_get_new_id (id_of_string "t") gls in     
    mkLambda(Name id,intype,body)
  
(* generate an adhoc tactic following the proof tree  *)

let _M =mkMeta

let rec proof_tac p gls =
  match p.p_rule with
      Ax c -> exact_check c gls
    | SymAx c -> 
	let l=constr_of_term p.p_lhs and 
	    r=constr_of_term p.p_rhs in
        let typ = refresh_universes (pf_type_of gls l) in 	  
	  exact_check
	    (mkApp(Lazy.force _sym_eq,[|typ;r;l;c|])) gls
    | Refl t ->
	let lr = constr_of_term t in
	let typ = refresh_universes (pf_type_of gls lr) in 
	exact_check
	   (mkApp(Lazy.force _refl_equal,[|typ;constr_of_term t|])) gls
    | Trans (p1,p2)->
	let t1 = constr_of_term p1.p_lhs and
	    t2 = constr_of_term p1.p_rhs and
	    t3 = constr_of_term p2.p_rhs in
	let typ = refresh_universes (pf_type_of gls t2) in 
	let prf = 
	  mkApp(Lazy.force _trans_eq,[|typ;t1;t2;t3;_M 1;_M 2|]) in
	  tclTHENS (refine prf) [(proof_tac p1);(proof_tac p2)] gls
    | Congr (p1,p2)->
	let tf1=constr_of_term p1.p_lhs 
	and tx1=constr_of_term p2.p_lhs 
	and tf2=constr_of_term p1.p_rhs 
	and tx2=constr_of_term p2.p_rhs in
	let typf = refresh_universes (pf_type_of gls tf1) in
	let typx = refresh_universes (pf_type_of gls tx1) in
	let typfx = refresh_universes (pf_type_of gls (mkApp (tf1,[|tx1|]))) in
	let id = pf_get_new_id (id_of_string "f") gls in
	let appx1 = mkLambda(Name id,typf,mkApp(mkRel 1,[|tx1|])) in
	let lemma1 =
	  mkApp(Lazy.force _f_equal,
		[|typf;typfx;appx1;tf1;tf2;_M 1|]) in
	let lemma2=
	  mkApp(Lazy.force _f_equal,
		[|typx;typfx;tf2;tx1;tx2;_M 1|]) in
	let prf = 
	  mkApp(Lazy.force _trans_eq,
		[|typfx;
		  mkApp(tf1,[|tx1|]);
		  mkApp(tf2,[|tx1|]);
		  mkApp(tf2,[|tx2|]);_M 2;_M 3|]) in
	  tclTHENS (refine prf)
	    [tclTHEN (refine lemma1) (proof_tac p1);
  	     tclFIRST
	       [tclTHEN (refine lemma2) (proof_tac p2);
		reflexivity;
		fun gls ->
		  errorlabstrm  "Congruence" 
		    (Pp.str 
		       "I don't know how to handle dependent equality")]] gls
  | Inject (prf,cstr,nargs,argind) ->
	 let ti=constr_of_term prf.p_lhs in
	 let tj=constr_of_term prf.p_rhs in
	 let default=constr_of_term p.p_lhs in
	 let intype=refresh_universes (pf_type_of gls ti) in
	 let outtype=refresh_universes (pf_type_of gls default) in
	 let special=mkRel (1+nargs-argind) in
	 let proj=build_projection intype outtype cstr special default gls in
	 let injt=
	   mkApp (Lazy.force _f_equal,[|intype;outtype;proj;ti;tj;_M 1|]) in 
	   tclTHEN (refine injt) (proof_tac prf) gls

let refute_tac c t1 t2 p gls =      
  let tt1=constr_of_term t1 and tt2=constr_of_term t2 in
  let intype=refresh_universes (pf_type_of gls tt1) in
  let neweq=
    mkApp(Lazy.force _eq,
	  [|intype;tt1;tt2|]) in
  let hid=pf_get_new_id (id_of_string "Heq") gls in
  let false_t=mkApp (c,[|mkVar hid|]) in
    tclTHENS (true_cut (Name hid) neweq)
      [proof_tac p; simplest_elim false_t] gls

let convert_to_goal_tac c t1 t2 p gls =
  let tt1=constr_of_term t1 and tt2=constr_of_term t2 in
  let sort=refresh_universes (pf_type_of gls tt2) in
  let neweq=mkApp(Lazy.force _eq,[|sort;tt1;tt2|]) in 
  let e=pf_get_new_id (id_of_string "e") gls in
  let x=pf_get_new_id (id_of_string "X") gls in
  let identity=mkLambda (Name x,sort,mkRel 1) in 
  let endt=mkApp (Lazy.force _eq_rect,
		  [|sort;tt1;identity;c;tt2;mkVar e|]) in
    tclTHENS (true_cut (Name e) neweq) 
      [proof_tac p;exact_check endt] gls

let convert_to_hyp_tac c1 t1 c2 t2 p gls =
  let tt2=constr_of_term t2 in
  let h=pf_get_new_id (id_of_string "H") gls in
  let false_t=mkApp (c2,[|mkVar h|]) in
    tclTHENS (true_cut (Name h) tt2)
      [convert_to_goal_tac c1 t1 t2 p;
       simplest_elim false_t] gls
  
let discriminate_tac cstr p gls =
  let t1=constr_of_term p.p_lhs and t2=constr_of_term p.p_rhs in
  let intype=refresh_universes (pf_type_of gls t1) in
  let concl=pf_concl gls in
  let outsort=mkType (new_univ ()) in
  let xid=pf_get_new_id (id_of_string "X") gls in
  let tid=pf_get_new_id (id_of_string "t") gls in
  let identity=mkLambda(Name xid,outsort,mkLambda(Name tid,mkRel 1,mkRel 1)) in
  let trivial=pf_type_of gls identity in
  let outtype=mkType (new_univ ()) in
  let pred=mkLambda(Name xid,outtype,mkRel 1) in
  let hid=pf_get_new_id (id_of_string "Heq") gls in     
  let proj=build_projection intype outtype cstr trivial concl gls in
  let injt=mkApp (Lazy.force _f_equal,
		  [|intype;outtype;proj;t1;t2;mkVar hid|]) in   
  let endt=mkApp (Lazy.force _eq_rect,
		  [|outtype;trivial;pred;identity;concl;injt|]) in
  let neweq=mkApp(Lazy.force _eq,[|intype;t1;t2|]) in
    tclTHENS (true_cut (Name hid) neweq) 
      [proof_tac p;exact_check endt] gls
      
(* wrap everything *)
	
let build_term_to_complete uf meta pac =
  let cinfo = get_constructor_info uf pac.cnode in
  let real_args = List.map (fun i -> constr_of_term (term uf i)) pac.args in
  let dummy_args = List.rev (list_tabulate meta pac.arity) in
  let all_args = List.rev_append real_args dummy_args in
    applistc (mkConstruct cinfo.ci_constr) all_args
      
let cc_tactic depth additionnal_terms gls=
  Coqlib.check_required_library ["Coq";"Init";"Logic"];
  let _ = debug Pp.msgnl (Pp.str "Reading subgoal ...") in
  let state = make_prb gls depth additionnal_terms in
  let _ = debug Pp.msgnl (Pp.str "Problem built, solving ...") in
  let sol = execute true state in
  let _ = debug Pp.msgnl (Pp.str "Computation completed.") in
  let uf=forest state in
    match sol with
	None -> tclFAIL 0 (str "congruence failed") gls  
      | Some reason ->
	  debug Pp.msgnl (Pp.str "Goal solved, generating proof ...");
	  match reason with
	      Discrimination (i,ipac,j,jpac) ->
		let p=build_proof uf (`Discr (i,ipac,j,jpac)) in
		let cstr=(get_constructor_info uf ipac.cnode).ci_constr in
		  discriminate_tac cstr p gls
	    | Incomplete ->
		let metacnt = ref 0 in
		let newmeta _ = incr metacnt; _M !metacnt in
		let terms_to_complete = 
		  List.map 
		    (build_term_to_complete uf newmeta) 
		    (epsilons uf) in 
		  Pp.msgnl
		    (Pp.str "Goal is solvable by congruence but \
 some arguments are missing.");
		  Pp.msgnl
		    (Pp.str "  Try " ++
		     hov 8
		       begin 
			 str "\"congruence with (" ++  
			 prlist_with_sep 
			   (fun () -> str ")" ++ pr_spc () ++ str "(")
			   (print_constr_env (pf_env gls))
			   terms_to_complete ++ 
			 str ")\","
		       end);
		  Pp.msgnl
		    (Pp.str "  replacing metavariables by arbitrary terms.");
		  tclFAIL 0 (str "Incomplete") gls
	    | Contradiction dis ->
		let p=build_proof uf (`Prove (dis.lhs,dis.rhs)) in
		let ta=term uf dis.lhs and tb=term uf dis.rhs in
		  match dis.rule with
		      Goal -> proof_tac p gls
		    | Hyp id -> refute_tac id ta tb p gls
		    | HeqG id -> 
			convert_to_goal_tac id ta tb p gls
		    | HeqnH (ida,idb) -> 
			convert_to_hyp_tac ida ta idb tb p gls
		    

let cc_fail gls =
  errorlabstrm  "Congruence" (Pp.str "congruence failed.")     

let congruence_tac depth l = 
  tclORELSE 
    (tclTHEN (tclREPEAT introf) (cc_tactic depth l)) 
    cc_fail

(* The [f_equal] tactic.

   It mimics the use of lemmas [f_equal], [f_equal2], etc.
   This isn't particularly related with congruence, apart from
   the fact that congruence is called internally. 
*)

let f_equal gl = 
  let cut_eq c1 c2 = 
    let ty = refresh_universes (pf_type_of gl c1) in 
    tclTHENTRY
      (Tactics.cut (mkApp (Lazy.force _eq, [|ty; c1; c2|]))) reflexivity
  in 
  try match kind_of_term (pf_concl gl) with 
    | App (r,[|_;t;t'|]) when eq_constr r (Lazy.force _eq) -> 
	begin match kind_of_term t, kind_of_term t' with 
	  | App (f,v), App (f',v') when Array.length v = Array.length v' ->
	      let rec cuts i = 
		if i < 0 then tclTRY (congruence_tac 1000 []) 
		else tclTHENFIRST (cut_eq v.(i) v'.(i)) (cuts (i-1))
	      in cuts (Array.length v - 1) gl
	  | _ -> tclIDTAC gl
	end
    | _ -> tclIDTAC gl
  with Type_errors.TypeError _ -> tclIDTAC gl
