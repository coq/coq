(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4deps: "parsing/grammar.cma" i*)

open Term
open Termops
open Environ
open Declarations
open Entries
open Pp
open Names
open Libnames
open Nameops
open Util
open Closure
open RedFlags
open Tacticals
open Typing
open Tacmach
open Tactics
open Nametab
open Declare
open Decl_kinds
open Tacred
open Proof_type
open Vernacinterp
open Pfedit
open Topconstr
open Rawterm
open Pretyping
open Safe_typing
open Constrintern
open Hiddentac

open Equality
open Auto
open Eauto

open Genarg

let observe_tac s tac g = tac g

(* let observe_tac s tac g = *)
(*   begin try msgnl (Printer.pr_goal (sig_it g)) with _ -> assert false end; *)
(*  try let v = tac g in msgnl ((str s)++(str " ")++(str "finished")); v *)
(*  with e ->  *)
(*    msgnl (str "observation "++str s++str " raised an exception"); raise e;; *)

let hyp_ids = List.map id_of_string
    ["x";"v";"k";"def";"p";"h";"n";"h'"; "anonymous"; "teq"; "rec_res";
     "hspec";"heq"; "hrec"; "hex"; "teq"; "pmax";"hle"];;

let rec nthtl = function
    l, 0 -> l  | _::tl, n -> nthtl (tl, n-1) | [], _ -> [];;

let hyp_id n l = List.nth l n;;

let (x_id:identifier) = hyp_id 0 hyp_ids;;
let (v_id:identifier) = hyp_id 1 hyp_ids;;
let (k_id:identifier) = hyp_id 2 hyp_ids;;
let (def_id:identifier) = hyp_id 3 hyp_ids;;
let (p_id:identifier) = hyp_id 4 hyp_ids;;
let (h_id:identifier) = hyp_id 5 hyp_ids;;
let (n_id:identifier) = hyp_id 6 hyp_ids;;
let (h'_id:identifier) = hyp_id 7 hyp_ids;;
let (ano_id:identifier) = hyp_id 8 hyp_ids;;
let (rec_res_id:identifier) = hyp_id 10 hyp_ids;;
let (hspec_id:identifier) = hyp_id 11 hyp_ids;;
let (heq_id:identifier) = hyp_id 12 hyp_ids;;
let (hrec_id:identifier) = hyp_id 13 hyp_ids;;
let (hex_id:identifier) = hyp_id 14 hyp_ids;;
let (teq_id:identifier) = hyp_id 15 hyp_ids;;
let (pmax_id:identifier) = hyp_id 16 hyp_ids;;
let (hle_id:identifier) = hyp_id 17 hyp_ids;;

let message s = if Options.is_verbose () then msgnl(str s);;

let def_of_const t =
   match (kind_of_term t) with
    Const sp -> 
      (try (match (Global.lookup_constant sp) with
             {const_body=Some c} -> Declarations.force c
	     |_ -> assert false)
       with _ -> anomaly ("Cannot find constant "^(string_of_id (id_of_label (con_label sp)))))
    |_ -> assert false

let arg_type t =
  match kind_of_term (def_of_const t) with
      Lambda(a,b,c) -> b
    | _ -> assert false;;

let evaluable_of_global_reference r =
  match r with 
      ConstRef sp -> EvalConstRef sp
    | VarRef id -> EvalVarRef id
    | _ -> assert false;;
  
let rec (find_call_occs:
	   constr -> constr -> (constr list ->constr)*(constr  list list)) =
 fun f expr ->
  match (kind_of_term expr) with
    App (g, args) when g = f -> 
      (* For now we suppose that the function takes only one argument. *)
      (fun l -> List.hd l), [Array.to_list args]
  | App (g, args) ->
     let (largs: constr list) = Array.to_list args in
     let rec find_aux = function
	 []    -> (fun x -> []), []
       | a::tl ->
         (match find_aux tl with
          (cf, ((arg1::args) as opt_args)) -> 
           (match find_call_occs f a with
             cf2, (_ :: _ as other_args) ->
	       let len1 = List.length other_args in
                 (fun l ->
                   cf2 l::(cf (nthtl(l,len1)))), other_args@opt_args
           | _, [] -> (fun x -> a::cf x), opt_args)
	 | _, [] ->
	   (match find_call_occs f a with
	     cf, (arg1::args) -> (fun l -> cf l::tl), (arg1::args)
	   | _, [] -> (fun x -> a::tl), [])) in
     begin
       match (find_aux largs) with
	   cf, [] -> (fun l -> mkApp(g, args)), []
	 | cf, args ->
	     (fun l -> mkApp (g, Array.of_list (cf l))), args
     end
  | Rel(_) -> error "find_call_occs : Rel"
  | Var(id) -> (fun l -> expr), []
  | Meta(_) -> error "find_call_occs : Meta"
  | Evar(_) -> error "find_call_occs : Evar"
  | Sort(_)  -> error "find_call_occs : Sort"
  | Cast(_,_,_) -> error "find_call_occs : cast"
  | Prod(_,_,_) -> error "find_call_occs : Prod"
  | Lambda(_,_,_) -> error "find_call_occs : Lambda"
  | LetIn(_,_,_,_) -> error "find_call_occs : let in"
  | Const(_) -> (fun l -> expr), []
  | Ind(_) -> (fun l -> expr), []
  | Construct (_, _) -> (fun l -> expr), []
  | Case(i,t,a,r) ->
      (match find_call_occs f a with
	cf, (arg1::args) -> (fun l -> mkCase(i, t, (cf l), r)),(arg1::args)
      | _ -> (fun l -> mkCase(i, t, a, r)),[])
  | Fix(_) -> error "find_call_occs : Fix"
  | CoFix(_) -> error "find_call_occs : CoFix";;

let coq_constant s =
  Coqlib.gen_constant_in_modules "RecursiveDefinition" 
    (Coqlib.init_modules @ Coqlib.arith_modules) s;;

let constant sl s =
  constr_of_reference
    (locate (make_qualid(Names.make_dirpath 
			   (List.map id_of_string (List.rev sl)))
	       (id_of_string s)));;

let find_reference sl s =
    (locate (make_qualid(Names.make_dirpath 
			   (List.map id_of_string (List.rev sl)))
	       (id_of_string s)));;

let le_lt_SS = lazy(constant ["Recdef"] "le_lt_SS")
let le_lt_n_Sm = lazy(coq_constant "le_lt_n_Sm")

let le_trans = lazy(coq_constant "le_trans")
let le_lt_trans = lazy(coq_constant "le_lt_trans")
let lt_S_n = lazy(coq_constant "lt_S_n")
let le_n = lazy(coq_constant "le_n")
let refl_equal = lazy(coq_constant "refl_equal")
let eq = lazy(coq_constant "eq")
let ex = lazy(coq_constant "ex")
let coq_sig_ref = lazy(find_reference ["Coq";"Init";"Specif"] "sig")
let coq_sig = lazy(coq_constant "sig")
let coq_O = lazy(coq_constant "O")
let coq_S = lazy(coq_constant "S")

let gt_antirefl = lazy(coq_constant "gt_irrefl")
let lt_n_O = lazy(coq_constant "lt_n_O")
let lt_n_Sn = lazy(coq_constant "lt_n_Sn")

let f_equal = lazy(coq_constant "f_equal")
let well_founded_induction = lazy(coq_constant "well_founded_induction")
let well_founded = lazy (coq_constant "well_founded")
let acc_rel = lazy (coq_constant "Acc")
let acc_inv_id = lazy (coq_constant "Acc_inv")

let iter_ref = lazy(find_reference ["Recdef"] "iter")
let max_ref = lazy(find_reference ["Recdef"] "max")
let iter = lazy(constr_of_reference (Lazy.force iter_ref))
let max_constr = lazy(constr_of_reference (Lazy.force max_ref))

(* These are specific to experiments in nat with lt as well_founded_relation,
   but this should be made more general. *)
let nat = lazy(coq_constant "nat")
let lt = lazy(coq_constant "lt")

let  mkCaseEq a  : tactic =
     (fun g ->
(* commentaire de Yves: on pourra avoir des problemes si
   a n'est pas bien type dans l'environnement du but *)
       let type_of_a = pf_type_of g a in
       (tclTHEN (generalize [mkApp(Lazy.force refl_equal, [| type_of_a; a|])])
	  (tclTHEN 
	     (fun g2 ->
		change_in_concl None 
		  (pattern_occs [([2], a)] (pf_env g2) Evd.empty (pf_concl g2))
		  g2)
	     (simplest_case a))) g);;

let rec  mk_intros_and_continue (extra_eqn:bool)
    cont_function (eqs:constr list) (expr:constr) g =
  let ids = pf_ids_of_hyps g in
  match kind_of_term expr with
    | Lambda (n, _, b) -> 
     	let n1 = 
	  match n with
      	      Name x -> x
            | Anonymous -> ano_id
	in
     	let new_n = next_ident_away n1 ids in
	  tclTHEN (intro_using new_n)
	    (mk_intros_and_continue extra_eqn cont_function eqs 
	       (subst1 (mkVar new_n) b)) g
    | _ -> 
 	if extra_eqn then
	  let teq = next_ident_away teq_id ids in
	    tclTHEN (intro_using teq)	
	      (cont_function (mkVar teq::eqs) expr) g
	else
	  cont_function eqs expr g

let const_of_ref = function
    ConstRef kn -> kn
  | _ -> anomaly "ConstRef expected"

let simpl_iter () =
  reduce 
    (Lazy 
       {rBeta=true;rIota=true;rZeta= true; rDelta=false;
        rConst = [ EvalConstRef (const_of_ref (Lazy.force iter_ref))]})
    onConcl
    
let tclUSER l g = 
  let b,l = 
    match l with 
	None -> true,[]
      | Some l -> false,l
  in
  tclTHEN 
    (h_clear b l)
    (*     (tclIDTAC_MESSAGE (str "USER"++fnl()))  *)
    tclIDTAC
    g
    
    
let list_rewrite (rev:bool) (eqs: constr list) =
  tclREPEAT
    (List.fold_right
       (fun eq i -> tclORELSE (rewriteLR eq) i)
       (if rev then (List.rev eqs) else eqs) (tclFAIL 0 (mt())));;

let base_leaf (func:global_reference) eqs expr =
(*  let _ = msgnl (str "entering base_leaf") in *)
  (fun g ->
     let ids = ids_of_named_context (pf_hyps g) in
     let k = next_ident_away k_id ids in
     let h = next_ident_away h_id (k::ids) in
       tclTHENLIST [split (ImplicitBindings [expr]);
		    split (ImplicitBindings [Lazy.force coq_O]);
		    intro_using k;
                    tclTHENS (simplest_case (mkVar k))
                      [(tclTHEN (intro_using h) 
		     	  (tclTHEN (simplest_elim 
				      (mkApp (Lazy.force gt_antirefl,
					      [| Lazy.force coq_O |])))
		             default_auto)); tclIDTAC ];
                    intros;
		    simpl_iter();
		    unfold_constr func;
                    list_rewrite true eqs;
		    default_auto ] g);;

(* La fonction est donnee en premier argument a la 
   fonctionnelle suivie d'autres Lambdas et de Case ...
   Pour recuperer la fonction f a partir de la 
   fonctionnelle *)
let get_f foncl = 
  match (kind_of_term (def_of_const foncl)) with
      Lambda (Name f, _, _) -> f  
    |_ -> error "la fonctionnelle est mal definie";;


let rec compute_le_proofs = function
    [] -> assumption
  | a::tl ->
      tclORELSE assumption 
	(tclTHENS
	   (apply_with_bindings
	      (Lazy.force le_trans,
	       ExplicitBindings[dummy_loc,NamedHyp(id_of_string "m"),a]))
	   [compute_le_proofs tl; 
            tclORELSE (apply (Lazy.force le_n)) assumption])

let make_lt_proof pmax le_proof =
  tclTHENS
    (apply_with_bindings
       (Lazy.force le_lt_trans,
	ExplicitBindings[dummy_loc,NamedHyp(id_of_string "m"), pmax]))
    [compute_le_proofs le_proof; 
     tclTHENLIST[apply (Lazy.force lt_S_n); default_full_auto]];;

let rec list_cond_rewrite k def pmax cond_eqs le_proofs =
  match cond_eqs with
    [] -> tclIDTAC
  | eq::eqs ->
      tclTHENS
	(general_rewrite_bindings false
	 (mkVar eq,
	    ExplicitBindings[dummy_loc, NamedHyp k_id, k;
			     dummy_loc, NamedHyp def_id, def]))
	[list_cond_rewrite k def pmax eqs le_proofs;
         make_lt_proof pmax le_proofs];;


let rec introduce_all_equalities func eqs values specs bound le_proofs 
    cond_eqs =
  match specs with
    [] -> 
      fun g ->
	let ids = ids_of_named_context (pf_hyps g) in
	let s_max = mkApp(Lazy.force coq_S, [|bound|]) in
	let k = next_ident_away k_id ids in
        let ids = k::ids in
	let h' = next_ident_away (h'_id) ids in
        let ids = h'::ids in
	let def = next_ident_away def_id ids in
	tclTHENLIST
	  [split (ImplicitBindings [s_max]);
	   intro_using k;
	   tclTHENS
	     (simplest_case (mkVar k))
	     [tclTHENLIST[intro_using h';
			  simplest_elim(mkApp(Lazy.force lt_n_O,[|s_max|]));
			  default_full_auto]; tclIDTAC];
	   clear [k];
	   intros_using [k;h';def];
	   simpl_iter();
	   unfold_in_concl[([1],evaluable_of_global_reference func)];
	   list_rewrite true eqs;
           list_cond_rewrite (mkVar k) (mkVar def) bound cond_eqs le_proofs;
	   apply (Lazy.force refl_equal)] g
  | spec1::specs ->
      fun g ->
	let ids = ids_of_named_context (pf_hyps g) in
	let p = next_ident_away p_id ids in
        let ids = p::ids in
	let pmax = next_ident_away pmax_id ids in
        let ids = pmax::ids in
	let hle1 = next_ident_away hle_id ids in
        let ids = hle1::ids in
	let hle2 = next_ident_away  hle_id ids in
	let ids = hle2::ids in
	let heq = next_ident_away heq_id ids in
	tclTHENLIST
	  [simplest_elim (mkVar spec1);
	   list_rewrite true eqs;
	   intros_using [p; heq];
	   simplest_elim (mkApp(Lazy.force max_constr, [| bound; mkVar p|]));
	   intros_using [pmax; hle1; hle2];
	   introduce_all_equalities func eqs values specs 
	     (mkVar pmax) ((mkVar pmax)::le_proofs)
	     (heq::cond_eqs)] g;;
    
let string_match  s =
 try 
  for i = 0 to 3  do
    if String.get s i <> String.get "Acc_" i then failwith ""
  done;
 with Invalid_argument _ -> failwith ""
	  
let retrieve_acc_var g = 
  (* Julien: I don't like this version .... *) 
  let hyps = pf_ids_of_hyps g  in 
  map_succeed 
    (fun id -> 
       try 
	 string_match (string_of_id id);
	 id
       with _ -> failwith "")
    hyps 

let rec introduce_all_values acc_inv func context_fn
    eqs  hrec args values specs =
    (match args with
    [] -> 
      tclTHENLIST
	[split(ImplicitBindings
		 [context_fn (List.map mkVar (List.rev values))]);
	 introduce_all_equalities func eqs
	   (List.rev values) (List.rev specs) (Lazy.force coq_O) [] []]
  | arg::args ->
      (fun g ->
	let ids = ids_of_named_context (pf_hyps g) in
	let rec_res = next_ident_away rec_res_id ids in
        let ids = rec_res::ids in
	let hspec = next_ident_away hspec_id ids in
	let tac = introduce_all_values acc_inv func context_fn eqs 
	  hrec args
	  (rec_res::values)(hspec::specs) in
	(tclTHENS
	   (simplest_elim (mkApp(mkVar hrec, Array.of_list arg)))
	   [tclTHENLIST [intros_using [rec_res; hspec];
			 tac]; 
	    (tclTHENS
		 (apply (Lazy.force acc_inv))
		 [ h_assumption
		 ;
		   (fun g ->  
		      tclUSER (Some (hrec::hspec::(retrieve_acc_var g)@specs)) g
		   )
		 ]
	    )
	   ]) g)
	
    )
 
	   
let rec_leaf acc_inv hrec (func:global_reference) eqs expr =
  match find_call_occs (mkVar (get_f (constr_of_reference func))) expr with
  | context_fn, args ->
      introduce_all_values acc_inv func context_fn eqs  hrec args  [] []

let rec proveterminate acc_inv (hrec:identifier)  (* (proofs:constr list) *)
  (f_constr:constr) (func:global_reference) (eqs:constr list) (expr:constr)  =
try
(*  let _ = msgnl (str "entering proveterminate") in *)
  let v =
  match (kind_of_term expr) with
      Case (_, t, a, l) -> 
	(match find_call_occs f_constr a with
	     _,[] ->
      	       tclTHENS (fun g ->
(* 			   let _ = msgnl(str "entering mkCaseEq") in *)
			   let v = (mkCaseEq a) g in 
(* 			   let _ = msgnl (str "exiting mkCaseEq") in *)
			   v
			)
   	         (List.map (mk_intros_and_continue true
                              (proveterminate acc_inv hrec f_constr func)
                              eqs) 
	            (Array.to_list l))
	   | _, _::_ -> 
	       (
		 match find_call_occs  f_constr expr with
	     	     _,[] -> base_leaf func eqs expr
		   | _, _:: _ -> 
		       rec_leaf acc_inv hrec  func eqs expr
	       )
	)
    | _ ->  (match find_call_occs  f_constr expr with
	     	_,[] -> 
		  (try 
		    base_leaf func eqs expr
		   with e -> (msgerrnl (str "failure in base case");raise e ))
	       | _, _::_ -> 
		   rec_leaf acc_inv hrec  func eqs expr) in
  (*  let _ = msgnl(str "exiting proveterminate") in *)
  v
with e -> 
  msgerrnl(str "failure in proveterminate"); 
  raise e

let hyp_terminates func = 
  let a_arrow_b = arg_type (constr_of_reference func) in 
  let rev_args,b = decompose_prod a_arrow_b in 
  let left = 
    mkApp(Lazy.force iter, 
	  Array.of_list 
	    (lift 5 a_arrow_b:: mkRel 3::
	       constr_of_reference func::mkRel 1::
	       List.rev (list_map_i (fun i _ -> mkRel (6+i)) 0 rev_args)
	    )
	 )
  in
  let right = mkRel 5 in 
  let equality = mkApp(Lazy.force eq, [|lift 5 b; left; right|]) in
  let result = (mkProd ((Name def_id) , lift 4 a_arrow_b, equality)) in
  let cond = mkApp(Lazy.force lt, [|(mkRel 2); (mkRel 1)|]) in
  let nb_iter =
    mkApp(Lazy.force ex,
	  [|Lazy.force nat;
	    (mkLambda 
	       (Name
		  p_id,
		  Lazy.force nat, 
		  (mkProd (Name k_id, Lazy.force nat, 
			   mkArrow cond result))))|])in
  let value = mkApp(Lazy.force coq_sig, 
		    [|b;
		      (mkLambda (Name v_id, b, nb_iter))|]) in
  compose_prod rev_args value
	     

let start input_type ids args_id relation rec_arg_num rec_arg_id tac : tactic = 
  begin 
    fun g -> 
      let nargs = List.length args_id in
      let pre_rec_args = 
	List.rev_map
	  mkVar (fst (list_chop (rec_arg_num - 1) args_id)) 
      in 
      let relation = substl pre_rec_args relation in 
      let input_type = substl pre_rec_args input_type in 
      let wf_thm = next_ident_away (id_of_string ("wf_R")) ids in 
      let wf_rec_arg = 
	next_ident_away 
	  (id_of_string ("Acc_"^(string_of_id rec_arg_id)))
	  (wf_thm::ids) 
      in 
      let hrec = next_ident_away hrec_id (wf_rec_arg::wf_thm::ids) in 
      let acc_inv = 
	lazy 
	  (
	    mkApp (
	      Lazy.force acc_inv_id,
	      [|input_type;relation;mkVar rec_arg_id|]
	    )
	  )
      in
      tclTHEN
	(intros_using args_id)
	(tclTHENS
	   (observe_tac 
	      "first assert" 
	      (assert_tac 
		 true (* the assert thm is in first subgoal *)
		 (Name wf_rec_arg) 
		 (mkApp (Lazy.force acc_rel,
			 [|input_type;relation;mkVar rec_arg_id|])
		 )
	      )
	   )
	   [
	     (* accesibility proof *) 
	     tclTHENS 
	       (observe_tac 
		  "second assert" 
		  (assert_tac 
		     true 
		     (Name wf_thm)
		     (mkApp (Lazy.force well_founded,[|input_type;relation|]))
		  )
	       )
	       [ 
		 (* interactive proof of the well_foundness of the relation *) 
		 tclUSER None;
		 (* well_foundness -> Acc for any element *)
		 observe_tac 
		   "apply wf_thm" 
		   (h_apply ((mkApp(mkVar wf_thm,
				    [|mkVar rec_arg_id |])),Rawterm.NoBindings)
		   )
	       ]
	     ;
	     (* rest of the proof *)
	     tclTHENSEQ 
	       [observe_tac "generalize" 
		  (onNLastHyps (nargs+1)
		     (fun (id,_,_) -> 
			tclTHEN (generalize [mkVar id]) (h_clear false [id])
		     ))
	       ;
		observe_tac "h_fix" (h_fix (Some hrec) (nargs+1));
		intros_using args_id;
		intro_using wf_rec_arg;
		observe_tac "tac" (tac hrec acc_inv)
	       ]
	   ]
	) g  
  end



let rec instantiate_lambda t l = 
  match l with
  | [] -> t
  | a::l -> 
      let (bound_name, _, body) = destLambda t in
      instantiate_lambda (subst1 a body) l
;;


let whole_start func input_type relation rec_arg_num  : tactic = 
  begin 
    fun g -> 
      let ids = ids_of_named_context (pf_hyps g) in
      let func_body = (def_of_const (constr_of_reference func)) in
      let (f_name, _, body1) = destLambda func_body in
      let f_id =
	match f_name with
	  | Name f_id -> next_ident_away f_id ids
	  | Anonymous -> assert false 
      in
      let n_names_types,_ = decompose_lam body1 in 
      let n_ids,ids = 
	List.fold_left 
	  (fun (n_ids,ids) (n_name,_) -> 
	     match n_name with 
	       | Name id -> 
		   let n_id = next_ident_away id ids in 
		   n_id::n_ids,n_id::ids
	       | _ -> assert false
	  )
	  ([],(f_id::ids))
	  n_names_types
      in
      let rec_arg_id = List.nth n_ids (rec_arg_num - 1) in
      let expr = instantiate_lambda func_body (mkVar f_id::(List.map mkVar n_ids)) in 
      start 
	input_type
	ids
	n_ids
	relation 
	rec_arg_num
	rec_arg_id
	(fun hrec acc_inv g ->  
           (proveterminate 
	      acc_inv 
	      hrec
	      (mkVar f_id)
	      func
	      []
	      expr
	   )
	     g 
	)
	g 
  end



let com_terminate fonctional_ref input_type relation rec_arg_num
    thm_name hook =
  let (evmap, env) = Command.get_current_context() in
  start_proof thm_name
    (Global, Proof Lemma) (Environ.named_context_val env)
    (hyp_terminates fonctional_ref) hook;
  by (whole_start fonctional_ref
	input_type relation rec_arg_num )
    

let ind_of_ref = function 
  | IndRef (ind,i) -> (ind,i)
  | _ -> anomaly "IndRef expected"

let (value_f:constr list -> global_reference -> constr) =
  fun al fterm ->
    let d0 = dummy_loc in 
    let rev_x_id_l =  
      (
	List.fold_left 
	  (fun x_id_l _ -> 
	     let x_id = next_ident_away x_id x_id_l in 
	     x_id::x_id_l
	  )
	  []
	  al
      )
    in
    let fun_body = 
      RCases
	(d0,None,
	 [RApp(d0, RRef(d0,fterm), List.rev_map (fun x_id -> RVar(d0, x_id)) rev_x_id_l),
	  (Anonymous,None)],
	 [d0, [v_id], [PatCstr(d0,(ind_of_ref 
				     (Lazy.force coq_sig_ref),1),
			       [PatVar(d0, Name v_id);
				PatVar(d0, Anonymous)],
			       Anonymous)],
	  RVar(d0,v_id)])
    in
    let value =
      List.fold_left2 
	(fun acc x_id a -> 
	   RLambda
      	     (d0, Name x_id, RDynamic(d0, constr_in a),
	      acc
	     ) 
	)
	fun_body
	rev_x_id_l
	(List.rev al)
    in
    understand Evd.empty (Global.env()) value;;

let (declare_fun : identifier -> logical_kind -> constr -> global_reference) =
  fun f_id kind value ->
    let ce = {const_entry_body = value;
	      const_entry_type = None;
	      const_entry_opaque = false;
              const_entry_boxed = true} in
      ConstRef(declare_constant f_id (DefinitionEntry ce, kind));;

let (declare_f : identifier -> logical_kind -> constr list -> global_reference -> global_reference) =
  fun f_id kind input_type fterm_ref ->
    declare_fun f_id kind (value_f input_type fterm_ref);;

let start_equation (f:global_reference) (term_f:global_reference) 
  (cont_tactic:identifier list -> tactic) g =
  let ids = ids_of_named_context (pf_hyps g) in
  let terminate_constr = constr_of_reference term_f in 
  let nargs = nb_lam (def_of_const terminate_constr) in 
  let x = 
    let rec f ids n =
      if n = 0 
      then []
      else 
	let x = next_ident_away x_id ids in 
	x::f (x::ids) (n-1)
    in
    f ids nargs
  in
  tclTHENLIST [
    intros_using x;
    unfold_constr f;
    simplest_case (mkApp (terminate_constr, Array.of_list (List.map mkVar x)));
    cont_tactic x] g;;

let base_leaf_eq func eqs f_id g =
  let ids = ids_of_named_context (pf_hyps g) in
  let k = next_ident_away k_id ids in
  let p = next_ident_away p_id (k::ids) in
  let v = next_ident_away v_id (p::k::ids) in
  let heq = next_ident_away heq_id (v::p::k::ids) in
  let heq1 = next_ident_away heq_id (heq::v::p::k::ids) in
  let hex = next_ident_away hex_id (heq1::heq::v::p::k::ids) in
    tclTHENLIST [
      intros_using [v; hex]; 
      simplest_elim (mkVar hex);
      intros_using [p;heq1];
      tclTRY
	(rewriteRL 
	   (mkApp(mkVar heq1, 
		  [|mkApp (Lazy.force coq_S, [|mkVar p|]);
		    mkApp(Lazy.force lt_n_Sn, [|mkVar p|]); f_id|])));
      simpl_iter();
      unfold_in_concl [([1], evaluable_of_global_reference func)];
      list_rewrite true eqs;
      apply (Lazy.force refl_equal)] g;;

let f_S t = mkApp(Lazy.force coq_S, [|t|]);;

let rec introduce_all_values_eq cont_tac functional termine f p heq1 pmax 
    bounds le_proofs eqs ids =
  function
      [] ->
	tclTHENLIST
	  [tclTHENS
	     (general_rewrite_bindings false
		(mkVar heq1,
		 ExplicitBindings[dummy_loc,NamedHyp k_id,
				  f_S(f_S(mkVar pmax));
				  dummy_loc,NamedHyp def_id,
				  f]))
	     [tclTHENLIST
		[simpl_iter();
		 unfold_constr (reference_of_constr functional);
		 list_rewrite true eqs; cont_tac pmax le_proofs];
	      tclTHENLIST[apply (Lazy.force le_lt_SS);
			compute_le_proofs le_proofs]]]
    | arg::args ->
	let v' = next_ident_away v_id ids in
        let ids = v'::ids in
	let hex' = next_ident_away hex_id ids in
        let ids = hex'::ids in
	let p' = next_ident_away p_id ids in
        let ids = p'::ids in
	let new_pmax = next_ident_away pmax_id ids in
        let ids = pmax::ids in
	let hle1 = next_ident_away hle_id ids in
        let ids = hle1::ids in
	let hle2 = next_ident_away hle_id ids in
        let ids = hle2::ids in
	let heq = next_ident_away heq_id ids in
        let ids = heq::ids in
	let heq2 =
	  next_ident_away heq_id ids in
        let ids = heq2::ids in
	tclTHENLIST
	  [mkCaseEq(mkApp(termine, Array.of_list arg));
	   intros_using [v'; hex'];
	   simplest_elim(mkVar hex');
	   intros_using [p'];
	   simplest_elim(mkApp(Lazy.force max_constr, [|mkVar pmax;
							mkVar p'|]));
	   intros_using [new_pmax;hle1;hle2];
           introduce_all_values_eq 
              (fun pmax' le_proofs'->
		tclTHENLIST
		  [cont_tac pmax' le_proofs';
		   intros_using [heq;heq2];
		   rewriteLR (mkVar heq2);
		   tclTHENS
		     (general_rewrite_bindings false
			(mkVar heq,
			 ExplicitBindings
			   [dummy_loc, NamedHyp k_id,
			    f_S(mkVar pmax');
			    dummy_loc, NamedHyp def_id, f]))
		     [tclIDTAC;
		      tclTHENLIST
			[apply (Lazy.force le_lt_n_Sm);
			 compute_le_proofs le_proofs']]])
	     functional termine f p heq1 new_pmax
	     (p'::bounds)((mkVar pmax)::le_proofs) eqs
             (heq2::heq::hle2::hle1::new_pmax::p'::hex'::v'::ids) args]
  

let rec_leaf_eq termine f ids functional eqs expr fn args =
  let p = next_ident_away p_id ids in
  let ids = p::ids in
  let v = next_ident_away v_id ids in
  let ids = v::ids in
  let hex = next_ident_away hex_id ids in
  let ids = hex::ids in
  let heq1 = next_ident_away heq_id ids in
  let ids = heq1::ids in
  let hle1 = next_ident_away hle_id ids in
  let ids = hle1::ids in
    tclTHENLIST
      [intros_using [v;hex];
       simplest_elim (mkVar hex);
       intros_using [p;heq1];
       generalize [mkApp(Lazy.force le_n,[|mkVar p|])];
       intros_using [hle1];
       introduce_all_values_eq (fun _ _ -> tclIDTAC)
	 functional termine f p heq1 p [] [] eqs ids args;
       apply (Lazy.force refl_equal)]

let rec prove_eq (termine:constr) (f:constr)(functional:global_reference)
    (eqs:constr list)
  (expr:constr) =
  tclTRY
    (match kind_of_term expr with
      Case(_,t,a,l) ->
	(match find_call_occs f a with
	     _,[] -> 
	       tclTHENS(mkCaseEq a)(* (simplest_case a) *)
	  	 (List.map
		    (mk_intros_and_continue true
		       (prove_eq termine f functional) eqs)
		    (Array.to_list l))
	   | _,_::_ ->
               	(match find_call_occs f expr with
	     _,[] -> base_leaf_eq functional eqs f
	   | fn,args ->
	       fun g ->
		 let ids = ids_of_named_context (pf_hyps g) in
	       rec_leaf_eq termine f ids (constr_of_reference functional)
		   eqs expr fn args g))
    | _ -> 
	(match find_call_occs f expr with
	     _,[] -> base_leaf_eq functional eqs f
	   | fn,args ->
	       fun g ->
		 let ids = ids_of_named_context (pf_hyps g) in
		 rec_leaf_eq termine f ids (constr_of_reference functional)
		   eqs expr fn args g));;

let (com_eqn : identifier ->
       global_reference -> global_reference -> global_reference
	 -> constr_expr -> unit) =
  fun eq_name functional_ref f_ref terminate_ref eq ->
    let (evmap, env) = Command.get_current_context() in
    let eq_constr = interp_constr evmap env eq in
    let f_constr = (constr_of_reference f_ref) in
    (start_proof eq_name (Global, Proof Lemma)
       (Environ.named_context_val env) eq_constr (fun _ _ -> ());
     by
       (start_equation f_ref terminate_ref
	  (fun x ->
	     prove_eq 
	       (constr_of_reference terminate_ref)
	       f_constr 
	       functional_ref
	       []
	       (instantiate_lambda
	       	  (def_of_const (constr_of_reference functional_ref))
	       	  (f_constr::List.map mkVar x)
	       )
	  )
       );
     Command.save_named true);;


let recursive_definition f type_of_f r  rec_arg_num eq =
  let function_type = interp_constr Evd.empty (Global.env()) type_of_f in
  let env = push_rel (Name f,None,function_type) (Global.env()) in
  let res_vars,eq' = decompose_prod (interp_constr Evd.empty env eq) in 
  let res = 
(*     Pp.msgnl (str "res_var :=" ++ Printer.pr_lconstr_env (push_rel_context (List.map (function (x,t) -> (x,None,t)) res_vars) env) eq'); *)
(*     Pp.msgnl (str "rec_arg_num := " ++ str (string_of_int rec_arg_num)); *)
(*     Pp.msgnl (str "eq' := " ++ str (string_of_int rec_arg_num)); *)
    match kind_of_term eq' with 
      | App(e,[|_;_;eq_fix|]) -> 
		  mkLambda (Name f,function_type,compose_lam res_vars eq_fix)
      | _ -> failwith "Recursive Definition (res not eq)"
  in
  let pre_rec_args,function_type_before_rec_arg = decompose_prod_n (rec_arg_num - 1) function_type in 
  let (_, rec_arg_type, _) = destProd function_type_before_rec_arg in
  let arg_types = List.rev_map snd (fst (decompose_prod_n (List.length res_vars) function_type)) in
  let equation_id = add_suffix f "_equation" in
  let functional_id =  add_suffix f "_F" in
  let term_id = add_suffix f "_terminate" in
  let functional_ref = declare_fun functional_id (IsDefinition Definition) res in
(*   let _ = Pp.msgnl (str "res := " ++ Printer.pr_lconstr res) in  *)
  let env_with_pre_rec_args = push_rel_context(List.map (function (x,t) -> (x,None,t)) pre_rec_args) env in 
  let relation = 
    interp_constr
      Evd.empty 
      env_with_pre_rec_args
      r
  in 
(*   let _ = Pp.msgnl (str "relation := " ++ Printer.pr_lconstr_env env_with_pre_rec_args relation) in *)
  let hook _ _ =   
    let term_ref = Nametab.locate (make_short_qualid term_id) in
    let f_ref = declare_f f (IsProof Lemma) arg_types term_ref in
(*     let _ = message "start second proof" in *)
    com_eqn equation_id functional_ref f_ref term_ref eq
  in
  com_terminate functional_ref rec_arg_type relation  rec_arg_num term_id  hook 
;;

VERNAC COMMAND EXTEND RecursiveDefinition
  [ "Recursive" "Definition" ident(f) constr(type_of_f) constr(r) constr(wf)
     constr(proof) integer_opt(rec_arg_num) constr(eq) ] ->
  [ ignore(proof);ignore(wf);
    let rec_arg_num = 
      match rec_arg_num with 
	| None -> 1
	| Some n -> n 
    in
    recursive_definition f type_of_f r rec_arg_num eq ]
| [ "Recursive" "Definition" ident(f) constr(type_of_f) constr(r) constr(wf)
     "[" ne_constr_list(proof) "]" constr(eq) ] ->
  [ ignore(proof);ignore(wf);recursive_definition f type_of_f r 1 eq ]
END
