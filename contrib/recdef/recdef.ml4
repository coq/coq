(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4deps: "parsing/grammar.cma" i*)

(* $Id$ *)

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
open Pretyping.Default
open Safe_typing
open Constrintern
open Hiddentac

open Equality
open Auto
open Eauto

open Genarg


let compute_renamed_type gls c = 
  rename_bound_var (pf_env gls) [] (pf_type_of gls c)

let qed () = Command.save_named true 
let defined () = Command.save_named false

let pf_get_new_ids idl g = 
  let ids = pf_ids_of_hyps g in 
  List.fold_right
    (fun id acc -> next_global_ident_away false id (acc@ids)::acc)
    idl 
    []

let pf_get_new_id id g = 
  List.hd (pf_get_new_ids [id] g)

let h_intros l = 
  tclMAP h_intro l

let do_observe_tac s tac g =
  let goal = begin (Printer.pr_goal (sig_it g)) end in
 try let v = tac g in msgnl (goal ++ fnl () ++ (str "recdef ") ++
    (str s)++(str " ")++(str "finished")); v
 with e ->
   msgnl (str "observation "++str s++str " raised exception " ++ 
	    Cerrors.explain_exn e ++ str " on goal " ++ goal ); 
   raise e;;


let observe_tac s tac g = 
  if Tacinterp.get_debug () <> Tactic_debug.DebugOff
  then do_observe_tac s tac g
  else tac g

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

let message s = if Flags.is_verbose () then msgnl(str s);;

let def_of_const t =
   match (kind_of_term t) with
    Const sp -> 
      (try (match (Global.lookup_constant sp) with
             {const_body=Some c} -> Declarations.force c
	     |_ -> assert false)
       with _ -> 
	 anomaly ("Cannot find definition of constant "^
		    (string_of_id (id_of_label (con_label sp))))
      )
     |_ -> assert false

let type_of_const t =
   match (kind_of_term t) with
    Const sp -> Typeops.type_of_constant (Global.env()) sp
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


let rank_for_arg_list h = 
  let predicate a b = 
      try List.for_all2 eq_constr a b with
        Invalid_argument _ -> false in
  let rec rank_aux i = function
  | [] -> None
  | x::tl -> if predicate h x then Some i else rank_aux (i+1) tl in
  rank_aux 0;;

let rec (find_call_occs : int -> constr -> constr -> 
  (constr list -> constr) * constr list list) =
 fun nb_lam f expr ->
  match (kind_of_term expr) with
    App (g, args) when g = f -> 
      (fun l -> List.hd l), [Array.to_list args]
  | App (g, args) ->
     let (largs: constr list) = Array.to_list args in
     let rec find_aux = function
	 []    -> (fun x -> []), []
       | a::upper_tl ->
         (match find_aux upper_tl with
          (cf, ((arg1::args) as args_for_upper_tl)) -> 
           (match find_call_occs nb_lam f a with
             cf2, (_ :: _ as other_args) ->
               let rec avoid_duplicates args =
                  match args with
                  | [] -> (fun _ -> []), []
                  | h::tl -> 
                      let recomb_tl, args_for_tl =
                          avoid_duplicates tl in
                    match rank_for_arg_list h args_for_upper_tl with
                    | None -> 
                        (fun l -> List.hd l::recomb_tl(List.tl l)),
                        h::args_for_tl
                    | Some i ->
                        (fun l -> List.nth l (i+List.length args_for_tl)::
                            recomb_tl l),
                        args_for_tl
               in
               let recombine, other_args' =
                   avoid_duplicates other_args in
	       let len1 = List.length other_args' in                   
                   (fun l -> cf2 (recombine l)::cf(nthtl(l,len1))),
                     other_args'@args_for_upper_tl
           | _, [] -> (fun x -> a::cf x), args_for_upper_tl)
	 | _, [] ->
	   (match find_call_occs nb_lam f a with
	     cf, (arg1::args) -> (fun l -> cf l::upper_tl), (arg1::args)
	   | _, [] -> (fun x -> a::upper_tl), [])) in
     begin
       match (find_aux largs) with
	   cf, [] -> (fun l -> mkApp(g, args)), []
	 | cf, args ->
	     (fun l -> mkApp (g, Array.of_list (cf l))), args
     end
  | Rel(v) -> if v > nb_lam then error "find_call_occs : Rel" else ((fun l -> expr),[])
  | Var(id) -> (fun l -> expr), []
  | Meta(_) -> error "find_call_occs : Meta"
  | Evar(_) -> error "find_call_occs : Evar"
  | Sort(_)  -> (fun l -> expr), []
  | Cast(b,_,_) -> find_call_occs nb_lam f b
  | Prod(_,_,_) -> error "find_call_occs : Prod"
  | Lambda(na,t,b) -> 
      begin
	match find_call_occs (succ nb_lam) f b with 
	  | _, [] ->  (* Lambda are authorized as long as they do not contain 
			 recursives calls *)
	      (fun l -> expr),[]
	  | _ ->  error "find_call_occs : Lambda"
      end
  | LetIn(na,v,t,b) -> 
      begin
	match find_call_occs nb_lam f v, find_call_occs (succ nb_lam) f b with 
	  | (_,[]),(_,[]) -> 
	      ((fun l -> expr), [])
	  | (_,[]),(cf,(_::_ as l)) -> 
	      ((fun  l -> mkLetIn(na,v,t,cf l)),l)
	  | (cf,(_::_ as l)),(_,[]) -> 
	      ((fun l -> mkLetIn(na,cf l,t,b)), l)
	  | _ -> error "find_call_occs : LetIn"
      end
  | Const(_) -> (fun l -> expr), []
  | Ind(_) -> (fun l -> expr), []
  | Construct (_, _) -> (fun l -> expr), []
  | Case(i,t,a,r) ->
      (match find_call_occs nb_lam f a with
	cf, (arg1::args) -> (fun l -> mkCase(i, t, (cf l), r)),(arg1::args)
      | _ -> (fun l -> expr),[])
  | Fix(_) -> error "find_call_occs : Fix"
  | CoFix(_) -> error "find_call_occs : CoFix";;

let coq_constant s =
  Coqlib.gen_constant_in_modules "RecursiveDefinition" 
    (Coqlib.init_modules @ Coqlib.arith_modules) s;;

let constant sl s =
  constr_of_global
    (locate (make_qualid(Names.make_dirpath 
			   (List.map id_of_string (List.rev sl)))
	       (id_of_string s)));;

let find_reference sl s =
    (locate (make_qualid(Names.make_dirpath 
			   (List.map id_of_string (List.rev sl)))
	       (id_of_string s)));;

let delayed_force f = f ()

let le_lt_SS = function () -> (constant ["Recdef"] "le_lt_SS")
let le_lt_n_Sm = function () -> (coq_constant "le_lt_n_Sm")

let le_trans = function () -> (coq_constant "le_trans")
let le_lt_trans = function () -> (coq_constant "le_lt_trans")
let lt_S_n = function () -> (coq_constant "lt_S_n")
let le_n = function () -> (coq_constant "le_n")
let refl_equal = function () -> (coq_constant "refl_equal")
let eq = function () -> (coq_constant "eq")
let ex = function () -> (coq_constant "ex")
let coq_sig_ref = function () -> (find_reference ["Coq";"Init";"Specif"] "sig")
let coq_sig = function () -> (coq_constant "sig")
let coq_O = function () -> (coq_constant "O")
let coq_S = function () -> (coq_constant "S")

let gt_antirefl = function () -> (coq_constant "gt_irrefl")
let lt_n_O = function () -> (coq_constant "lt_n_O")
let lt_n_Sn = function () -> (coq_constant "lt_n_Sn")

let f_equal = function () -> (coq_constant "f_equal")
let well_founded_induction = function () -> (coq_constant "well_founded_induction")
let well_founded = function () -> (coq_constant "well_founded")
let acc_rel = function () -> (coq_constant "Acc")
let acc_inv_id = function () -> (coq_constant "Acc_inv")
let well_founded_ltof = function () ->  (Coqlib.coq_constant "" ["Arith";"Wf_nat"] "well_founded_ltof")
let iter_ref = function () -> (try find_reference ["Recdef"] "iter" with Not_found -> error "module Recdef not loaded")
let max_ref = function () -> (find_reference ["Recdef"] "max")
let iter = function () -> (constr_of_global (delayed_force iter_ref))
let max_constr = function () -> (constr_of_global (delayed_force max_ref))

let ltof_ref = function  () -> (find_reference ["Coq";"Arith";"Wf_nat"] "ltof")
let coq_conj = function () -> find_reference ["Coq";"Init";"Logic"] "conj"

(* These are specific to experiments in nat with lt as well_founded_relation, *)
(*    but this should be made more general. *)
let nat = function () -> (coq_constant "nat")
let lt = function () -> (coq_constant "lt")

(* This is simply an implementation of the case_eq tactic.  this code
  should be replaced with the tactic defined in Ltac in Init/Tactics.v *)
let  mkCaseEq a  : tactic =
     (fun g ->
       let type_of_a = pf_type_of g a in
       tclTHENLIST
         [h_generalize [mkApp(delayed_force refl_equal, [| type_of_a; a|])];
          (fun g2 ->
	    change_in_concl None 
	      (pattern_occs [([-1], a)] (pf_env g2) Evd.empty (pf_concl g2))
		  g2);
	  simplest_case a] g);;

(* This is like the previous one except that it also rewrite on all
  hypotheses except the ones given in the first argument.  All the
  modified hypotheses are generalized in the process and should be
  introduced back later; the result is the pair of the tactic and the
  list of hypotheses that have been generalized and cleared. *)
let mkDestructEq :
  identifier list -> constr -> goal sigma -> tactic * identifier list =
  fun not_on_hyp expr g ->
  let hyps = pf_hyps g in 
  let to_revert = 
    Util.map_succeed 
      (fun (id,_,t) -> 
        if List.mem id not_on_hyp || not (Termops.occur_term expr t)
        then failwith "is_expr_context";
        id) hyps in
  let to_revert_constr = List.rev_map mkVar to_revert in 
  let type_of_expr = pf_type_of g expr in
  let new_hyps = mkApp(delayed_force refl_equal, [|type_of_expr; expr|])::
           to_revert_constr in
    tclTHENLIST
     [h_generalize new_hyps;
      (fun g2 ->
	change_in_concl None 
	  (pattern_occs [([-1], expr)] (pf_env g2) Evd.empty (pf_concl g2)) g2);
      simplest_case expr], to_revert

let rec  mk_intros_and_continue thin_intros (extra_eqn:bool)
    cont_function (eqs:constr list) nb_lam (expr:constr) g =
  let finalize () =  	if extra_eqn then
	  let teq = pf_get_new_id teq_id g in
	    tclTHENLIST
	      [ h_intro teq;
		thin thin_intros;
		h_intros thin_intros;
		
		tclMAP 
		  (fun eq -> tclTRY (Equality.general_rewrite_in true teq eq false)) 
		  (List.rev eqs);
		(fun g1 -> 
		   let ty_teq = pf_type_of g1 (mkVar teq) in 
		   let teq_lhs,teq_rhs = 
		     let _,args = try destApp ty_teq with _ -> Pp.msgnl (Printer.pr_goal (sig_it g1) ++ fnl () ++ pr_id teq ++ str ":" ++ Printer.pr_lconstr ty_teq); assert false in 
		     args.(1),args.(2) 
		   in
	           cont_function (mkVar teq::eqs) (replace_term teq_lhs teq_rhs expr) g1
		)
	      ]
	      g
	else
	  tclTHENSEQ[
	    thin thin_intros;
	    h_intros thin_intros;
	    cont_function eqs expr 
	  ] g
  in
  if nb_lam = 0 
  then finalize () 
  else
    match kind_of_term expr with
      | Lambda (n, _, b) -> 
     	  let n1 = 
	    match n with
      		Name x -> x
              | Anonymous -> ano_id
	  in
     	  let new_n = pf_get_new_id n1 g in
	  tclTHEN (h_intro new_n)
	    (mk_intros_and_continue thin_intros extra_eqn cont_function eqs 
	       (pred nb_lam) (subst1 (mkVar new_n) b)) g
      | _ -> 
	  assert false 
(* 	  finalize () *)
let const_of_ref = function
    ConstRef kn -> kn
  | _ -> anomaly "ConstRef expected"

let simpl_iter clause =
  reduce 
    (Lazy
       {rBeta=true;rIota=true;rZeta= true; rDelta=false;
        rConst = [ EvalConstRef (const_of_ref (delayed_force iter_ref))]})
(*     (Simpl (Some ([],mkConst (const_of_ref (delayed_force iter_ref))))) *)
    clause

(* The boolean value is_mes expresses that the termination is expressed
  using a measure function instead of a well-founded relation. *)
let tclUSER tac is_mes l g = 
  let clear_tac = 
    match l with 
      | None -> h_clear true []
      | Some l -> tclMAP (fun id -> tclTRY (h_clear false [id])) (List.rev l)
  in
  tclTHENSEQ 
    [
      clear_tac;
      if is_mes 
      then tclTHEN
             (unfold_in_concl [([], evaluable_of_global_reference
                                      (delayed_force ltof_ref))])
             tac
      else tac
    ]
    g
    
    
let list_rewrite (rev:bool) (eqs: constr list) =
  tclREPEAT
    (List.fold_right
       (fun eq i -> tclORELSE (rewriteLR eq) i)
       (if rev then (List.rev eqs) else eqs) (tclFAIL 0 (mt())));;

let base_leaf_terminate (func:global_reference) eqs expr =
(*  let _ = msgnl (str "entering base_leaf") in *)
  (fun g ->
     let k',h = 
       match pf_get_new_ids [k_id;h_id] g with 
	   [k';h] -> k',h
	 | _ -> assert false
     in
     tclTHENLIST
     [observe_tac "first split" (split (ImplicitBindings [expr]));
      observe_tac "second split"
        (split (ImplicitBindings [delayed_force coq_O]));
      observe_tac "intro k" (h_intro k');
      observe_tac "case on k" 
        (tclTHENS (simplest_case (mkVar k'))
        [(tclTHEN (h_intro h) 
          (tclTHEN (simplest_elim (mkApp (delayed_force gt_antirefl,
					 [| delayed_force coq_O |])))
            default_auto)); tclIDTAC ]);
      intros;
      simpl_iter onConcl;
      unfold_constr func;
      list_rewrite true eqs;
      default_auto] g);;

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
	   (fun g -> 
	      let le_trans = delayed_force le_trans in 
	      let t_le_trans = compute_renamed_type g le_trans in 
	      let m_id = 
		let _,_,t = destProd t_le_trans in 
		let na,_,_ = destProd t in 
		Nameops.out_name na
	      in
	      apply_with_bindings
		(le_trans,
		 ExplicitBindings[dummy_loc,NamedHyp m_id,a])
		g)
	   [compute_le_proofs tl; 
            tclORELSE (apply (delayed_force le_n)) assumption])

let make_lt_proof pmax le_proof =
  tclTHENS
    (fun g -> 
       let le_lt_trans = delayed_force le_lt_trans in 
       let t_le_lt_trans = compute_renamed_type g le_lt_trans in 
       let m_id = 
	 let _,_,t = destProd t_le_lt_trans in 
	 let na,_,_ = destProd t in 
	 Nameops.out_name na
       in
       apply_with_bindings
	 (le_lt_trans,
	  ExplicitBindings[dummy_loc,NamedHyp m_id, pmax]) g)
    [observe_tac "compute_le_proofs" (compute_le_proofs le_proof); 
     tclTHENLIST[observe_tac "lt_S_n" (apply (delayed_force lt_S_n)); default_full_auto]];;

let rec list_cond_rewrite k def pmax cond_eqs le_proofs =
  match cond_eqs with
    [] -> tclIDTAC
  | eq::eqs ->
      (fun g -> 
	 let t_eq = compute_renamed_type g (mkVar eq) in 
	 let k_id,def_id = 
	   let k_na,_,t = destProd t_eq in 
	   let _,_,t  = destProd t in 
	   let def_na,_,_ = destProd t in 
	   Nameops.out_name k_na,Nameops.out_name def_na
	 in
	 tclTHENS
	   (general_rewrite_bindings false
	      (mkVar eq,
	       ExplicitBindings[dummy_loc, NamedHyp k_id, mkVar k;
				dummy_loc, NamedHyp def_id, mkVar def]) false)
	   [list_cond_rewrite k def pmax eqs le_proofs;
            observe_tac "make_lt_proof" (make_lt_proof pmax le_proofs)] g
      ) 

let rec introduce_all_equalities func eqs values specs bound le_proofs 
    cond_eqs =
  match specs with
    [] -> 
      fun g ->
	let ids = pf_ids_of_hyps g in
	let s_max = mkApp(delayed_force coq_S, [|bound|]) in
	let k = next_global_ident_away true k_id ids in
        let ids = k::ids in
	let h' = next_global_ident_away true (h'_id) ids in
        let ids = h'::ids in
	let def = next_global_ident_away true def_id ids in
	tclTHENLIST
	  [observe_tac "introduce_all_equalities_final split" (split (ImplicitBindings [s_max]));
	   observe_tac "introduce_all_equalities_final intro k" (h_intro  k);
	   tclTHENS
	     (observe_tac "introduce_all_equalities_final case k" (simplest_case (mkVar k)))
	     [
	       tclTHENLIST[h_intro h';
			   simplest_elim(mkApp(delayed_force lt_n_O,[|s_max|]));
			   default_full_auto];
	       tclIDTAC
	     ];
	   observe_tac "clearing k " (clear [k]);
	   observe_tac "intros k h' def" (h_intros [k;h';def]);
	   observe_tac "simple_iter" (simpl_iter onConcl);
	   observe_tac "unfold functional" 
	     (unfold_in_concl[([1],evaluable_of_global_reference func)]);
	   observe_tac "rewriting equations" 
	     (list_rewrite true eqs);
           observe_tac ("cond rewrite "^(string_of_id k)) (list_cond_rewrite  k def bound cond_eqs le_proofs);
	   observe_tac "refl equal" (apply (delayed_force refl_equal))] g
  | spec1::specs ->
      fun g ->
	let ids = ids_of_named_context (pf_hyps g) in
	let p = next_global_ident_away true p_id ids in
        let ids = p::ids in
	let pmax = next_global_ident_away true pmax_id ids in
        let ids = pmax::ids in
	let hle1 = next_global_ident_away true hle_id ids in
        let ids = hle1::ids in
	let hle2 = next_global_ident_away true  hle_id ids in
	let ids = hle2::ids in
	let heq = next_global_ident_away true heq_id ids in
	tclTHENLIST
	  [simplest_elim (mkVar spec1);
	   list_rewrite true eqs;
	   h_intros [p; heq];
	   simplest_elim (mkApp(delayed_force max_constr, [| bound; mkVar p|]));
	   h_intros [pmax; hle1; hle2];
	   introduce_all_equalities func eqs values specs 
	     (mkVar pmax) ((mkVar pmax)::le_proofs)
	     (heq::cond_eqs)] g;;
    
let string_match s =
  if String.length s < 3 then failwith "string_match";
  try 
    for i = 0 to 3  do
      if String.get s i <> String.get "Acc_" i then failwith "string_match"
    done;
  with Invalid_argument _ -> failwith "string_match"
	  
let retrieve_acc_var g = 
  (* Julien: I don't like this version .... *) 
  let hyps = pf_ids_of_hyps g  in 
  map_succeed 
    (fun id -> string_match (string_of_id id);id)
    hyps 

let rec introduce_all_values concl_tac is_mes acc_inv func context_fn
    eqs  hrec args values specs =
    (match args with
    [] -> 
      tclTHENLIST
	[observe_tac "split" (split(ImplicitBindings
		 [context_fn (List.map mkVar (List.rev values))]));
	 observe_tac "introduce_all_equalities" (introduce_all_equalities func eqs
	   (List.rev values) (List.rev specs) (delayed_force coq_O) [] [])]
  | arg::args ->
      (fun g ->
	let ids = ids_of_named_context (pf_hyps g) in
	let rec_res = next_global_ident_away true rec_res_id ids in
        let ids = rec_res::ids in
	let hspec = next_global_ident_away true hspec_id ids in
	let tac =  
	  observe_tac "introduce_all_values" (
	    introduce_all_values concl_tac is_mes acc_inv func context_fn eqs
	      hrec args
	      (rec_res::values)(hspec::specs)) in
	(tclTHENS
	   (observe_tac "elim h_rec" 
	      (simplest_elim (mkApp(mkVar hrec, Array.of_list arg)))
	   )
	   [tclTHENLIST [h_intros [rec_res; hspec];
			 tac]; 
	    (tclTHENS
		 (observe_tac "acc_inv" (apply (Lazy.force acc_inv)))
		 [(* tclTHEN (tclTRY(list_rewrite true eqs)) *)
		    (observe_tac "h_assumption" h_assumption)
		 ;
		  tclTHENLIST
		    [
		      tclTRY(list_rewrite true eqs);
		      observe_tac "user proof" 
			(fun g ->  
			   tclUSER
			     concl_tac
			     is_mes
			     (Some (hrec::hspec::(retrieve_acc_var g)@specs))
			     g
			)		     
		    ]
		 ]
	    )
	   ]) g)
	
    )
 
	   
let rec_leaf_terminate concl_tac is_mes acc_inv hrec (func:global_reference) eqs expr =
  match find_call_occs 0 (mkVar (get_f (constr_of_global func))) expr with
  | context_fn, args ->
      observe_tac "introduce_all_values" 
	(introduce_all_values concl_tac is_mes acc_inv func context_fn eqs  hrec args  [] [])

let proveterminate rec_arg_id is_mes acc_inv (hrec:identifier)  
  (f_constr:constr) (func:global_reference) base_leaf rec_leaf = 
  let rec proveterminate (eqs:constr list) (expr:constr)  =
    try
      (*  let _ = msgnl (str "entering proveterminate") in *)
      let v =
        match (kind_of_term expr) with
	  Case (ci, t, a, l) -> 
	  (match find_call_occs 0 f_constr a with
	    _,[] ->
	    (fun g -> 
	      let destruct_tac, rev_to_thin_intro =
                mkDestructEq rec_arg_id a g in 
		tclTHENS destruct_tac
		  (list_map_i 
		    (fun i -> mk_intros_and_continue 
				(List.rev rev_to_thin_intro) 
				true 
				proveterminate 
				eqs
				ci.ci_cstr_nargs.(i))
		    0 (Array.to_list l)) g)
		  | _, _::_ -> 
		    (match find_call_occs  0 f_constr expr with
	     	      _,[] -> observe_tac "base_leaf" (base_leaf func eqs expr)
		    | _, _:: _ -> 
		      observe_tac "rec_leaf" 
		      (rec_leaf is_mes acc_inv hrec  func eqs expr)))
	  | _ ->
            (match find_call_occs  0 f_constr expr with
	      _,[] -> 
	      (try observe_tac "base_leaf" (base_leaf func eqs expr)
	       with e -> (msgerrnl (str "failure in base case");raise e ))
	    | _, _::_ -> 
	      observe_tac "rec_leaf"
	        (rec_leaf is_mes acc_inv hrec func eqs expr)) in
      v
    with e -> begin msgerrnl(str "failure in proveterminate"); raise e end
  in 
  proveterminate 

let hyp_terminates nb_args func = 
  let a_arrow_b = arg_type (constr_of_global func) in 
  let rev_args,b = decompose_prod_n nb_args a_arrow_b in 
  let left = 
    mkApp(delayed_force iter, 
	  Array.of_list 
	    (lift 5 a_arrow_b:: mkRel 3::
	       constr_of_global func::mkRel 1::
	       List.rev (list_map_i (fun i _ -> mkRel (6+i)) 0 rev_args)
	    )
	 )
  in
  let right = mkRel 5 in 
  let equality = mkApp(delayed_force eq, [|lift 5 b; left; right|]) in
  let result = (mkProd ((Name def_id) , lift 4 a_arrow_b, equality)) in
  let cond = mkApp(delayed_force lt, [|(mkRel 2); (mkRel 1)|]) in
  let nb_iter =
    mkApp(delayed_force ex,
	  [|delayed_force nat;
	    (mkLambda 
	       (Name
		  p_id,
		  delayed_force nat, 
		  (mkProd (Name k_id, delayed_force nat, 
			   mkArrow cond result))))|])in
  let value = mkApp(delayed_force coq_sig, 
		    [|b;
		      (mkLambda (Name v_id, b, nb_iter))|]) in
  compose_prod rev_args value
	     


let tclUSER_if_not_mes concl_tac is_mes names_to_suppress = 
  if is_mes 
  then tclCOMPLETE (h_simplest_apply (delayed_force well_founded_ltof))
  else tclUSER concl_tac is_mes names_to_suppress

let termination_proof_header is_mes input_type ids args_id relation
    rec_arg_num rec_arg_id tac wf_tac : tactic = 
  begin 
    fun g -> 
      let nargs = List.length args_id in
      let pre_rec_args = 
	List.rev_map
	  mkVar (fst (list_chop (rec_arg_num - 1) args_id)) 
      in 
      let relation = substl pre_rec_args relation in 
      let input_type = substl pre_rec_args input_type in 
      let wf_thm = next_global_ident_away true (id_of_string ("wf_R")) ids in 
      let wf_rec_arg = 
	next_global_ident_away true 
	  (id_of_string ("Acc_"^(string_of_id rec_arg_id)))
	  (wf_thm::ids) 
      in 
      let hrec = next_global_ident_away true hrec_id
	(wf_rec_arg::wf_thm::ids) in 
      let acc_inv = 
	  lazy (
	    mkApp (
	      delayed_force acc_inv_id,
	      [|input_type;relation;mkVar rec_arg_id|]
	    )
	  )
      in
      tclTHEN
	(h_intros args_id)
	(tclTHENS
	   (observe_tac 
	      "first assert" 
	      (assert_tac 
		 true (* the assert thm is in first subgoal *)
		 (Name wf_rec_arg) 
		 (mkApp (delayed_force acc_rel,
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
		     (mkApp (delayed_force well_founded,[|input_type;relation|]))
		  )
	       )
	       [ 
		 (* interactive proof that the relation is well_founded *)
		 observe_tac "wf_tac" (wf_tac is_mes (Some args_id));
		 (* this gives the accessibility argument *)
		 observe_tac 
		   "apply wf_thm" 
		   (h_simplest_apply (mkApp(mkVar wf_thm,[|mkVar rec_arg_id|]))
		   )
	       ]
	     ;
	     (* rest of the proof *)
	     tclTHENSEQ 
	       [observe_tac "generalize" 
		  (onNLastHyps (nargs+1)
		     (fun (id,_,_) -> 
			tclTHEN (h_generalize [mkVar id]) (h_clear false [id])
		     ))
	       ;
		observe_tac "h_fix" (h_fix (Some hrec) (nargs+1));
		h_intros args_id;
		h_intro wf_rec_arg;
		observe_tac "tac" (tac wf_rec_arg hrec acc_inv)
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


let whole_start (concl_tac:tactic) nb_args is_mes func input_type relation rec_arg_num  : tactic = 
  begin 
    fun g -> 
      let ids = ids_of_named_context (pf_hyps g) in
      let func_body = (def_of_const (constr_of_global func)) in
      let (f_name, _, body1) = destLambda func_body in
      let f_id =
	match f_name with
	  | Name f_id -> next_global_ident_away true f_id ids
	  | Anonymous -> anomaly "Anonymous function"
      in
      let n_names_types,_ = decompose_lam_n nb_args body1 in 
      let n_ids,ids = 
	List.fold_left 
	  (fun (n_ids,ids) (n_name,_) -> 
	     match n_name with 
	       | Name id -> 
		   let n_id = next_global_ident_away true id ids in 
		   n_id::n_ids,n_id::ids
	       | _ -> anomaly "anonymous argument"
	  )
	  ([],(f_id::ids))
	  n_names_types
      in
      let rec_arg_id = List.nth n_ids (rec_arg_num - 1) in
      let expr = instantiate_lambda func_body (mkVar f_id::(List.map mkVar n_ids)) in 
      termination_proof_header 
	is_mes
	input_type
	ids
	n_ids
	relation 
	rec_arg_num
	rec_arg_id
	(fun rec_arg_id hrec acc_inv g ->  
           (proveterminate 
	      [rec_arg_id]
	      is_mes
	      acc_inv 
	      hrec
	      (mkVar f_id)
	      func
	      base_leaf_terminate 
	      (rec_leaf_terminate concl_tac)
	      []
	      expr
	   )
	     g 
	)
	(tclUSER_if_not_mes concl_tac)
	g 
  end

let get_current_subgoals_types () = 
  let pts =  get_pftreestate () in 
  let _,subs = extract_open_pftreestate pts in 
  List.map snd ((* List.sort (fun (x,_) (y,_) -> x -y ) *)subs )

let build_and_l l = 
  let and_constr =  Coqlib.build_coq_and () in 
  let conj_constr = coq_conj () in 
  let mk_and p1 p2 = 
    Term.mkApp(and_constr,[|p1;p2|]) in 
  let rec f  = function 
    | [] -> failwith "empty list of subgoals!" 
    | [p] -> p,tclIDTAC,1 
    | p1::pl -> 
	let c,tac,nb = f pl in 
	mk_and p1 c, 
	tclTHENS
	  (apply (constr_of_global conj_constr)) 
	  [tclIDTAC;
	   tac
	  ],nb+1
  in f l


let is_rec_res id = 
  let rec_res_name = string_of_id rec_res_id   in 
  let id_name = string_of_id id in 
  try 
    String.sub id_name 0 (String.length rec_res_name) = rec_res_name 
  with _ -> false

let clear_goals = 
  let rec clear_goal t = 
    match kind_of_term t with 
      | Prod(Name id as na,t,b) -> 
	  let b' = clear_goal b in 
	  if noccurn 1 b' && (is_rec_res id) 
	  then pop b' 
	  else if b' == b then t 
	  else mkProd(na,t,b')
      | _ -> map_constr clear_goal t
  in 
  List.map clear_goal 


let build_new_goal_type () = 
  let sub_gls_types = get_current_subgoals_types () in 
  let sub_gls_types = clear_goals sub_gls_types in 
  let res = build_and_l sub_gls_types in 
  res
  

    (*
let prove_with_tcc lemma _ : tactic = 
  fun gls ->
    let hid = next_global_ident_away true h_id (pf_ids_of_hyps gls) in 
    tclTHENSEQ 
      [
	h_generalize [lemma];
	h_intro hid;
	Elim.h_decompose_and (mkVar hid); 
	gen_eauto(* default_eauto *) false (false,5) [] (Some [])
	  (* 	      default_auto *)
      ]
      gls
    *)
      
	     

let open_new_goal (build_proof:tactic -> tactic -> unit) using_lemmas ref_ goal_name (gls_type,decompose_and_tac,nb_goal)   = 
  let current_proof_name = get_current_proof_name () in
  let name = match goal_name with 
    | Some s -> s 
    | None   ->  
	try (add_suffix current_proof_name "_subproof") 
	with _ -> anomaly "open_new_goal with an unamed theorem"
  in  
  let sign = Global.named_context () in
  let sign = clear_proofs sign in
  let na = next_global_ident_away false name [] in
  if occur_existential gls_type then
    Util.error "\"abstract\" cannot handle existentials";
  let hook _ _ = 
    let opacity = 
      let na_ref = Libnames.Ident (dummy_loc,na) in 
      let na_global = Nametab.global na_ref in
      match na_global with 
	  ConstRef c -> 
	    let cb = Global.lookup_constant c in 
	    if cb.Declarations.const_opaque then true 
	    else begin  match cb.const_body with None -> true | _ -> false end 
	| _ -> anomaly "equation_lemma: not a constant"
    in
    let lemma = mkConst (Lib.make_con na) in 
    ref_ := Some lemma ;
    let lid = ref [] in 
    let h_num = ref (-1) in 
    Flags.silently Vernacentries.interp (Vernacexpr.VernacAbort None);
    build_proof 
      (  fun gls ->
	   let hid = next_global_ident_away true h_id (pf_ids_of_hyps gls) in 
	   tclTHENSEQ 
	     [
	       h_generalize [lemma];
	       h_intro hid;
	       (fun g -> 
		  let ids = pf_ids_of_hyps g in 
		  tclTHEN
		    (Elim.h_decompose_and (mkVar hid))
		    (fun g -> 
		       let ids' = pf_ids_of_hyps g in 
		       lid := List.rev (list_subtract ids' ids);
		       if !lid = [] then lid := [hid];
(* 		       list_iter_i  *)
(* 			 (fun i v ->  *)
(* 			    msgnl (str "hyp" ++ int i ++ str " " ++  *)
(* 				     Nameops.pr_id v ++ fnl () ++ fnl())) *)
(* 			      !lid; *)
		       tclIDTAC g
		    )
		    g
	       ); 
	     ] gls)
      (fun g ->
	 match kind_of_term (pf_concl g) with
	   | App(f,_) when eq_constr f (well_founded ()) ->
	       Auto.h_auto None [] (Some [])  g
	   | _ ->
	       incr h_num;
	       tclTHEN
		 (eapply_with_bindings (mkVar (List.nth !lid !h_num), NoBindings))
		 e_assumption
      		 g)
;
    Command.save_named opacity;
  in
  start_proof
    na
    (Decl_kinds.Global, Decl_kinds.Proof Decl_kinds.Lemma) 
    sign
    gls_type 
    hook ;
  by (
    fun g -> 
      tclTHEN 
	(decompose_and_tac)
	(tclORELSE 
	(tclFIRST 
	   (List.map
	      (fun c -> 
		 tclTHENSEQ
		   [intros; 
		    h_simplest_apply (interp_constr Evd.empty (Global.env()) c); 
		    tclCOMPLETE Auto.default_auto
		   ]
	      )
	      using_lemmas)
	) tclIDTAC)
	g);
  try
    by tclIDTAC; (* raises UserError _ if the proof is complete *)
    if Flags.is_verbose () then (pp (Printer.pr_open_subgoals()))
  with UserError _ -> 
    defined ()
  
;;    


let com_terminate 
    tcc_lemma_name 
    tcc_lemma_ref 
    is_mes 
    fonctional_ref
    input_type
    relation 
    rec_arg_num
    thm_name using_lemmas 
    nb_args
    hook =
  let start_proof (tac_start:tactic) (tac_end:tactic) = 
    let (evmap, env) = Command.get_current_context() in
    start_proof thm_name
      (Global, Proof Lemma) (Environ.named_context_val env)
      (hyp_terminates nb_args fonctional_ref) hook;
    by (observe_tac "starting_tac" tac_start);
    by (observe_tac "whole_start" (whole_start tac_end nb_args is_mes fonctional_ref
				   input_type relation rec_arg_num ))
    
  in
  start_proof tclIDTAC tclIDTAC;
  try 
    let new_goal_type = build_new_goal_type () in 
    open_new_goal start_proof using_lemmas tcc_lemma_ref
      (Some tcc_lemma_name)
      (new_goal_type)
  with Failure "empty list of subgoals!" -> 
    (* a non recursive function declared with measure ! *)
    defined ()
    

    

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
	     let x_id = next_global_ident_away true x_id x_id_l in 
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
				     (delayed_force coq_sig_ref),1),
			       [PatVar(d0, Name v_id);
				PatVar(d0, Anonymous)],
			       Anonymous)],
	  RVar(d0,v_id)])
    in
    let value =
      List.fold_left2 
	(fun acc x_id a -> 
	   RLambda
      	     (d0, Name x_id, Explicit, RDynamic(d0, constr_in a),
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

let rec n_x_id ids n =
  if n = 0 then []
  else let x = next_global_ident_away true x_id ids in
          x::n_x_id (x::ids) (n-1);;

let start_equation (f:global_reference) (term_f:global_reference) 
  (cont_tactic:identifier list -> tactic) g =
  let ids = pf_ids_of_hyps g in
  let terminate_constr = constr_of_global term_f in 
  let nargs = nb_prod (type_of_const terminate_constr) in 
  let x = n_x_id ids nargs in
  tclTHENLIST [
    h_intros x;
    unfold_in_concl [([], evaluable_of_global_reference f)];
    observe_tac "simplest_case" 
      (simplest_case (mkApp (terminate_constr,
                             Array.of_list (List.map mkVar x))));
    observe_tac "prove_eq" (cont_tactic x)] g;;

let base_leaf_eq func eqs f_id g =
  let ids = pf_ids_of_hyps g in
  let k = next_global_ident_away true k_id ids in
  let p = next_global_ident_away true p_id (k::ids) in
  let v = next_global_ident_away true v_id (p::k::ids) in
  let heq = next_global_ident_away true heq_id (v::p::k::ids) in
  let heq1 = next_global_ident_away true heq_id (heq::v::p::k::ids) in
  let hex = next_global_ident_away true hex_id (heq1::heq::v::p::k::ids) in
    tclTHENLIST [
      h_intros [v; hex]; 
      simplest_elim (mkVar hex);
      h_intros [p;heq1];
      tclTRY
	(rewriteRL 
	   (mkApp(mkVar heq1, 
		  [|mkApp (delayed_force coq_S, [|mkVar p|]);
		    mkApp(delayed_force lt_n_Sn, [|mkVar p|]); f_id|])));
      simpl_iter onConcl;
      tclTRY (unfold_in_concl [([1], evaluable_of_global_reference func)]);
      list_rewrite true eqs;
      apply (delayed_force refl_equal)] g;;

let f_S t = mkApp(delayed_force coq_S, [|t|]);;


let rec introduce_all_values_eq cont_tac functional termine 
    f p heq1 pmax bounds le_proofs eqs ids =
  function
      [] ->
       let heq2 = next_global_ident_away true heq_id ids in
	tclTHENLIST
	  [forward None (IntroIdentifier heq2)
             (mkApp(mkVar heq1, [|f_S(f_S(mkVar pmax))|]));
           simpl_iter (onHyp heq2);
           unfold_in_hyp [([1], evaluable_of_global_reference 
                             (global_of_constr functional))]
             (([], heq2), Tacexpr.InHyp);
           tclTHENS
	     (fun gls -> 
		let t_eq = compute_renamed_type gls (mkVar heq2) in 
		let def_id = 
		  let _,_,t  = destProd t_eq in let def_na,_,_ = destProd t in 
		  Nameops.out_name def_na
		in
		observe_tac "rewrite heq" (general_rewrite_bindings false
		(mkVar heq2,
		 ExplicitBindings[dummy_loc,NamedHyp def_id,
				  f]) false) gls)
	     [tclTHENLIST
		[observe_tac "list_rewrite" (list_rewrite true eqs);
                 cont_tac pmax le_proofs];
	      tclTHENLIST[apply (delayed_force le_lt_SS);
			compute_le_proofs le_proofs]]]
    | arg::args ->
	let v' = next_global_ident_away true v_id ids in
        let ids = v'::ids in
	let hex' = next_global_ident_away true hex_id ids in
        let ids = hex'::ids in
	let p' = next_global_ident_away true p_id ids in
        let ids = p'::ids in
	let new_pmax = next_global_ident_away true pmax_id ids in
        let ids = pmax::ids in
	let hle1 = next_global_ident_away true hle_id ids in
        let ids = hle1::ids in
	let hle2 = next_global_ident_away true hle_id ids in
        let ids = hle2::ids in
	let heq = next_global_ident_away true heq_id ids in
        let ids = heq::ids in
	let heq2 = next_global_ident_away true heq_id ids in
        let ids = heq2::ids in
	tclTHENLIST
	  [mkCaseEq(mkApp(termine, Array.of_list arg));
	   h_intros [v'; hex'];
	   simplest_elim(mkVar hex');
	   h_intros [p'];
	   simplest_elim(mkApp(delayed_force max_constr, [|mkVar pmax;
							mkVar p'|]));
	   h_intros [new_pmax;hle1;hle2];
           introduce_all_values_eq 
              (fun pmax' le_proofs'->
		tclTHENLIST
		  [cont_tac pmax' le_proofs';
		   h_intros [heq;heq2];
		   observe_tac ("rewriteRL " ^ (string_of_id heq2))
                     (tclTRY (rewriteLR (mkVar heq2)));
		   tclTRY (tclTHENS
		     ( fun g -> 
			 let t_eq = compute_renamed_type g (mkVar heq) in 
			 let k_id,def_id = 
			   let k_na,_,t = destProd t_eq in 
			   let _,_,t  = destProd t in 
			   let def_na,_,_ = destProd t in 
			   Nameops.out_name k_na,Nameops.out_name def_na
			 in
			 let c_b = (mkVar heq,
			    ExplicitBindings
			      [dummy_loc, NamedHyp k_id,
			       f_S(mkVar pmax');
			       dummy_loc, NamedHyp def_id, f])
			 in
			   observe_tac "general_rewrite_bindings" ( (general_rewrite_bindings false
								       c_b false))
			     g
		     )
		     [tclIDTAC;
		      tclTHENLIST
			[apply (delayed_force le_lt_n_Sm);
			 compute_le_proofs le_proofs']])])
	     functional termine f p heq1 new_pmax
	     (p'::bounds)((mkVar pmax)::le_proofs) eqs
             (heq2::heq::hle2::hle1::new_pmax::p'::hex'::v'::ids) args]
  

let rec_leaf_eq termine f ids functional eqs expr fn args =
  let p = next_global_ident_away true p_id ids in
  let ids = p::ids in
  let v = next_global_ident_away true v_id ids in
  let ids = v::ids in
  let hex = next_global_ident_away true hex_id ids in
  let ids = hex::ids in
  let heq1 = next_global_ident_away true heq_id ids in
  let ids = heq1::ids in
  let hle1 = next_global_ident_away true hle_id ids in
  let ids = hle1::ids in
    tclTHENLIST
      [observe_tac "intros v hex" (h_intros [v;hex]);
       simplest_elim (mkVar hex);
       h_intros [p;heq1];
       h_generalize [mkApp(delayed_force le_n,[|mkVar p|])];
       h_intros [hle1];
       observe_tac "introduce_all_values_eq" (introduce_all_values_eq
	 (fun _ _ -> tclIDTAC)
	 functional termine f p heq1 p [] [] eqs ids args);
       observe_tac "failing here" (apply (delayed_force refl_equal))]

let rec prove_eq  (termine:constr) (f:constr)(functional:global_reference)
    (eqs:constr list) (expr:constr) =
(*   tclTRY *)
  (match kind_of_term expr with
     Case(ci,t,a,l) ->
     (match find_call_occs 0 f a with
	_,[] -> 
	(fun g -> 
	  let destruct_tac,rev_to_thin_intro = mkDestructEq [] a g in 
	  tclTHENS
            destruct_tac
	    (list_map_i  
	       (fun i -> mk_intros_and_continue
                          (List.rev rev_to_thin_intro) true 
			  (prove_eq termine f functional)  
			  eqs ci.ci_cstr_nargs.(i))
	       0 (Array.to_list l)) g)
	   | _,_::_ ->
	      (match find_call_occs 0 f expr with
		_,[] -> base_leaf_eq functional eqs f
	      | fn,args ->
	        fun g ->
		  let ids = ids_of_named_context (pf_hyps g) in
	          rec_leaf_eq termine f ids
		    (constr_of_global functional)
		    eqs expr fn args g))
       | _ -> 
	   (match find_call_occs 0 f expr with
		_,[] -> base_leaf_eq functional eqs f
	      | fn,args ->
		  fun g ->
		    let ids = ids_of_named_context (pf_hyps g) in
		    observe_tac "rec_leaf_eq" (rec_leaf_eq  
		      termine f ids (constr_of_global functional)
		      eqs expr fn args) g));;

let (com_eqn : identifier ->
       global_reference -> global_reference -> global_reference
	 -> constr -> unit) =
  fun eq_name functional_ref f_ref terminate_ref equation_lemma_type ->
    let opacity = 
      match terminate_ref with 
	| ConstRef c -> 	      
	    let cb = Global.lookup_constant c in 
	    if cb.Declarations.const_opaque then true 
	    else begin match cb.const_body with None -> true | _ -> false end 
	| _ -> anomaly "terminate_lemma: not a constant"
    in 
    let (evmap, env) = Command.get_current_context() in
    let f_constr = (constr_of_global f_ref) in
    let equation_lemma_type = subst1 f_constr equation_lemma_type in
    (start_proof eq_name (Global, Proof Lemma)
       (Environ.named_context_val env) equation_lemma_type (fun _ _ -> ());
     by
       (start_equation f_ref terminate_ref
	  (fun  x ->
	     prove_eq 
	       (constr_of_global terminate_ref)
	       f_constr 
	       functional_ref
	       []
	       (instantiate_lambda
	       	  (def_of_const (constr_of_global functional_ref))
	       	  (f_constr::List.map mkVar x)
	       )
	  )
       );
(*      (try Vernacentries.interp (Vernacexpr.VernacShow Vernacexpr.ShowProof) with _ -> ()); *)
(*      Vernacentries.interp (Vernacexpr.VernacShow Vernacexpr.ShowScript); *)
     Flags.silently (fun () ->Command.save_named opacity) () ;  
(*      Pp.msgnl (str "eqn finished"); *)
    
    );;

let nf_zeta env =       
  Reductionops.clos_norm_flags  (Closure.RedFlags.mkflags [Closure.RedFlags.fZETA])
    env
    Evd.empty

let recursive_definition is_mes function_name rec_impls type_of_f r rec_arg_num eq 
    generate_induction_principle using_lemmas : unit =
  let function_type = interp_constr Evd.empty (Global.env()) type_of_f in
  let env = push_named (function_name,None,function_type) (Global.env()) in
(*   Pp.msgnl (str "function type := " ++ Printer.pr_lconstr function_type); *)
  let equation_lemma_type = interp_gen (OfType None) Evd.empty env ~impls:([],rec_impls) eq in 
(*   Pp.msgnl (Printer.pr_lconstr equation_lemma_type); *)
  let res_vars,eq' = decompose_prod equation_lemma_type in 
  let env_eq' = Environ.push_rel_context (List.map (fun (x,y) -> (x,None,y)) res_vars) env in
  let eq' = nf_zeta env_eq' eq'  in 
  let res = 
(*     Pp.msgnl (str "res_var :=" ++ Printer.pr_lconstr_env (push_rel_context (List.map (function (x,t) -> (x,None,t)) res_vars) env) eq'); *)
(*     Pp.msgnl (str "rec_arg_num := " ++ str (string_of_int rec_arg_num)); *)
(*     Pp.msgnl (str "eq' := " ++ str (string_of_int rec_arg_num)); *)
    match kind_of_term eq' with 
      | App(e,[|_;_;eq_fix|]) -> 
	  mkLambda (Name function_name,function_type,subst_var function_name (compose_lam res_vars  eq_fix))
      | _ -> failwith "Recursive Definition (res not eq)"
  in
  let pre_rec_args,function_type_before_rec_arg = decompose_prod_n (rec_arg_num - 1) function_type in 
  let (_, rec_arg_type, _) = destProd function_type_before_rec_arg in
  let arg_types = List.rev_map snd (fst (decompose_prod_n (List.length res_vars) function_type)) in
  let equation_id = add_suffix function_name "_equation" in
  let functional_id =  add_suffix function_name "_F" in
  let term_id = add_suffix function_name "_terminate" in
  let functional_ref = declare_fun functional_id (IsDefinition Definition) res in
  let env_with_pre_rec_args = push_rel_context(List.map (function (x,t) -> (x,None,t)) pre_rec_args) env in 
  let relation = 
    interp_constr
      Evd.empty 
      env_with_pre_rec_args
      r
  in 
  let tcc_lemma_name = add_suffix function_name "_tcc" in
  let tcc_lemma_constr = ref None in 
(*   let _ = Pp.msgnl (str "relation := " ++ Printer.pr_lconstr_env env_with_pre_rec_args relation) in *)
  let hook _ _ =   
    let term_ref = Nametab.locate (make_short_qualid term_id) in
    let f_ref = declare_f function_name (IsProof Lemma) arg_types term_ref in
(*     message "start second proof"; *)
    let stop = ref false in 
    begin 
      try com_eqn equation_id functional_ref f_ref term_ref (subst_var function_name equation_lemma_type)
      with e -> 
	begin 
	  if Tacinterp.get_debug () <> Tactic_debug.DebugOff
	  then pperrnl (str "Cannot create equation Lemma " ++ Cerrors.explain_exn e)
	  else anomaly "Cannot create equation Lemma"
	  ;
(* 	  ignore(try Vernacentries.vernac_reset_name (Util.dummy_loc,functional_id) with _ -> ()); *)
	  stop := true;
	end
    end;
    if not !stop
    then
      let eq_ref = Nametab.locate (make_short_qualid equation_id ) in
      let f_ref = destConst (constr_of_global f_ref) 
      and functional_ref = destConst (constr_of_global functional_ref) 
      and eq_ref = destConst (constr_of_global eq_ref) in
      generate_induction_principle f_ref tcc_lemma_constr
	functional_ref eq_ref rec_arg_num rec_arg_type (nb_prod res) relation;
      if Flags.is_verbose ()
      then msgnl (h 1 (Ppconstr.pr_id function_name ++ 
			 spc () ++ str"is defined" )++ fnl () ++ 
		    h 1 (Ppconstr.pr_id equation_id ++ 
			   spc () ++ str"is defined" )
		 )
  in
  try 
    com_terminate 
      tcc_lemma_name
      tcc_lemma_constr
      is_mes functional_ref
      rec_arg_type
      relation rec_arg_num
      term_id
      using_lemmas
      (List.length res_vars)
      hook
  with e -> 
    begin
      ignore(try Vernacentries.vernac_reset_name (Util.dummy_loc,functional_id) with _ -> ());
(*       anomaly "Cannot create termination Lemma" *)
      raise e
    end


VERNAC COMMAND EXTEND RecursiveDefinition
  [ "Recursive" "Definition" ident(f) constr(type_of_f) constr(r) constr(wf)
     constr(proof) integer_opt(rec_arg_num) constr(eq) ] ->
  [ 
    warning "Recursive Definition is obsolete. Use Function instead";
    ignore(proof);ignore(wf);
    let rec_arg_num = 
      match rec_arg_num with 
	| None -> 1
	| Some n -> n 
    in
    recursive_definition false f [] type_of_f r rec_arg_num eq (fun _ _ _ _ _  _ _ _ -> ()) []]
| [ "Recursive" "Definition" ident(f) constr(type_of_f) constr(r) constr(wf)
     "[" ne_constr_list(proof) "]" constr(eq) ] ->
  [ ignore(proof);ignore(wf);recursive_definition false f [] type_of_f r 1 eq  (fun  _ _  _ _ _ _ _ _ -> ()) []]
END



