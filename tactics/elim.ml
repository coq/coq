(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Pp
open Util
open Names
open Term
open Termops
open Environ
open Libnames
open Reduction
open Inductiveops
open Proof_type
open Clenv
open Hipattern
open Tacmach
open Tacticals
open Tactics
open Hiddentac

let introElimAssumsThen tac ba =
  let nassums = 
    List.fold_left 
      (fun acc b -> if b then acc+2 else acc+1) 
      0 ba.branchsign 
  in 
  let introElimAssums = tclDO nassums intro in 
  (tclTHEN introElimAssums (elim_on_ba tac ba))

let introCaseAssumsThen tac ba =
  let case_thin_sign =
    List.flatten 
      (List.map 
	 (function b -> if b then [false;true] else [false]) 
	 ba.branchsign) 
  in 
  let introCaseAssums = intros_clearing case_thin_sign in
  (tclTHEN introCaseAssums (case_on_ba tac ba))

(* The following tactic Decompose repeatedly applies the
   elimination(s) rule(s) of the types satisfying the predicate
   ``recognizer'' onto a certain hypothesis. For example :

Require Elim.
Require Le.
   Goal (y:nat){x:nat | (le O x)/\(le x y)}->{x:nat | (le O x)}.
   Intros y H.
   Decompose [sig and] H;EAuto.
   Qed.

Another example :

   Goal (A,B,C:Prop)(A/\B/\C \/ B/\C \/ C/\A) -> C.
   Intros A B C H; Decompose [and or] H; Assumption.
   Qed.
*)

let elimHypThen tac id gl =
  elimination_then tac ([],[]) (mkVar id) gl

let rec general_decompose_on_hyp recognizer =
  ifOnHyp recognizer (general_decompose recognizer) (fun _ -> tclIDTAC)

and general_decompose recognizer id =
  elimHypThen
    (introElimAssumsThen
       (fun bas ->
	  tclTHEN (clear [id])
	    (tclMAP (general_decompose_on_hyp recognizer)
               (ids_of_named_context bas.assums))))
    id

(* Faudrait ajouter un COMPLETE pour que l'hypothèse créée ne reste
   pas si aucune élimination n'est possible *)

(* Meilleures stratégies mais perte de compatibilité *)
let tmphyp_name = id_of_string "_TmpHyp"
let up_to_delta = ref false (* true *)

let general_decompose recognizer c gl = 
  let typc = pf_type_of gl c in  
  (tclTHENS (cut typc) 
    [tclTHEN (intro_using tmphyp_name)
      (onLastHyp
	(ifOnHyp recognizer (general_decompose recognizer)
          (fun id -> clear [id])));
     exact_no_check c]) gl

let head_in gls indl t =
  try
    let ity,_ =
      if !up_to_delta
      then find_mrectype (pf_env gls) (project gls) t
      else extract_mrectype t
    in List.mem ity indl
  with Not_found -> false
       
let inductive_of_qualid gls qid =
  let c = 
    try Declare.construct_qualified_reference qid
    with Not_found -> Nametab.error_global_not_found qid
  in
  match kind_of_term c with
    | Ind ity -> ity
    | _ ->
	errorlabstrm "Decompose"
	  (pr_qualid qid ++ str " is not an inductive type")

let decompose_these c l gls =
  let indl = List.map (inductive_of_qualid gls) l in 
  general_decompose (fun (_,t) -> head_in gls indl t) c gls

let decompose_nonrec c gls =
  general_decompose 
    (fun (_,t) -> is_non_recursive_type t)
    c gls

let decompose_and c gls = 
  general_decompose 
    (fun (_,t) -> is_conjunction t)
    c gls

let decompose_or c gls = 
  general_decompose 
    (fun (_,t) -> is_disjunction t)
    c gls

let dyn_decompose args gl =
  let out_qualid = function
    | Qualid qid -> qid
    | l -> bad_tactic_args "DecomposeThese" [l] gl in
  match args with 
    | Command c :: ids -> 
        decompose_these (pf_interp_constr gl c) (List.map out_qualid ids) gl
    | Constr c :: ids  -> 
	decompose_these c (List.map out_qualid ids) gl
    | l -> bad_tactic_args "DecomposeThese" l gl
	  
let h_decompose =
  let v_decompose = hide_tactic "DecomposeThese" dyn_decompose in 
  fun ids c ->
    v_decompose 
      (Constr c :: List.map (fun x -> Qualid (qualid_of_sp x)) ids)

let vernac_decompose_and = 
  hide_constr_tactic "DecomposeAnd" decompose_and
let vernac_decompose_or  = 
  hide_constr_tactic  "DecomposeOr"  decompose_or

(* The tactic Double performs a double induction *)

let simple_elimination c gls =
  simple_elimination_then (fun _ -> tclIDTAC) c gls

let induction_trailer abs_i abs_j bargs =
  tclTHEN 
    (tclDO (abs_j - abs_i) intro)
    (onLastHyp
       (fun id gls ->
	  let idty = pf_type_of gls (mkVar id) in
	  let fvty = global_vars (pf_env gls) idty in
	  let possible_bring_hyps =
	    (List.tl (nLastHyps (abs_j - abs_i) gls)) @ bargs.assums
          in
	  let (hyps,_) =
            List.fold_left 
	      (fun (bring_ids,leave_ids) (cid,_,cidty as d) ->
                 if not (List.mem cid leave_ids)
                 then (d::bring_ids,leave_ids)
                 else (bring_ids,cid::leave_ids))
	      ([],fvty) possible_bring_hyps
	  in
          let ids = List.rev (ids_of_named_context hyps) in
	  (tclTHENSEQ
            [bring_hyps hyps; clear ids; simple_elimination (mkVar id)])
          gls))

let double_ind abs_i abs_j gls =
  let cl = pf_concl gls in 
  (tclTHEN (tclDO abs_i intro)
     (onLastHyp
       	(fun id ->
           elimination_then
             (introElimAssumsThen (induction_trailer abs_i abs_j))
             ([],[]) (mkVar id)))) gls

let dyn_double_ind = function
  | [Integer i; Integer j] -> double_ind i j
  | _ -> assert false

let _ = add_tactic "DoubleInd" dyn_double_ind


(*****************************)
(* Decomposing introductions *)
(*****************************)

let rec intro_pattern p = 
  let clear_last = tclLAST_HYP (fun c -> (clear [destVar c]))
  and case_last  = tclLAST_HYP h_simplest_case in  
  match p with
    | WildPat    -> tclTHEN intro clear_last
    | IdPat  id  -> intro_mustbe_force id
    | DisjPat l  -> tclTHEN introf
                       (tclTHENS 
			  (tclTHEN case_last clear_last)
			  (List.map intro_pattern l))
    | ConjPat l  ->
        tclTHENSEQ [introf; case_last; clear_last; intros_pattern l]
    | ListPat l  ->  intros_pattern l

and intros_pattern l = tclMAP intro_pattern l

let dyn_intro_pattern = function 
  | []               -> intros
  | [Intropattern p] -> intro_pattern p
  | l                -> bad_tactic_args "Elim.dyn_intro_pattern" l

let v_intro_pattern = hide_tactic "Intros" dyn_intro_pattern

let h_intro_pattern p = v_intro_pattern [Intropattern p]
