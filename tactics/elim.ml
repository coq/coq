
(* $Id$ *)

open Pp
open Util
open Names
open Generic
open Term
open Reduction
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
   Goal (y:nat){x:nat | (le O x)/\(le x y)}->(le O y).
   Intros y H.
   Decompose [sig and] H;EAuto.
   Qed.

Another example :

   Goal (A,B,C:Prop)(A/\B/\C \/ B/\C \/ C/\A) -> C.
   Intros A B C H; Decompose [and or] H; Assumption.
   Qed.
*)

let elimClauseThen tac idopt gl =
  elimination_then tac ([],[]) (VAR (out_some idopt)) gl

let rec general_decompose_clause recognizer =
  ifOnClause recognizer
    (fun cls ->
       elimClauseThen
	 (introElimAssumsThen
            (fun bas ->
               (tclTHEN (clear_clause cls)
		  (tclMAP (general_decompose_clause recognizer) 
		     (List.map in_some bas.assums)))))
	 cls)
    (fun _ -> tclIDTAC)

let rec general_decompose recognizer c gl = 
  let typc = pf_type_of gl c in  
  (tclTHENS (cut typc) 
     [(tclTHEN intro 
         (onLastHyp (general_decompose_clause recognizer)));
      (exact c)]) gl
  
let head_in l c = List.mem (List.hd (head_constr c)) l
		    
let decompose_these c l gls =
  let l = List.map (pf_global gls) l in 
  general_decompose (fun (_,t) -> head_in l t) c gls

let decompose_nonrec c gls =
  general_decompose 
    (fun (_,t) -> 
       (is_non_recursive_type  (List.hd (head_constr t))))
    c gls

let decompose_and c gls = 
  general_decompose 
    (fun (_,t) -> (is_conjunction (List.hd (head_constr t))))
    c gls

let decompose_or c gls = 
  general_decompose 
    (fun (_,t) -> (is_disjunction (List.hd (head_constr t))))
    c gls

let dyn_decompose args gl = 
  match args with 
    | [Clause ids; Command c] -> 
        decompose_these (pf_interp_constr gl c) ids gl
    | [Clause ids; Constr c]  -> 
        decompose_these c ids  gl
    | l -> bad_tactic_args "DecomposeThese" l gl
	  
let h_decompose =
  let v_decompose = hide_tactic "DecomposeThese" dyn_decompose in 
  fun ids c -> v_decompose [Clause ids; Constr c] 

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
       (fun idopt gls ->
	  let id = out_some idopt in
	  let idty = pf_type_of gls (VAR id) in
	  let fvty = global_vars idty in
	  let possible_bring_ids =
	    (List.tl (List.map out_some (nLastHyps (abs_j - abs_i) gls)))
            @bargs.assums in
	  let (ids,_) = List.fold_left 
			  (fun (bring_ids,leave_ids) cid ->
                             let cidty = pf_type_of gls (VAR cid) in
                             if not (List.mem cid leave_ids)
                             then (cid::bring_ids,leave_ids)
                             else (bring_ids,cid::leave_ids))
			  ([],fvty) possible_bring_ids 
	  in 
	  (tclTHEN (tclTHEN (bring_hyps (List.map in_some ids))
		      (clear_clauses (List.rev (List.map in_some ids))))
             (simple_elimination (VAR id))) gls))

let double_ind abs_i abs_j gls =
  let cl = pf_concl gls in 
  (tclTHEN (tclDO abs_i intro)
     (onLastHyp
       	(fun idopt ->
           elimination_then
             (introElimAssumsThen (induction_trailer abs_i abs_j))
             ([],[]) (VAR (out_some idopt))))) gls

let dyn_double_ind = function
  | [Integer i; Integer j] -> double_ind i j
  | _ -> assert false

let _ = add_tactic "DoubleInd" dyn_double_ind


(*****************************)
(* Decomposing introductions *)
(*****************************)

let rec intro_pattern p = 
  let clear_last = (tclLAST_HYP (fun c -> (clear_one (destVar c))))
  and case_last  = (tclLAST_HYP h_simplest_case) in  
  match p with
    | IdPat  id  -> intro_using_warning id
    | DisjPat l  -> (tclTHEN introf
                       (tclTHENS 
			  (tclTHEN case_last clear_last)
			  (List.map intro_pattern l)))
    | ConjPat l  -> (tclTHEN introf
                       (tclTHEN (tclTHEN  case_last clear_last)
                          (intros_pattern l)))
    | ListPat l  ->  intros_pattern l

and intros_pattern l = tclMAP intro_pattern l

let dyn_intro_pattern = function 
  | []               -> intros
  | [Intropattern p] -> intro_pattern p
  | l                -> bad_tactic_args "Elim.dyn_intro_pattern" l

let v_intro_pattern = hide_tactic "Intros" dyn_intro_pattern

let h_intro_pattern p = v_intro_pattern [Intropattern p]
