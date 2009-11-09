(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Pp
open Util
open Names
open Namegen
open Sign
open Term
open Termops
open Environ
open Reductionops
open Evd
open Typing
open Redexpr
open Tacred
open Proof_trees
open Proof_type
open Logic
open Refiner
open Tacexpr

let re_sig it gc = { it = it; sigma = gc }

(**************************************************************)
(* Operations for handling terms under a local typing context *)
(**************************************************************)

type 'a sigma   = 'a Evd.sigma;;
type validation = Proof_type.validation;;
type tactic     = Proof_type.tactic;;

let unpackage = Refiner.unpackage
let repackage = Refiner.repackage
let apply_sig_tac = Refiner.apply_sig_tac

let sig_it   = Refiner.sig_it
let project  = Refiner.project
let pf_env   = Refiner.pf_env
let pf_hyps  = Refiner.pf_hyps

let pf_concl gls = (sig_it gls).evar_concl
let pf_hyps_types gls  =
  let sign = Environ.named_context (pf_env gls) in
  List.map (fun (id,_,x) -> (id, x)) sign

let pf_nth_hyp_id gls n = let (id,c,t) = List.nth (pf_hyps gls) (n-1) in id

let pf_last_hyp gl = List.hd (pf_hyps gl)

let pf_get_hyp gls id =
  try
    Sign.lookup_named id (pf_hyps gls)
  with Not_found ->
    error ("No such hypothesis: " ^ (string_of_id id))

let pf_get_hyp_typ gls id =
  let (_,_,ty)= (pf_get_hyp gls id) in
  ty

let pf_ids_of_hyps gls = ids_of_named_context (pf_hyps gls)

let pf_get_new_id id gls =
  next_ident_away id (pf_ids_of_hyps gls)

let pf_get_new_ids ids gls =
  let avoid = pf_ids_of_hyps gls in
  List.fold_right
    (fun id acc -> (next_ident_away id (acc@avoid))::acc)
    ids []

let pf_interp_constr gls c =
  let evc = project gls in
  Constrintern.interp_constr evc (pf_env gls) c

let pf_interp_type gls c =
  let evc = project gls in
  Constrintern.interp_type evc (pf_env gls) c

let pf_global gls id = Constrintern.construct_reference (pf_hyps gls) id

let pf_parse_const gls = compose (pf_global gls) id_of_string

let pf_reduction_of_red_expr gls re c =
  (fst (reduction_of_red_expr re)) (pf_env gls) (project gls) c

let pf_apply f gls = f (pf_env gls) (project gls)
let pf_reduce = pf_apply

let pf_whd_betadeltaiota         = pf_reduce whd_betadeltaiota
let pf_whd_betadeltaiota_stack   = pf_reduce whd_betadeltaiota_stack
let pf_hnf_constr                = pf_reduce hnf_constr
let pf_red_product               = pf_reduce red_product
let pf_nf                        = pf_reduce simpl
let pf_nf_betaiota               = pf_reduce (fun _ -> nf_betaiota)
let pf_compute                   = pf_reduce compute
let pf_unfoldn ubinds            = pf_reduce (unfoldn ubinds)
let pf_type_of                   = pf_reduce type_of
let pf_get_type_of               = pf_reduce Retyping.get_type_of

let pf_conv_x                   = pf_reduce is_conv
let pf_conv_x_leq               = pf_reduce is_conv_leq
let pf_const_value              = pf_reduce (fun env _ -> constant_value env)
let pf_reduce_to_quantified_ind = pf_reduce reduce_to_quantified_ind
let pf_reduce_to_atomic_ind     = pf_reduce reduce_to_atomic_ind

let pf_hnf_type_of gls = compose (pf_whd_betadeltaiota gls) (pf_get_type_of gls)

let pf_check_type gls c1 c2 =
  ignore (pf_type_of gls (mkCast (c1, DEFAULTcast, c2)))

let pf_is_matching              = pf_apply Matching.is_matching_conv
let pf_matches                  = pf_apply Matching.matches_conv

(************************************)
(* Tactics handling a list of goals *)
(************************************)

type transformation_tactic = proof_tree -> (goal list * validation)

type validation_list = proof_tree list -> proof_tree list

type tactic_list = (goal list sigma) -> (goal list sigma) * validation_list

let first_goal         = first_goal
let goal_goal_list     = goal_goal_list
let apply_tac_list     = apply_tac_list
let then_tactic_list   = then_tactic_list
let tactic_list_tactic = tactic_list_tactic
let tclFIRSTLIST       = tclFIRSTLIST
let tclIDTAC_list      = tclIDTAC_list


(********************************************************)
(* Functions for handling the state of the proof editor *)
(********************************************************)

type pftreestate = Refiner.pftreestate

let proof_of_pftreestate    = proof_of_pftreestate
let cursor_of_pftreestate   = cursor_of_pftreestate
let is_top_pftreestate      = is_top_pftreestate
let evc_of_pftreestate      = evc_of_pftreestate
let top_goal_of_pftreestate = top_goal_of_pftreestate
let nth_goal_of_pftreestate = nth_goal_of_pftreestate
let traverse                = traverse
let solve_nth_pftreestate   = solve_nth_pftreestate
let solve_pftreestate       = solve_pftreestate
let weak_undo_pftreestate   = weak_undo_pftreestate
let mk_pftreestate          = mk_pftreestate
let extract_pftreestate     = extract_pftreestate
let extract_open_pftreestate = extract_open_pftreestate
let first_unproven          = first_unproven
let last_unproven           = last_unproven
let nth_unproven            = nth_unproven
let node_prev_unproven      = node_prev_unproven
let node_next_unproven      = node_next_unproven
let next_unproven           = next_unproven
let prev_unproven           = prev_unproven
let top_of_tree             = top_of_tree
let frontier                = frontier
let change_constraints_pftreestate = change_constraints_pftreestate


(********************************************)
(* Definition of the most primitive tactics *)
(********************************************)

let refiner = refiner

(* This does not check that the variable name is not here *)
let introduction_no_check id =
  refiner (Prim (Intro id))

let internal_cut_no_check replace id t gl =
  refiner (Prim (Cut (true,replace,id,t))) gl

let internal_cut_rev_no_check replace id t gl =
  refiner (Prim (Cut (false,replace,id,t))) gl

let refine_no_check c gl =
  refiner (Prim (Refine c)) gl

let convert_concl_no_check c sty gl =
  refiner (Prim (Convert_concl (c,sty))) gl

let convert_hyp_no_check d gl =
  refiner (Prim (Convert_hyp d)) gl

(* This does not check dependencies *)
let thin_no_check ids gl =
  if ids = [] then tclIDTAC gl else refiner (Prim (Thin ids)) gl

(* This does not check dependencies *)
let thin_body_no_check ids gl =
  if ids = [] then tclIDTAC gl else refiner (Prim (ThinBody ids)) gl

let move_hyp_no_check with_dep id1 id2 gl =
  refiner (Prim (Move (with_dep,id1,id2))) gl

let order_hyps idl gl =
  refiner (Prim (Order idl)) gl

let rec rename_hyp_no_check l gl = match l with
  | [] -> tclIDTAC gl
  | (id1,id2)::l ->
      tclTHEN (refiner (Prim (Rename (id1,id2))))
	(rename_hyp_no_check l) gl

let mutual_fix f n others j gl =
  with_check (refiner (Prim (FixRule (f,n,others,j)))) gl

let mutual_cofix f others j gl =
  with_check (refiner (Prim (Cofix (f,others,j)))) gl

(* Versions with consistency checks *)

let introduction id    = with_check (introduction_no_check id)
let internal_cut b d t = with_check (internal_cut_no_check b d t)
let internal_cut_rev b d t = with_check (internal_cut_rev_no_check b d t)
let refine c           = with_check (refine_no_check c)
let convert_concl d sty = with_check (convert_concl_no_check d sty)
let convert_hyp d      = with_check (convert_hyp_no_check d)
let thin c             = with_check (thin_no_check c)
let thin_body c        = with_check (thin_body_no_check c)
let move_hyp b id id'  = with_check (move_hyp_no_check b id id')
let rename_hyp l       = with_check (rename_hyp_no_check l)

(* Pretty-printers *)

open Pp
open Tacexpr
open Rawterm

let rec pr_list f = function
  | []   -> mt ()
  | a::l1 -> (f a) ++ pr_list f l1

let pr_gls gls =
  hov 0 (pr_evar_defs (sig_sig gls) ++ fnl () ++ db_pr_goal (sig_it gls))

let pr_glls glls =
  hov 0 (pr_evar_defs (sig_sig glls) ++ fnl () ++
         prlist_with_sep pr_fnl db_pr_goal (sig_it glls))

