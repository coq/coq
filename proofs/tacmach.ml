(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util
open Names
open Namegen
open Term
open Termops
open Environ
open Reductionops
open Evd
open Typing
open Redexpr
open Tacred
open Proof_type
open Logic
open Refiner

let re_sig it  gc = { it = it; sigma = gc; }

(**************************************************************)
(* Operations for handling terms under a local typing context *)
(**************************************************************)

type 'a sigma   = 'a Evd.sigma;;
type tactic     = Proof_type.tactic;;

let unpackage = Refiner.unpackage
let repackage = Refiner.repackage
let apply_sig_tac = Refiner.apply_sig_tac

let sig_it   = Refiner.sig_it
let project  = Refiner.project
let pf_env   = Refiner.pf_env
let pf_hyps  = Refiner.pf_hyps

let pf_concl gls = Goal.V82.concl (project gls) (sig_it gls)
let pf_hyps_types gls  =
  let sign = Environ.named_context (pf_env gls) in
  List.map (fun (id,_,x) -> (id, x)) sign

let pf_nth_hyp_id gls n = let (id,c,t) = List.nth (pf_hyps gls) (n-1) in id

let pf_last_hyp gl = List.hd (pf_hyps gl)

let pf_get_hyp gls id =
  try
    Context.lookup_named id (pf_hyps gls)
  with Not_found ->
    raise (RefinerError (NoSuchHyp id))

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

let pf_global gls id = Constrintern.construct_reference (pf_hyps gls) id

let pf_reduction_of_red_expr gls re c =
  (fst (reduction_of_red_expr (pf_env gls) re)) (pf_env gls) (project gls) c

let pf_apply f gls = f (pf_env gls) (project gls)
let pf_reduce = pf_apply

let pf_whd_betadeltaiota         = pf_reduce whd_betadeltaiota
let pf_hnf_constr                = pf_reduce hnf_constr
let pf_nf                        = pf_reduce simpl
let pf_nf_betaiota               = pf_reduce (fun _ -> nf_betaiota)
let pf_compute                   = pf_reduce compute
let pf_unfoldn ubinds            = pf_reduce (unfoldn ubinds)
let pf_type_of                   = pf_reduce type_of
let pf_get_type_of               = pf_reduce Retyping.get_type_of

let pf_conv_x                   = pf_reduce is_conv
let pf_conv_x_leq               = pf_reduce is_conv_leq
let pf_reduce_to_quantified_ind = pf_reduce reduce_to_quantified_ind
let pf_reduce_to_atomic_ind     = pf_reduce reduce_to_atomic_ind

let pf_hnf_type_of gls = compose (pf_whd_betadeltaiota gls) (pf_get_type_of gls)

let pf_is_matching              = pf_apply ConstrMatching.is_matching_conv
let pf_matches                  = pf_apply ConstrMatching.matches_conv

(********************************************)
(* Definition of the most primitive tactics *)
(********************************************)

let refiner = refiner

(* This does not check that the variable name is not here *)
let introduction_no_check id =
  refiner (Intro id)

let internal_cut_no_check replace id t gl =
  refiner (Cut (true,replace,id,t)) gl

let internal_cut_rev_no_check replace id t gl =
  refiner (Cut (false,replace,id,t)) gl

let refine_no_check c gl =
  refiner (Refine c) gl

let convert_concl_no_check c sty gl =
  refiner (Convert_concl (c,sty)) gl

let convert_hyp_no_check d gl =
  refiner (Convert_hyp d) gl

(* This does not check dependencies *)
let thin_no_check ids gl =
  if List.is_empty ids then tclIDTAC gl else refiner (Thin ids) gl

(* This does not check dependencies *)
let thin_body_no_check ids gl =
  if List.is_empty ids then tclIDTAC gl else refiner (ThinBody ids) gl

let move_hyp_no_check with_dep id1 id2 gl =
  refiner (Move (with_dep,id1,id2)) gl

let rec rename_hyp_no_check l gl = match l with
  | [] -> tclIDTAC gl
  | (id1,id2)::l ->
      tclTHEN (refiner (Rename (id1,id2)))
	(rename_hyp_no_check l) gl

let mutual_fix f n others j gl =
  with_check (refiner (FixRule (f,n,others,j))) gl

let mutual_cofix f others j gl =
  with_check (refiner (Cofix (f,others,j))) gl

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

let db_pr_goal sigma g =
  let env = Goal.V82.env sigma g in
  let penv = print_named_context env in
  let pc = print_constr_env env (Goal.V82.concl sigma g) in
  str"  " ++ hv 0 (penv ++ fnl () ++
                   str "============================" ++ fnl ()  ++
                   str" "  ++ pc) ++ fnl ()

let pr_gls gls =
  hov 0 (pr_evar_map (Some 2) (sig_sig gls) ++ fnl () ++ db_pr_goal (project gls) (sig_it gls))

let pr_glls glls =
  hov 0 (pr_evar_map (Some 2) (sig_sig glls) ++ fnl () ++
         prlist_with_sep fnl (db_pr_goal (project glls)) (sig_it glls))

(* Variants of [Tacmach] functions built with the new proof engine *)
module New = struct

  let pf_apply f gl =
    f (Proofview.Goal.env gl) (Proofview.Goal.sigma gl)

  let of_old f gl =
    f { Evd.it = Proofview.Goal.goal gl ; sigma = Proofview.Goal.sigma gl }

  let pf_global id gl =
    (** We only check for the existence of an [id] in [hyps] *)
    let gl = Proofview.Goal.assume gl in
    let hyps = Proofview.Goal.hyps gl in
    Constrintern.construct_reference hyps id

  let pf_env = Proofview.Goal.env

  let pf_type_of gl t =
    pf_apply type_of gl t

  let pf_conv_x gl t1 t2 = pf_apply is_conv gl t1 t2

  let pf_ids_of_hyps gl =
    (** We only get the identifiers in [hyps] *)
    let gl = Proofview.Goal.assume gl in
    let hyps = Proofview.Goal.hyps gl in
    ids_of_named_context hyps

  let pf_get_new_id id gl =
    let ids = pf_ids_of_hyps gl in
    next_ident_away id ids

  let pf_get_hyp id gl =
    let hyps = Proofview.Goal.hyps gl in
    let sign =
      try Context.lookup_named id hyps
      with Not_found -> raise (RefinerError (NoSuchHyp id))
    in
    sign

  let pf_get_hyp_typ id gl =
    let (_,_,ty) = pf_get_hyp id gl in
    ty

  let pf_hyps_types gl =
    let env = Proofview.Goal.env gl in
    let sign = Environ.named_context env in
    List.map (fun (id,_,x) -> (id, x)) sign

  let pf_last_hyp gl =
    let hyps = Proofview.Goal.hyps gl in
    List.hd hyps

  let pf_nf_concl (gl : [ `LZ ] Proofview.Goal.t) =
    (** We normalize the conclusion just after *)
    let gl = Proofview.Goal.assume gl in
    let concl = Proofview.Goal.concl gl in
    let sigma = Proofview.Goal.sigma gl in
    nf_evar sigma concl

  let pf_whd_betadeltaiota gl t = pf_apply whd_betadeltaiota gl t

  let pf_get_type_of gl t = pf_apply Retyping.get_type_of gl t

  let pf_reduce_to_quantified_ind gl t =
    pf_apply reduce_to_quantified_ind gl t

  let pf_hnf_constr gl t = pf_apply hnf_constr gl t
  let pf_hnf_type_of gl t =
    pf_whd_betadeltaiota gl (pf_get_type_of gl t)

  let pf_matches gl pat t = pf_apply ConstrMatching.matches_conv gl pat t

  let pf_whd_betadeltaiota gl t = pf_apply whd_betadeltaiota gl t
  let pf_compute gl t = pf_apply compute gl t

  let pf_nf_evar gl t = nf_evar (Proofview.Goal.sigma gl) t

end
