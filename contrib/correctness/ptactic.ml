(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id$ *)

open Pp
open Names
open Term
open Pfedit
open Vernacentries

open Pmisc
open Putil
open Past
open Penv
open Prename
open Peffect
open Pmonad


(* [coqast_of_prog: program -> constr * constr]
 * Traduction d'un programme impératif en un but (second constr)
 * et un terme de preuve partiel pour ce but (premier constr)
 *)

let coqast_of_prog p =
  (* 1. db : séparation dB/var/const *)
  let p = Pdb.db_prog p in

  (* 2. typage avec effets *)
  deb_mess [< 'sTR"Ptyping.states: Typage avec effets..."; 'fNL >];
  let env = Penv.empty in
  let ren = initial_renaming env in
  let p = Ptyping.states ren env p in
  let ((_,v),_,_,_) as c = p.info.kappa in
  Perror.check_for_not_mutable p.loc v;
  deb_mess (pp_type_c c);

  (* 3. propagation annotations *)
  let p = Pwp.propagate ren p in

  (* 4a. traduction type *)
  let ty = Pmonad.trad_ml_type_c ren env c in
  deb_mess (Printer.prterm ty);

  (* 4b. traduction terme (terme intermédiaire de type cc_term) *)
  deb_mess 
    [< 'fNL; 'sTR"Mlise.trad: Traduction program -> cc_term..."; 'fNL >];
  let cc = Pmlize.trans ren p in
  let cc = Pred.red cc in
  deb_mess (Putil.pp_cc_term cc);

  (* 5. traduction en constr *)
  deb_mess 
    [< 'fNL; 'sTR"Pcic.constr_of_prog: Traduction cc_term -> constr..."; 
       'fNL >];
  let c = Pcic.constr_of_prog cc in
  deb_mess (Printer.prterm c);

  (* 6. résolution implicites *)
  deb_mess [< 'fNL; 'sTR"Résolution implicites (? => Meta(n))..."; 'fNL >];
  let c = c in
  (*i WAS
    (ise_resolve false (Evd.mt_evd()) [] (gLOB(initial_sign())) c)._VAL in
  i*)
  deb_mess (Printer.prterm c);

  p,c,ty,v

(* [automatic : tactic]
 * 
 * Certains buts engendrés par "correctness" (ci-dessous)
 * sont réellement triviaux. On peut les résoudre aisément, sans pour autant
 * tomber dans la solution trop lourde qui consiste à faire "; Auto."
 *
 * Cette tactique fait les choses suivantes :
 *   o  elle élimine les hypothèses de nom loop<i>
 *   o  sur  G |- (well_founded nat lt) ==> Exact lt_wf.  
 *   o  sur  G |- (well_founded Z (Zwf c)) ==> Exact (Zwf_well_founded c)
 *   o  sur  G |- e = e' ==> Reflexivity.  (arg. de decr. des boucles)
 *                           sinon Try Assumption.
 *   o  sur  G |- P /\ Q ==> Try (Split; Assumption). (sortie de boucle)
 *   o  sinon, Try AssumptionBis (= Assumption + décomposition /\ dans hyp.)
 *             (pour entrée dans corps de boucle par ex.)
 *)

open Pattern
open Tacmach
open Tactics
open Tacticals
open Equality

let coq_constant d s = make_path ("Coq" :: d) (id_of_string s) CCI

let nat = IndRef (coq_constant ["Init";"Datatypes"] "nat", 0)
let lt = ConstRef (coq_constant ["Init";"Peano"] "lt")
let well_founded = ConstRef (coq_constant ["Init";"Wf"] "well_founded")
let z = IndRef (coq_constant ["Init";"fast_integer"] "Z", 0)
let and_ = IndRef (coq_constant ["Init";"Logic"] "and", 0)
let eq = IndRef (coq_constant ["Init";"Logic"] "eq", 0)

(* ["(well_founded nat lt)"] *)
let wf_nat_pattern = 
  PApp (PRef well_founded, [| PRef nat; PRef lt |])
(* ["((well_founded Z (Zwf ?))"] *)
let wf_z_pattern = 
  let zwf = ConstRef (coq_constant ["correctness";"Zwf"] "Zwf") in
  PApp (PRef well_founded, [| PRef z; PApp (PRef zwf, [| PMeta None |]) |])
(* ["(and ? ?)"] *)
let and_pattern = 
  PApp (PRef and_, [| PMeta None; PMeta None |])
(* ["(eq ? ? ?)"] *)
let eq_pattern = 
  PApp (PRef eq, [| PMeta None; PMeta None; PMeta None |])

(* loop_ids: remove loop<i> hypotheses from the context, and rewrite
 * using Variant<i> hypotheses when needed. *)
 
let (loop_ids : tactic) = fun gl ->
  let rec arec hyps gl =
    let concl = pf_concl gl in 
    match hyps with
      | [] -> tclIDTAC gl
      | (id,a) :: al ->
	  let s = string_of_id id in
	  let n = String.length s in
	  if n >= 4 & (let su = String.sub s 0 4 in su="loop" or su="Bool")
	  then
	    tclTHEN (clear [id]) (arec al) gl
	  else if n >= 7 & String.sub s 0 7 = "Variant" then begin
	    match pf_matches gl eq_pattern (body_of_type a) with
	      | [_; _,varphi; _] when isVar varphi ->
		  let phi = destVar varphi in
		  if occur_var phi concl then
		    tclTHEN (rewriteLR (mkVar id)) (arec al) gl
		  else
		    arec al gl
	      | _ -> assert false end
	  else
	    arec al gl
  in 
  arec (pf_hyps_types gl) gl

(* assumption_bis: like assumption, but also solves ... h:A/\B ... |- A 
 * (resp. B) *)

let (assumption_bis : tactic) = fun gl ->
  let concl = pf_concl gl in 
  let rec arec = function
    | [] -> Util.error "No such assumption"
    | (s,a) :: al ->
	let a = body_of_type a in
	if pf_conv_x_leq gl a concl then 
          refine (mkVar s) gl
	else if pf_is_matching gl and_pattern a then
	  match pf_matches gl and_pattern a with
	    | [_,c1; _,c2] -> 
		if pf_conv_x_leq gl c1 concl then
		  exact_check (applistc (constant "proj1") [c1;c2;mkVar s]) gl
		else if pf_conv_x_leq gl c2 concl then
		  exact_check (applistc (constant "proj2") [c1;c2;mkVar s]) gl
		else
		  arec al
	    | _ -> assert false
	else
	  arec al
  in 
  arec (pf_hyps_types gl)

(* automatic: see above *)

let (automatic : tactic) =
  tclTHEN
    loop_ids
    (fun gl ->
       let c = pf_concl gl in
	 if pf_is_matching gl wf_nat_pattern c then
	   exact_check (constant "lt_wf") gl
	 else if pf_is_matching gl wf_z_pattern c then
	   let (_,z) = List.hd (pf_matches gl wf_z_pattern c) in
	   exact_check (Term.applist (constant "Zwf_well_founded",[z])) gl
	 else if pf_is_matching gl and_pattern c then
	   (tclORELSE assumption_bis
	      (tclTRY (tclTHEN simplest_split assumption))) gl
	 else if pf_is_matching gl eq_pattern c then
	   (tclORELSE reflexivity (tclTRY assumption_bis)) gl
	 else
	   tclTRY assumption_bis gl)
      
(* [correctness s p] : string -> program -> tactic option -> unit
 *
 * Vernac: Correctness <string> <program> [; <tactic>].
 *)

let correctness s p opttac =
  Pmisc.reset_names();
  let p,c,cty,v = coqast_of_prog p in
  let env = Global.env () in
  let sign = Global.named_context () in
  let sigma = Evd.empty in
  let cty = Reduction.nf_betaiota env sigma cty in
  let id = id_of_string s in 
  start_proof id Declare.NeverDischarge sign cty;
  Penv.new_edited id (v,p);
  if !debug then show_open_subgoals();
  deb_mess [< 'sTR"Pred.red_cci: Réduction..."; 'fNL >];
  let c = Pred.red_cci c in
  deb_mess [< 'sTR"APRES REDUCTION :"; 'fNL >];
  deb_mess (Printer.prterm c);
  let oc = [],c in (* TODO: quid des existentielles ici *)
  let tac = (tclTHEN (Refine.refine_tac oc) automatic) in
  let tac = match opttac with 
    | None -> tac
    | Some t -> tclTHEN tac t
  in
  solve_nth 1 tac;
  show_open_subgoals()


(* On redéfinit la commande "Save" pour enregistrer les nouveaux programmes *)

open Vernacinterp

let add = Vernacinterp.overwriting_vinterp_add

let register id n =
  let id' = match n with None -> id | Some id' -> id' in
  Penv.register id id'

let wrap_save_named b =
  let pf_id = Pfedit.get_current_proof_name () in
  Command.save_named b;
  register pf_id None

let wrap_save_anonymous_thm b id =
  let pf_id = Pfedit.get_current_proof_name () in
  Command.save_anonymous_thm b (string_of_id id);
  register pf_id (Some id)

let wrap_save_anonymous_remark b id =
  let pf_id = Pfedit.get_current_proof_name () in
  Command.save_anonymous_remark b (string_of_id id);
  register pf_id (Some id)

let _ = add "SaveNamed"
    (function [] -> (fun () -> if not(Options.is_silent()) then show_script();
		              wrap_save_named true)
    |   _  -> assert false)

let _ = add "DefinedNamed"
    (function [] -> (fun () -> if not(Options.is_silent()) then show_script();
		              wrap_save_named false)
    |   _  -> assert false)

let _ = add "SaveAnonymousThm"
    (function [VARG_IDENTIFIER id] -> 
       (fun () -> if not(Options.is_silent()) then show_script();
	          wrap_save_anonymous_thm true id)
    |   _  -> assert false)

let _ = add "SaveAnonymousRmk"
    (function [VARG_IDENTIFIER id] -> 
        (fun () -> if not(Options.is_silent()) then show_script();
	            wrap_save_anonymous_remark true id)
    |   _  -> assert false)
