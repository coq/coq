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
open Constrtypes
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
  let p = Prog_db.db_prog p in

  (* 2. typage avec effets *)
  deb_mess [< 'sTR"Prog_typing.states: Typage avec effets..."; 'fNL >];
  let env = Prog_env.empty in
  let ren = initial_renaming env in
  let p = Prog_typing.states ren env p in
  let ((_,v),_,_,_) as c = p.info.kappa in
  Prog_errors.check_for_not_mutable p.loc v;
  deb_mess (pp_type_c c);

  (* 3. propagation annotations *)
  let p = Prog_wp.propagate ren p in

  (* 4a. traduction type *)
  let ty = Monad.trad_ml_type_c ren env c in
  deb_mess (Himsg.pTERM ty);

  (* 4b. traduction terme (terme intermédiaire de type cc_term) *)
  deb_mess 
    [< 'fNL; 'sTR"Mlise.trad: Traduction program -> cc_term..."; 'fNL >];
  let cc = Mlise.trans ren p in
  let cc = Prog_red.red cc in
  deb_mess (Prog_utils.pp_cc_term cc);

  (* 5. traduction en constr *)
  deb_mess 
    [< 'fNL; 'sTR"Prog_cci.constr_of_prog: Traduction cc_term -> constr..."; 
       'fNL >];
  let c = Prog_cci.constr_of_prog cc in
  deb_mess (Himsg.pTERM c);

  (* 6. résolution implicites *)
  deb_mess [< 'fNL; 'sTR"Résolution implicites (? => Meta(n))..."; 'fNL >];
  let c =
    (ise_resolve false (Evd.mt_evd()) [] (gLOB(initial_sign())) c)._VAL in
  deb_mess (Himsg.pTERM c);

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

let mmk = make_module_marker ["#Prelude.obj"; "#Wf.obj"]

let wf_nat_pattern = put_pat mmk "(well_founded nat lt)"
let zwf_nat_pattern = put_pat mmk "(well_founded Z (Zwf ?))"
let and_pattern = put_pat mmk "(and ? ?)"
let eq_pattern = put_pat mmk "(eq ? ? ?)"

(* loop_ids: remove loop<i> hypotheses from the context, and rewrite
 * using Variant<i> hypotheses when needed. *)
 
let (loop_ids : tactic) = fun gl ->
  let rec arec hyps gl =
    let concl = pf_concl gl in 
      match hyps with
	  ([],[]) -> tclIDTAC gl
	| (id::sl,a::al) ->
	    let s = string_of_id id in
	    let n = String.length s in
	      if n >= 4 & (let su = String.sub s 0 4 in su="loop" or su="Bool")
	      then
		tclTHEN (clear [id]) (arec (sl,al)) gl
	      else if n >= 7 & String.sub s 0 7 = "Variant" then begin
		match dest_match gl (body_of_type a) eq_pattern with
		    [_; VAR phi; _] ->
		      if occur_var phi concl then
			tclTHEN (rewriteLR (VAR id)) (arec (sl,al)) gl
		      else
			arec (sl,al) gl
		  | _ -> assert false end
	      else
		arec (sl,al) gl
	| _ -> assert false
  in 
    arec (pf_hyps gl) gl

(* assumption_bis: like assumption, but also solves ... h:A/\B ... |- A 
 * (resp. B) *)

let (assumption_bis : tactic) = fun gl ->
  let concl = pf_concl gl in 
  let rec arec = function
      ([],[]) -> Std.error "No such assumption"
    | (s::sl,a::al) ->
	let a = body_of_type a in
	if pf_conv_x_leq gl a concl then 
          refine (VAR s) gl
	else if matches gl a and_pattern then
	  match dest_match gl a and_pattern with
	      [c1;c2] -> 
		if pf_conv_x_leq gl c1 concl then
		  exact (applistc (constant "proj1") [c1;c2;VAR s]) gl
		else if pf_conv_x_leq gl c2 concl then
		  exact (applistc (constant "proj2") [c1;c2;VAR s]) gl
		else
		  arec (sl,al)
	    | _ -> assert false
	else
	  arec (sl,al)
    | _ -> assert false
  in 
    arec (pf_hyps gl)

(* automatic: see above *)

let (automatic : tactic) =
  tclTHEN
    loop_ids
    (fun gl ->
       let c = pf_concl gl in
	 if matches gl c wf_nat_pattern then
	   exact (constant "lt_wf") gl
	 else if matches gl c zwf_nat_pattern then
	   let z = List.hd (dest_match gl c zwf_nat_pattern) in
	     exact (Term.applist (constant "Zwf_well_founded",[z])) gl
	 else if matches gl c and_pattern then
	   (tclORELSE assumption_bis
	      (tclTRY (tclTHEN simplest_split assumption))) gl
	 else if matches gl c eq_pattern then
	   (tclORELSE reflexivity (tclTRY assumption_bis)) gl
	 else
	   tclTRY assumption_bis gl)
      
(* [correctness s p] : string -> program -> unit
 *
 * Vernac: Correctness <string> <program>.
 *)

let correctness s p opttac =
  Misc_utils.reset_names();
  let p,c,cty,v = coqast_of_prog p in
  let sigma = Proof_trees.empty_evd in
  let sign = initial_sign() in
  let cty = Reduction.nf_betaiota cty in
  start_proof_constr s NeverDischarge cty;
  Prog_env.new_edited (id_of_string s) (v,p);
  if !debug then show_open_subgoals();
  deb_mess [< 'sTR"Prog_red.red_cci: Réduction..."; 'fNL >];
  let c = Prog_red.red_cci c in
  deb_mess [< 'sTR"APRES REDUCTION :"; 'fNL >];
  deb_mess (Himsg.pTERM c);
  let tac = (tclTHEN (Tcc.refine_tac c) automatic) in
  let tac = match opttac with 
      None -> tac
    | Some t -> tclTHEN tac t
  in
  solve_nth 1 tac;
  show_open_subgoals()


(* On redéfinit la commande "Save" pour enregistrer les nouveaux programmes *)

open Initial
open Vernacinterp

let add = Vernacinterp.overwriting_vinterp_add

let register id n =
  let id' = match n with None -> id | Some id' -> id' in
    Prog_env.register id id'

let wrap_save_named b =
  let pf_id = id_of_string (Pfedit.get_proof()) in
    save_named b;
    register pf_id None

let wrap_save_anonymous_thm b id =
  let pf_id = id_of_string (Pfedit.get_proof()) in
    save_anonymous_thm b (string_of_id id);
    register pf_id (Some id)

let wrap_save_anonymous_remark b id =
  let pf_id = id_of_string (Pfedit.get_proof()) in
    save_anonymous_remark b (string_of_id id);
    register pf_id (Some id)
;;

add("SaveNamed",
    function [] -> (fun () -> if not(is_silent()) then show_script();
		              wrap_save_named true)
    |   _  -> assert false);;

add("DefinedNamed",
    function [] -> (fun () -> if not(is_silent()) then show_script();
		              wrap_save_named false)
    |   _  -> assert false);;

add("SaveAnonymousThm",
    function [VARG_IDENTIFIER id] -> 
       (fun () -> if not(is_silent()) then show_script();
	          wrap_save_anonymous_thm true id)
    |   _  -> assert false);;

add("SaveAnonymousRmk",
    function [VARG_IDENTIFIER id] -> 
        (fun () -> if not(is_silent()) then show_script();
	            wrap_save_anonymous_remark true id)
    |   _  -> assert false);;


