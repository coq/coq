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
open Options
open Names
open Term
open Pretyping
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
  deb_mess [< 'sTR"Ptyping.states: Typing with effects..."; 'fNL >];
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
    [< 'fNL; 'sTR"Mlize.trad: Translation program -> cc_term..."; 'fNL >];
  let cc = Pmlize.trans ren p in
  let cc = Pred.red cc in
  deb_mess (Putil.pp_cc_term cc);

  (* 5. traduction en constr *)
  deb_mess 
    [< 'fNL; 'sTR"Pcic.constr_of_prog: Translation cc_term -> rawconstr..."; 
       'fNL >];
  let r = Pcic.rawconstr_of_prog cc in
  deb_mess (Printer.pr_rawterm r);

  (* 6. résolution implicites *)
  deb_mess [< 'fNL; 'sTR"Resolution implicits (? => Meta(n))..."; 'fNL >];
  let oc = understand_gen_tcc Evd.empty (Global.env()) [] [] None r in
  deb_mess (Printer.prterm (snd oc));

  p,oc,ty,v

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

let nat = IndRef (coq_constant ["Init";"Datatypes"] "nat", 0)
let lt = ConstRef (coq_constant ["Init";"Peano"] "lt")
let well_founded = ConstRef (coq_constant ["Init";"Wf"] "well_founded")
let z = IndRef (coq_constant ["ZArith";"fast_integer"] "Z", 0)
let and_ = IndRef (coq_constant ["Init";"Logic"] "and", 0)
let eq = IndRef (coq_constant ["Init";"Logic"] "eq", 0)

(* ["(well_founded nat lt)"] *)
let wf_nat_pattern = 
  PApp (PRef well_founded, [| PRef nat; PRef lt |])
(* ["((well_founded Z (Zwf ?1))"] *)
let wf_z_pattern = 
  let zwf = ConstRef (coq_constant ["correctness";"ProgWf"] "Zwf") in
  PApp (PRef well_founded, [| PRef z; PApp (PRef zwf, [| PMeta (Some 1) |]) |])
(* ["(and ?1 ?2)"] *)
let and_pattern = 
  PApp (PRef and_, [| PMeta (Some 1); PMeta (Some 2) |])
(* ["(eq ?1 ?2 ?3)"] *)
let eq_pattern = 
  PApp (PRef eq, [| PMeta (Some 1); PMeta (Some 2); PMeta (Some 3) |])

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

let reduce_open_constr (em,c) =
  let existential_map_of_constr = 
    let rec collect em c = match kind_of_term c with
      | IsCast (c',t) -> 
	  (match kind_of_term c' with
	     | IsEvar ev -> (ev,t) :: em
	     | _ -> fold_constr collect em c)
      | IsEvar _ -> 
	  assert false (* all existentials should be casted *)
      | _ -> 
	  fold_constr collect em c
    in
    collect []
  in
  let c = Pred.red_cci c in
  let em = existential_map_of_constr c in
  (em,c)

let correctness s p opttac =
  Pmisc.reset_names();
  let p,oc,cty,v = coqast_of_prog p in
  let env = Global.env () in
  let sign = Global.named_context () in
  let sigma = Evd.empty in
  let cty = Reduction.nf_betaiota cty in
  let id = id_of_string s in 
  start_proof id Declare.NeverDischarge sign cty;
  Penv.new_edited id (v,p);
  if !debug then show_open_subgoals();
  deb_mess [< 'sTR"Pred.red_cci: Reduction..."; 'fNL >];
  let oc = reduce_open_constr oc in
  deb_mess [< 'sTR"AFTER REDUCTION:"; 'fNL >];
  deb_mess (Printer.prterm (snd oc));
  let tac = (tclTHEN (Refine.refine_tac oc) automatic) in
  let tac = match opttac with 
    | None -> tac
    | Some t -> tclTHEN tac t
  in
  solve_nth 1 tac;
  if_verbose show_open_subgoals ()


(* On redéfinit la commande "Save" pour enregistrer les nouveaux programmes *)

open Vernacinterp

let add = Vernacinterp.overwriting_vinterp_add

let register id n =
  let id' = match n with None -> id | Some id' -> id' in
  Penv.register id id'

(*
let wrap_save_named b =
  let pf_id = Pfedit.get_current_proof_name () in
  Command.save_named b;
  register pf_id None

let wrap_save_anonymous b id =
  let pf_id = Pfedit.get_current_proof_name () in
  Command.save_anonymous b (string_of_id id);
  register pf_id (Some id)
*)

let _ = 
  let current_save = Vernacinterp.vinterp_map "SaveNamed" in
    add "SaveNamed"
      (function [] -> (fun () -> let pf_id =  Pfedit.get_current_proof_name () in
			 current_save [] ();
			 register pf_id None)
	 |   _  -> assert false)

let _ = 
  let current_defined = Vernacinterp.vinterp_map "DefinedNamed" in
    add "DefinedNamed"
      (function [] -> (fun () -> let pf_id = Pfedit.get_current_proof_name () in
			 current_defined [] ();
			 register pf_id None)
	 | _ -> assert false)

let _ =
  let current_saveanonymous = Vernacinterp.vinterp_map "SaveAnonymous" in
    add "SaveAnonymous"
      (function [VARG_IDENTIFIER id] -> 
	 (fun () -> let pf_id = Pfedit.get_current_proof_name () in
	    current_saveanonymous [VARG_IDENTIFIER id] ();
	    register pf_id (Some id))
    |   _  -> assert false)

(* Old version that does not allow multiple modifications of the "Save" command *)
(*
let _ = 

let _ = add "DefinedNamed"
    (function [] -> (fun () -> if_verbose show_script ();
		              wrap_save_named false)
    |   _  -> assert false)

let _ = add "SaveAnonymous"
    (function [VARG_IDENTIFIER id] -> 
       (fun () -> if_verbose show_script ();
	          wrap_save_anonymous true id)
    |   _  -> assert false)
*)
