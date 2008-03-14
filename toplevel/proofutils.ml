(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

(***********************************************************************)
(*                                                                     *)
(*      This module proposes a number of methods to access             *)
(*      and use proofs (from module Proof) or the global proof         *)
(*      state (given by module Global_proof)                           *)
(*                                                                     *)
(***********************************************************************)

open Pp

(*** Helper functions related to the Proof module ***)


(*** Helper functions related to the Proof_global module ***)

let proof_starter_of_type_list typs =
  List.map (fun x -> (Global.env (), x, None)) typs

let start_new_single_proof (* name/tag? *) typ return =
  let return constrs pe =
    match constrs with
    | [c] -> return c pe
    | _ -> Util.anomaly "Proofutils.start_new_single_proof:
                         Proofs seems to have grown extra base goals."
  in
  Proof_global.start_a_new_proof (proof_starter_of_type_list [typ]) return

let start_a_new_proof_in_global_env typs_and_tags return =
  Proof_global.start_a_new_proof
    (List.map (fun (tp,tg) -> (Global.env (), tp, tg) ) typs_and_tags)
    return


(*arnaud:  COMMENTAIRES!! *)
open Decl_kinds
open Entries
let save id bdy otyp opacity boxed locality kind =
  let const = { const_entry_body = bdy;
		const_entry_type = otyp;
		const_entry_opaque = opacity;
	        const_entry_boxed = boxed }
  in
  match locality with
  | Local when Lib.sections_are_opened () ->
      let k = logical_kind_of_goal_kind kind in
      let c = Declare.SectionLocalDef (bdy, otyp, opacity) in
      let _ = Command.verbose_declare_variable id (Lib.cwd(), c, k) in
      (Local, Libnames.VarRef id)
  | Local ->
      let k = logical_kind_of_goal_kind kind in
      let kn = Command.verbose_declare_constant id (DefinitionEntry const, k) in
      (Global, Libnames.ConstRef kn)
  | Global ->
      let k = logical_kind_of_goal_kind kind in
      let kn = Command.verbose_declare_constant id (DefinitionEntry const, k) in
      (Global, Libnames.ConstRef kn) 

let return_for_definitions id locality kind typ c = function
  | Admitted -> let kn = Command.verbose_declare_constant
                                id
				(ParameterEntry (typ,false) , 
				 IsAssumption Conjectural   )
                in
                Proof_global.discard ()
  | Proved (is_opaque, idopt) -> 
      (* arnaud: fait le showscript à la fin des preuves, broken pour l'instant:
	 if not !Flags.print_emacs then if_verbose show_script ();
      *)
      let cur = Proof_global.give_me_the_proof () in
      if not (Proof.is_done cur) then
	Util.error "The proof is incomplete, it cannot be saved."
      else
	begin match idopt with
       | None -> 
	   save id c (Some typ) is_opaque false locality kind
       | Some _ ->
	   Util.anomaly "Proofutils.return_for_definition: cette commande n'a pas encore été réactivée"
	end;
	Proof_global.discard ()
	

let return_for_anonymous_proofs typ c = function
  | Admitted -> Proof_global.discard ()
  | Proved (is_opaque, idopt) -> 
      (* arnaud: fait le showscript à la fin des preuves, broken pour l'instant:
	 if not !Flags.print_emacs then if_verbose show_script ();
      *)
      let cur = Proof_global.give_me_the_proof () in
      if not (Proof.is_done cur) then
	Util.error "The proof is incomplete, it cannot be checked."
      else
	begin match idopt with
       | None -> 
	   (* arnaud: rattraper l'erreur sans doute ?*)
	   (* arnaud: rajouter un message encourageant *)
	   Typing.check (Global.env()) (Evd.empty) c typ
       | Some _ ->
	   Util.anomaly "Proofutils.return_for_goals: cette commande n'a pas encore été réactivée"
	end;
	Proof_global.discard ()

(*arnaud: quel type pour les hook ? *)
let start_a_new_definition_proof name (locality,kind) typ =
  start_new_single_proof typ (return_for_definitions name locality kind typ)

let start_a_new_proof_command oname kind (bl,t) =
  let env = Global.env () in
  let c = Constrintern.interp_type Evd.empty 
                                   env 
				  (Command.generalize_constr_expr t bl) 
  in
  let _ = Typeops.infer_type env c in
  match oname with
  | Some id -> 
      (* We check existence here: it's a bit late at Qed time *)
      if Nametab.exists_cci (Lib.make_path id) 
	                        or Termops.is_section_variable id then
        Util.errorlabstrm "start_proof" 
	                  (Nameops.pr_id id ++ str " already exists");
      start_a_new_definition_proof id kind c
  | None -> start_new_single_proof c (return_for_anonymous_proofs c)
