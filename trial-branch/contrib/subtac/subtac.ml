(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Global
open Pp
open Util
open Names
open Sign
open Evd
open Term
open Termops
open Reductionops
open Environ
open Type_errors
open Typeops
open Libnames
open Classops
open List
open Recordops 
open Evarutil
open Pretype_errors
open Rawterm
open Evarconv
open Pattern
open Dyn
open Vernacexpr

open Subtac_coercion
open Subtac_utils
open Coqlib
open Printer
open Subtac_errors
open Eterm

let require_library dirpath =
  let qualid = (dummy_loc, qualid_of_dirpath (dirpath_of_string dirpath)) in
    Library.require_library [qualid] None

open Pp
open Ppconstr
open Decl_kinds
open Tacinterp
open Tacexpr

let solve_tccs_in_type env id isevars evm c typ =
  if not (evm = Evd.empty) then 
    let stmt_id = Nameops.add_suffix id "_stmt" in
    let obls, c', t' = eterm_obligations env stmt_id !isevars evm 0 c typ in
    (** Make all obligations transparent so that real dependencies can be sorted out by the user *)
    let obls = Array.map (fun (id, t, op, d) -> (id, t, false, d)) obls in
      match Subtac_obligations.add_definition stmt_id c' typ obls with
	  Subtac_obligations.Defined cst -> constant_value (Global.env()) cst
	| _ -> 
	    errorlabstrm "start_proof" 
	      (str "The statement obligations could not be resolved automatically, " ++ spc () ++
		  str "write a statement definition first.")
  else
    let _ = Typeops.infer_type env c in c


let start_proof_com env isevars sopt kind (bl,t) hook =
  let id = match sopt with
    | Some id ->
        (* We check existence here: it's a bit late at Qed time *)
        if Nametab.exists_cci (Lib.make_path id) or is_section_variable id then
          errorlabstrm "start_proof" (pr_id id ++ str " already exists");
        id
    | None ->
	next_global_ident_away false (id_of_string "Unnamed_thm")
 	  (Pfedit.get_all_proof_names ())
  in
  let evm, c, typ, _imps = 
    Subtac_pretyping.subtac_process env isevars id [] (Command.generalize_constr_expr t bl) None 
  in
  let c = solve_tccs_in_type env id isevars evm c typ in
    Command.start_proof id kind c hook	
      
let print_subgoals () = Flags.if_verbose (fun () -> msg (Printer.pr_open_subgoals ())) ()

let start_proof_and_print env isevars idopt k t hook =
  start_proof_com env isevars idopt k t hook;
  print_subgoals ()
	  
let _ = Detyping.set_detype_anonymous (fun loc n -> RVar (loc, id_of_string ("Anonymous_REL_" ^ string_of_int n)))
  
let assumption_message id =
  Flags.if_verbose message ((string_of_id id) ^ " is assumed")

let declare_assumption env isevars idl is_coe k bl c nl =
  if not (Pfedit.refining ()) then
    let id = snd (List.hd idl) in
    let evm, c, typ, imps = 
      Subtac_pretyping.subtac_process env isevars id [] (Command.generalize_constr_expr c bl) None 
    in
    let c = solve_tccs_in_type env id isevars evm c typ in
      List.iter (Command.declare_one_assumption is_coe k c nl) idl
  else
    errorlabstrm "Command.Assumption"
	(str "Cannot declare an assumption while in proof editing mode.")

let vernac_assumption env isevars kind l nl =
  List.iter (fun (is_coe,(idl,c)) -> declare_assumption env isevars idl is_coe kind [] c nl) l


let subtac (loc, command) =
  check_required_library ["Coq";"Init";"Datatypes"];
  check_required_library ["Coq";"Init";"Specif"];
(*   check_required_library ["Coq";"Logic";"JMeq"]; *)
  require_library "Coq.Program.Wf";
  require_library "Coq.Program.Tactics";
  require_library "Coq.Logic.JMeq";
  let env = Global.env () in
  let isevars = ref (create_evar_defs Evd.empty) in
  try
  match command with
	VernacDefinition (defkind, (locid, id), expr, hook) -> 
	    (match expr with
	      | ProveBody (bl, t) -> 
		  if Lib.is_modtype () then
		    errorlabstrm "Subtac_command.StartProof"
		      (str "Proof editing mode not supported in module types");
		  start_proof_and_print env isevars (Some id) (Global, DefinitionBody Definition) (bl,t) 
		    (fun _ _ -> ())
	      | DefineBody (bl, _, c, tycon) -> 
		   ignore(Subtac_pretyping.subtac_proof env isevars id bl c tycon))
      | VernacFixpoint (l, b) -> 
	  let _ = trace (str "Building fixpoint") in
	    ignore(Subtac_command.build_recursive l b)

      | VernacStartTheoremProof (thkind, (locid, id), (bl, t), lettop, hook) ->
	  if not(Pfedit.refining ()) then
	    if lettop then
	      errorlabstrm "Subtac_command.StartProof"
		(str "Let declarations can only be used in proof editing mode");
	  if Lib.is_modtype () then
	    errorlabstrm "Subtac_command.StartProof"
	      (str "Proof editing mode not supported in module types");
	  start_proof_and_print env isevars (Some id) (Global, Proof thkind) (bl,t) hook


      | VernacAssumption (stre,nl,l) -> 
	  vernac_assumption env isevars stre l nl

      | VernacInstance (sup, is, props) ->
	  Subtac_classes.new_instance sup is props

(*       | VernacCoFixpoint (l, b) ->  *)
(* 	  let _ = trace (str "Building cofixpoint") in *)
(* 	    ignore(Subtac_command.build_recursive l b) *)

      (*| VernacEndProof e -> 
	  subtac_end_proof e*)

      | _ -> user_err_loc (loc,"", str ("Invalid Program command"))
  with 
    | Typing_error e ->
	msg_warning (str "Type error in Program tactic:");
	let cmds = 
	  (match e with
	     | NonFunctionalApp (loc, x, mux, e) ->
		 str "non functional application of term " ++ 
		 e ++ str " to function " ++ x ++ str " of (mu) type " ++ mux
	     | NonSigma (loc, t) ->
		 str "Term is not of Sigma type: " ++ t
	     | NonConvertible (loc, x, y) ->
		 str "Unconvertible terms:" ++ spc () ++
		   x ++ spc () ++ str "and" ++ spc () ++ y
	     | IllSorted (loc, t) ->
		 str "Term is ill-sorted:" ++ spc () ++ t
	  )
	in msg_warning cmds
	     
    | Subtyping_error e ->
	msg_warning (str "(Program tactic) Subtyping error:");
	let cmds = 
	  match e with
	    | UncoercibleInferType (loc, x, y) ->
		str "Uncoercible terms:" ++ spc ()
		++ x ++ spc () ++ str "and" ++ spc () ++ y
	    | UncoercibleInferTerm (loc, x, y, tx, ty) ->
		str "Uncoercible terms:" ++ spc ()
		++ tx ++ spc () ++ str "of" ++ spc () ++ str "type" ++ spc () ++ x
		++ str "and" ++ spc() ++ ty ++ spc () ++ str "of" ++ spc () ++ str "type" ++ spc () ++ y
	    | UncoercibleRewrite (x, y) ->
		str "Uncoercible terms:" ++ spc ()
		++ x ++ spc () ++ str "and" ++ spc () ++ y
	in msg_warning cmds

    | Cases.PatternMatchingError (env, exn) as e ->
	debug 2 (Himsg.explain_pattern_matching_error env exn);
	raise e
    
    | Type_errors.TypeError (env, exn) as e ->
	debug 2 (Himsg.explain_type_error env exn);
	raise e
	  
    | Pretype_errors.PretypeError (env, exn) as e ->
	debug 2 (Himsg.explain_pretype_error env exn);
	raise e
	  
    | (Stdpp.Exc_located (loc, e')) as e ->
	debug 2 (str "Parsing exception: ");
	(match e' with
	   | Type_errors.TypeError (env, exn) ->
	       debug 2 (Himsg.explain_type_error env exn);
	       raise e
		 
	   | Pretype_errors.PretypeError (env, exn) ->
	       debug 2 (Himsg.explain_pretype_error env exn);
	       raise e

	   | e'' -> msg_warning (str "Unexpected exception: " ++ Cerrors.explain_exn e'');
	       raise e)
  
    | e -> 
	msg_warning (str "Uncatched exception: " ++ Cerrors.explain_exn e);
	raise e


