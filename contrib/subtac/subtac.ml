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
open Context
open Eterm

let require_library dirpath =
  let qualid = (dummy_loc, qualid_of_dirpath (dirpath_of_string dirpath)) in
    Library.require_library [qualid] None
(*
let subtac_one_fixpoint env isevars (f, decl) = 
  let ((id, n, bl, typ, body), decl) = 
    Subtac_interp_fixpoint.rewrite_fixpoint env [] (f, decl) 
  in
  let _ = 
    try trace (str "Working on a single fixpoint rewritten as: " ++ spc () ++
	       Ppconstr.pr_constr_expr body)
    with _ -> ()
  in ((id, n, bl, typ, body), decl)
*)
	      
let subtac_fixpoint isevars l = 
  (* TODO: Copy command.build_recursive *)
  ()
(*
let save id const (locality,kind) hook =
  let {const_entry_body = pft;
       const_entry_type = tpo;
       const_entry_opaque = opacity } = const in
  let l,r = match locality with
    | Local when Lib.sections_are_opened () ->
        let k = logical_kind_of_goal_kind kind in
	let c = SectionLocalDef (pft, tpo, opacity) in
	let _ = declare_variable id (Lib.cwd(), c, k) in
	(Local, VarRef id)
    | Local ->
        let k = logical_kind_of_goal_kind kind in
        let kn = declare_constant id (DefinitionEntry const, k) in
	(Global, ConstRef kn)
    | Global ->
        let k = logical_kind_of_goal_kind kind in
        let kn = declare_constant id (DefinitionEntry const, k) in
	(Global, ConstRef kn) in
  Pfedit.delete_current_proof ();
  hook l r;
  definition_message id

let save_named opacity =
  let id,(const,persistence,hook) = Pfedit.cook_proof () in
  let const = { const with const_entry_opaque = opacity } in
  save id const persistence hook

let check_anonymity id save_ident =
  if atompart_of_id id <> "Unnamed_thm" then
    error "This command can only be used for unnamed theorem"
(*
    message("Overriding name "^(string_of_id id)^" and using "^save_ident)
*)

let save_anonymous opacity save_ident =
  let id,(const,persistence,hook) = Pfedit.cook_proof () in
  let const = { const with const_entry_opaque = opacity } in
  check_anonymity id save_ident;
  save save_ident const persistence hook

let save_anonymous_with_strength kind opacity save_ident =
  let id,(const,_,hook) = Pfedit.cook_proof () in
  let const = { const with const_entry_opaque = opacity } in
  check_anonymity id save_ident;
  (* we consider that non opaque behaves as local for discharge *)
  save save_ident const (Global, Proof kind) hook

let subtac_end_proof = function
  | Admitted -> admit ()
  | Proved (is_opaque,idopt) ->
    if_verbose show_script ();
    match idopt with
    | None -> save_named is_opaque
    | Some ((_,id),None) -> save_anonymous is_opaque id
    | Some ((_,id),Some kind) -> save_anonymous_with_strength kind is_opaque id

	*)

open Pp
open Ppconstr
open Decl_kinds
open Tacinterp
open Tacexpr

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
  let evm, c, typ = 
    Subtac_pretyping.subtac_process env isevars id [] (Command.generalize_constr_expr t bl) None 
  in
  let _ = Typeops.infer_type env c in
    Command.start_proof id kind c hook
      
let print_subgoals () = Options.if_verbose (fun () -> msg (Printer.pr_open_subgoals ())) ()

let start_proof_and_print env isevars idopt k t hook =
  start_proof_com env isevars idopt k t hook;
  print_subgoals ()
  (*if !pcoq <> None then (out_some !pcoq).start_proof ()*)

let subtac (loc, command) =
  check_required_library ["Coq";"Init";"Datatypes"];
  check_required_library ["Coq";"Init";"Specif"];
  (* check_required_library ["Coq";"Logic";"JMeq"]; *)
  require_library "Coq.subtac.FixSub";
  require_library "Coq.subtac.Utils";
  let env = Global.env () in
  let isevars = ref (create_evar_defs Evd.empty) in
  try
    match command with
	VernacDefinition (defkind, (locid, id), expr, hook) -> 
	    (match expr with
		 ProveBody (bl, c) -> Subtac_pretyping.subtac_proof env isevars id bl c None
(* 		   let evm, c, ctyp =  in *)
(* 		     trace (str "Starting proof"); *)
(* 		     Command.start_proof id goal_kind c hook; *)
(* 		     trace (str "Started proof");	      *)
		     
	       | DefineBody (bl, _, c, tycon) -> 
		   Subtac_pretyping.subtac_proof env isevars id bl c tycon
		     (* let tac = Eterm.etermtac (evm, c) in  *)
		     (* 		     trace (str "Starting proof"); *)
		     (* 		     Command.start_proof id goal_kind ctyp hook; *)
		     (* 		     trace (str "Started proof"); *)
		     (* 		     Pfedit.by tac) *))
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


