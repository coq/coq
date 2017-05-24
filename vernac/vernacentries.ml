(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Concrete syntax of the mathematical vernacular MV V2.6 *)

open Pp
open CErrors
open Util
open Flags
open Names
open Nameops
open Term
open Pfedit
open Tacmach
open Constrintern
open Prettyp
open Printer
open Command
open Goptions
open Libnames
open Globnames
open Vernacexpr
open Decl_kinds
open Constrexpr
open Redexpr
open Lemmas
open Misctypes
open Locality
open Sigma.Notations

module NamedDecl = Context.Named.Declaration

(** TODO: make this function independent of Ltac *)
let (f_interp_redexp, interp_redexp_hook) = Hook.make ()

let debug = false
(* XXX Should move to a common library *)
let vernac_pperr_endline pp =
  if debug then Format.eprintf "@[%a@]@\n%!" Pp.pp_with (pp ()) else ()

(* Misc *)

let cl_of_qualid = function
  | FunClass -> Classops.CL_FUN
  | SortClass -> Classops.CL_SORT
  | RefClass r -> Class.class_of_global (Smartlocate.smart_global ~head:true r)

let scope_class_of_qualid qid =
  Notation.scope_class_of_class (cl_of_qualid qid)

(*******************)
(* "Show" commands *)

let show_proof () =
  (* spiwack: this would probably be cooler with a bit of polishing. *)
  let p = Proof_global.give_me_the_proof () in
  let pprf = Proof.partial_proof p in
  Feedback.msg_notice (Pp.prlist_with_sep Pp.fnl Printer.pr_econstr pprf)

let show_node () =
  (* spiwack: I'm have little clue what this function used to do. I deactivated it, 
      could, possibly, be cleaned away. (Feb. 2010) *)
  ()

let show_thesis () = CErrors.anomaly (Pp.str "Show Thesis: TODO")

let show_top_evars () =
  (* spiwack: new as of Feb. 2010: shows goal evars in addition to non-goal evars. *)
  let pfts = get_pftreestate () in
  let gls = Proof.V82.subgoals pfts in
  let sigma = gls.Evd.sigma in
  Feedback.msg_notice (pr_evars_int sigma 1 (Evarutil.non_instantiated sigma))

let show_universes () =
  let pfts = get_pftreestate () in
  let gls = Proof.V82.subgoals pfts in
  let sigma = gls.Evd.sigma in
  let ctx = Evd.universe_context_set (Evd.nf_constraints sigma) in
    Feedback.msg_notice (Termops.pr_evar_universe_context (Evd.evar_universe_context sigma));
    Feedback.msg_notice (str"Normalized constraints: " ++ Univ.pr_universe_context_set (Termops.pr_evd_level sigma) ctx)

(* Spiwack: proof tree is currently not working *)
let show_prooftree () = ()

(* Simulate the Intro(s) tactic *)
let show_intro all =
  let open EConstr in
  let pf = get_pftreestate() in
  let {Evd.it=gls ; sigma=sigma; } = Proof.V82.subgoals pf in
  if not (List.is_empty gls) then begin
    let gl = {Evd.it=List.hd gls ; sigma = sigma; } in
    let l,_= decompose_prod_assum sigma (Termops.strip_outer_cast sigma (pf_concl gl)) in
    if all then
      let lid = Tactics.find_intro_names l gl in
      Feedback.msg_notice (hov 0 (prlist_with_sep  spc pr_id lid))
    else if not (List.is_empty l) then
      let n = List.last l in
      Feedback.msg_notice (pr_id (List.hd (Tactics.find_intro_names [n] gl)))
  end

(** Prepare a "match" template for a given inductive type.
    For each branch of the match, we list the constructor name
    followed by enough pattern variables.
    [Not_found] is raised if the given string isn't the qualid of
    a known inductive type. *)

let make_cases_aux glob_ref =
  match glob_ref with
    | Globnames.IndRef i ->
	let {Declarations.mind_nparams = np}
	    , {Declarations.mind_consnames = carr ; Declarations.mind_nf_lc = tarr }
	      = Global.lookup_inductive i in
	Util.Array.fold_right2
	  (fun consname typ l ->
	     let al = List.rev (fst (decompose_prod typ)) in
	     let al = Util.List.skipn np al in
	     let rec rename avoid = function
	       | [] -> []
	       | (n,_)::l ->
		   let n' = Namegen.next_name_away_with_default (Id.to_string Namegen.default_dependent_ident) n avoid in
		   Id.to_string n' :: rename (n'::avoid) l in
	     let al' = rename [] al in
	     (Id.to_string consname :: al') :: l)
	  carr tarr []
    | _ -> raise Not_found

let make_cases s =
  let qualified_name = Libnames.qualid_of_string s in
  let glob_ref = Nametab.locate qualified_name in
  make_cases_aux glob_ref

(** Textual display of a generic "match" template *)

let show_match id =
  let patterns =
    try make_cases_aux (Nametab.global id)
    with Not_found -> error "Unknown inductive type."
  in
  let pr_branch l =
    str "| " ++ hov 1 (prlist_with_sep spc str l) ++ str " =>"
  in
  Feedback.msg_notice (v 1 (str "match # with" ++ fnl () ++
	    prlist_with_sep fnl pr_branch patterns ++ fnl () ++ str "end" ++ fnl ()))

(* "Print" commands *)

let print_path_entry p =
  let dir = pr_dirpath (Loadpath.logical p) in
  let path = str (Loadpath.physical p) in
  Pp.hov 2 (dir ++ spc () ++ path)

let print_loadpath dir =
  let l = Loadpath.get_load_paths () in
  let l = match dir with
  | None -> l
  | Some dir ->
    let filter p = is_dirpath_prefix_of dir (Loadpath.logical p) in
    List.filter filter l
  in
  str "Logical Path / Physical path:" ++ fnl () ++
    prlist_with_sep fnl print_path_entry l

let print_modules () =
  let opened = Library.opened_libraries ()
  and loaded = Library.loaded_libraries () in
  (* we intersect over opened to preserve the order of opened since *)
  (* non-commutative operations (e.g. visibility) are done at import time *)
  let loaded_opened = List.intersect DirPath.equal opened loaded
  and only_loaded = List.subtract DirPath.equal loaded opened in
  str"Loaded and imported library files: " ++
  pr_vertical_list pr_dirpath loaded_opened ++ fnl () ++
  str"Loaded and not imported library files: " ++
  pr_vertical_list pr_dirpath only_loaded


let print_module r =
  let (loc,qid) = qualid_of_reference r in
  try
    let globdir = Nametab.locate_dir qid in
      match globdir with
	  DirModule (dirpath,(mp,_)) ->
	    Feedback.msg_notice (Printmod.print_module (Printmod.printable_body dirpath) mp)
	| _ -> raise Not_found
  with
      Not_found -> Feedback.msg_error (str"Unknown Module " ++ pr_qualid qid)

let print_modtype r =
  let (loc,qid) = qualid_of_reference r in
  try
    let kn = Nametab.locate_modtype qid in
    Feedback.msg_notice (Printmod.print_modtype kn)
  with Not_found ->
    (* Is there a module of this name ? If yes we display its type *)
    try
      let mp = Nametab.locate_module qid in
      Feedback.msg_notice (Printmod.print_module false mp)
    with Not_found ->
      Feedback.msg_error (str"Unknown Module Type or Module " ++ pr_qualid qid)

let print_namespace ns =
  let ns = List.rev (Names.DirPath.repr ns) in
  (* [match_dirpath], [match_modulpath] are helpers for [matches]
     which checks whether a constant is in the namespace [ns]. *)
  let rec match_dirpath ns = function
    | [] -> Some ns
    | id::dir ->
        begin match match_dirpath ns dir with
        | Some [] as y -> y
        | Some (a::ns') ->
            if Names.Id.equal a id then Some ns'
            else None
        | None -> None
        end
  in
  let rec match_modulepath ns = function
    | MPbound _ -> None (* Not a proper namespace. *)
    | MPfile dir -> match_dirpath ns (Names.DirPath.repr dir)
    | MPdot (mp,lbl) ->
        let id = Names.Label.to_id lbl in
        begin match match_modulepath ns mp with
        | Some [] as y -> y
        | Some (a::ns') ->
            if Names.Id.equal a id then Some ns'
            else None
        | None -> None
        end
  in
  (* [qualified_minus n mp] returns a list of qualifiers representing
     [mp] except the [n] first (in the concrete syntax order).  The
     idea is that if [mp] matches [ns], then [qualified_minus mp
     (length ns)] will be the correct representation of [mp] assuming
     [ns] is imported. *)
  (* precondition: [mp] matches some namespace of length [n] *)
  let qualified_minus n mp =
    let rec list_of_modulepath = function
      | MPbound _ -> assert false (* MPbound never matches *)
      | MPfile dir -> Names.DirPath.repr dir
      | MPdot (mp,lbl) -> (Names.Label.to_id lbl)::(list_of_modulepath mp)
    in
    snd (Util.List.chop n (List.rev (list_of_modulepath mp)))
  in
  let print_list pr l = prlist_with_sep (fun () -> str".") pr l in
  let print_kn kn =
    (* spiwack: I'm ignoring the dirpath, is that bad? *)
    let (mp,_,lbl) = Names.repr_kn kn in
    let qn = (qualified_minus (List.length ns) mp)@[Names.Label.to_id lbl] in
    print_list pr_id qn
  in
  let print_constant k body =
    (* FIXME: universes *)
    let t = Typeops.type_of_constant_type (Global.env ()) body.Declarations.const_type in
    print_kn k ++ str":" ++ spc() ++ Printer.pr_type t
  in
  let matches mp = match match_modulepath ns mp with
  | Some [] -> true
  | _ -> false in
  let constants = (Environ.pre_env (Global.env ())).Pre_env.env_globals.Pre_env.env_constants in
  let constants_in_namespace =
    Cmap_env.fold (fun c (body,_) acc ->
      let kn = user_con c in
      if matches (modpath kn) then
        acc++fnl()++hov 2 (print_constant kn body)
      else
        acc
    ) constants (str"")
  in
  Feedback.msg_notice ((print_list pr_id ns)++str":"++fnl()++constants_in_namespace)

let print_strategy r =
  let open Conv_oracle in
  let pr_level = function
  | Expand -> str "expand"
  | Level 0 -> str "transparent"
  | Level n -> str "level" ++ spc() ++ int n
  | Opaque -> str "opaque"
  in
  let pr_strategy (ref, lvl) = pr_global ref ++ str " : " ++ pr_level lvl in
  let oracle = Environ.oracle (Global.env ()) in
  match r with
  | None ->
    let fold key lvl (vacc, cacc) = match key with
    | VarKey id -> ((VarRef id, lvl) :: vacc, cacc)
    | ConstKey cst -> (vacc, (ConstRef cst, lvl) :: cacc)
    | RelKey _ -> (vacc, cacc)
    in
    let var_lvl, cst_lvl = fold_strategy fold oracle ([], []) in
    let var_msg =
      if List.is_empty var_lvl then mt ()
      else str "Variable strategies" ++ fnl () ++
        hov 0 (prlist_with_sep fnl pr_strategy var_lvl) ++ fnl ()
    in
    let cst_msg =
      if List.is_empty cst_lvl then mt ()
      else str "Constant strategies" ++ fnl () ++
        hov 0 (prlist_with_sep fnl pr_strategy cst_lvl)
    in
    Feedback.msg_notice (var_msg ++ cst_msg)
  | Some r ->
    let r = Smartlocate.smart_global r in
    let key = match r with
    | VarRef id -> VarKey id
    | ConstRef cst -> ConstKey cst
    | IndRef _ | ConstructRef _ -> error "The reference is not unfoldable"
    in
    let lvl = get_strategy oracle key in
    Feedback.msg_notice (pr_strategy (r, lvl))

let dump_universes_gen g s =
  let output = open_out s in
  let output_constraint, close =
    if Filename.check_suffix s ".dot" || Filename.check_suffix s ".gv" then begin
      (* the lazy unit is to handle errors while printing the first line *)
      let init = lazy (Printf.fprintf output "digraph universes {\n") in
      begin fun kind left right ->
        let () = Lazy.force init in
        match kind with
          | Univ.Lt ->
            Printf.fprintf output "  \"%s\" -> \"%s\" [style=bold];\n" right left
          | Univ.Le ->
            Printf.fprintf output "  \"%s\" -> \"%s\" [style=solid];\n" right left
          | Univ.Eq ->
            Printf.fprintf output "  \"%s\" -> \"%s\" [style=dashed];\n" left right
      end, begin fun () ->
        if Lazy.is_val init then Printf.fprintf output "}\n";
        close_out output
      end
    end else begin
      begin fun kind left right ->
        let kind = match kind with
          | Univ.Lt -> "<"
          | Univ.Le -> "<="
          | Univ.Eq -> "="
        in Printf.fprintf output "%s %s %s ;\n" left kind right
      end, (fun () -> close_out output)
    end
  in
  try
    UGraph.dump_universes output_constraint g;
    close ();
    Feedback.msg_info (str "Universes written to file \"" ++ str s ++ str "\".")
  with reraise ->
    let reraise = CErrors.push reraise in
    close ();
    iraise reraise

(*********************)
(* "Locate" commands *)

let locate_file f =
  let file = Flags.silently Loadpath.locate_file f in
  str file

let msg_found_library = function
  | Library.LibLoaded, fulldir, file ->
      Feedback.msg_info (hov 0
	(pr_dirpath fulldir ++ strbrk " has been loaded from file " ++
	 str file))
  | Library.LibInPath, fulldir, file ->
      Feedback.msg_info (hov 0
	(pr_dirpath fulldir ++ strbrk " is bound to file " ++ str file))

let err_unmapped_library ?loc ?from qid =
  let dir = fst (repr_qualid qid) in
  let prefix = match from with
  | None -> str "."
  | Some from ->
    str " and prefix " ++ pr_dirpath from ++ str "."
  in
  user_err ?loc
    ~hdr:"locate_library"
    (strbrk "Cannot find a physical path bound to logical path matching suffix " ++
       pr_dirpath dir ++ prefix)

let err_notfound_library ?loc ?from qid =
  let prefix = match from with
  | None -> str "."
  | Some from ->
    str " with prefix " ++ pr_dirpath from ++ str "."
  in
  user_err ?loc ~hdr:"locate_library"
     (strbrk "Unable to locate library " ++ pr_qualid qid ++ prefix)

let print_located_library r =
  let (loc,qid) = qualid_of_reference r in
  try msg_found_library (Library.locate_qualified_library ~warn:false qid)
  with
    | Library.LibUnmappedDir -> err_unmapped_library ?loc qid
    | Library.LibNotFound -> err_notfound_library ?loc qid

let smart_global r =
  let gr = Smartlocate.smart_global r in
    Dumpglob.add_glob ?loc:(Stdarg.loc_of_or_by_notation loc_of_reference r) gr;
    gr

let dump_global r =
  try
    let gr = Smartlocate.smart_global r in
    Dumpglob.add_glob ?loc:(Stdarg.loc_of_or_by_notation loc_of_reference r) gr
  with e when CErrors.noncritical e -> ()
(**********)
(* Syntax *)

let vernac_syntax_extension locality local =
  let local = enforce_module_locality locality local in
  Metasyntax.add_syntax_extension local

let vernac_delimiters sc = function
  | Some lr -> Metasyntax.add_delimiters sc lr
  | None -> Metasyntax.remove_delimiters sc

let vernac_bind_scope sc cll =
  Metasyntax.add_class_scope sc (List.map scope_class_of_qualid cll)

let vernac_open_close_scope locality local (b,s) =
  let local = enforce_section_locality locality local in
  Notation.open_close_scope (local,b,s)

let vernac_arguments_scope locality r scl =
  let local = make_section_locality locality in
  Notation.declare_arguments_scope local (smart_global r) scl

let vernac_infix locality local =
  let local = enforce_module_locality locality local in
  Metasyntax.add_infix local

let vernac_notation locality local =
  let local = enforce_module_locality locality local in
  Metasyntax.add_notation local

(***********)
(* Gallina *)

let start_proof_and_print k l hook =
  let inference_hook =
    if Flags.is_program_mode () then
      let hook env sigma ev =
        let tac = !Obligations.default_tactic in
        let evi = Evd.find sigma ev in
        let env = Evd.evar_filtered_env evi in
        try
          let concl = Evarutil.nf_evars_universes sigma evi.Evd.evar_concl in
          let concl = EConstr.of_constr concl in
          if Evarutil.has_undefined_evars sigma concl then raise Exit;
          let c, _, ctx =
            Pfedit.build_by_tactic env (Evd.evar_universe_context sigma)
                                   concl (Tacticals.New.tclCOMPLETE tac)
          in Evd.set_universe_context sigma ctx, EConstr.of_constr c
        with Logic_monad.TacticFailure e when Logic.catchable_exception e ->
          error "The statement obligations could not be resolved \
                 automatically, write a statement definition first."
      in Some hook
    else None
  in
  start_proof_com ?inference_hook k l hook

let no_hook = Lemmas.mk_hook (fun _ _ -> ())

let vernac_definition_hook p = function
| Coercion -> Class.add_coercion_hook p
| CanonicalStructure ->
    Lemmas.mk_hook (fun _ -> Recordops.declare_canonical_structure)
| SubClass -> Class.add_subclass_hook p
| _ -> no_hook

let vernac_definition locality p (local,k) ((loc,id as lid),pl) def =
  let local = enforce_locality_exp locality local in
  let hook = vernac_definition_hook p k in
  let () = match local with
  | Discharge -> Dumpglob.dump_definition lid true "var"
  | Local | Global -> Dumpglob.dump_definition lid false "def"
  in
  (match def with
    | ProveBody (bl,t) ->   (* local binders, typ *)
	  start_proof_and_print (local,p,DefinitionBody k)
	    [Some (lid,pl), (bl,t)] hook
    | DefineBody (bl,red_option,c,typ_opt) ->
 	let red_option = match red_option with
          | None -> None
          | Some r ->
	      let (evc,env)= get_current_context () in
 		Some (snd (Hook.get f_interp_redexp env evc r)) in
	do_definition id (local,p,k) pl bl red_option c typ_opt hook)

let vernac_start_proof locality p kind l lettop =
  let local = enforce_locality_exp locality None in
  if Dumpglob.dump () then
    List.iter (fun (id, _) ->
      match id with
	| Some (lid,_) -> Dumpglob.dump_definition lid false "prf"
	| None -> ()) l;
  if not(refining ()) then
    if lettop then
      user_err ~hdr:"Vernacentries.StartProof"
	(str "Let declarations can only be used in proof editing mode.");
  start_proof_and_print (local, p, Proof kind) l no_hook

let vernac_end_proof ?proof = function
  | Admitted          -> save_proof ?proof Admitted
  | Proved (_,_) as e -> save_proof ?proof e

let vernac_exact_proof c =
  (* spiwack: for simplicity I do not enforce that "Proof proof_term" is
     called only at the begining of a proof. *)
  let status = by (Tactics.exact_proof c) in
  save_proof (Vernacexpr.(Proved(Opaque None,None)));
  if not status then Feedback.feedback Feedback.AddedAxiom

let vernac_assumption locality poly (local, kind) l nl =
  let local = enforce_locality_exp locality local in
  let global = local == Global in
  let kind = local, poly, kind in
  List.iter (fun (is_coe,(idl,c)) ->
    if Dumpglob.dump () then
      List.iter (fun (lid, _) ->
	if global then Dumpglob.dump_definition lid false "ax"
	else Dumpglob.dump_definition lid true "var") idl) l;
  let status = do_assumptions kind nl l in
  if not status then Feedback.feedback Feedback.AddedAxiom

let vernac_record k poly finite struc binders sort nameopt cfs =
  let const = match nameopt with
    | None -> add_prefix "Build_" (snd (fst (snd struc)))
    | Some (_,id as lid) ->
	Dumpglob.dump_definition lid false "constr"; id in
    if Dumpglob.dump () then (
      Dumpglob.dump_definition (fst (snd struc)) false "rec";
      List.iter (fun (((_, x), _), _) ->
	match x with
	| Vernacexpr.AssumExpr ((loc, Name id), _) -> Dumpglob.dump_definition (loc,id) false "proj"
	| _ -> ()) cfs);
    ignore(Record.definition_structure (k,poly,finite,struc,binders,cfs,const,sort))

(** When [poly] is true the type is declared polymorphic. When [lo] is true,
    then the type is declared private (as per the [Private] keyword). [finite]
    indicates whether the type is inductive, co-inductive or
    neither. *)
let vernac_inductive poly lo finite indl =
  if Dumpglob.dump () then
    List.iter (fun (((coe,(lid,_)), _, _, _, cstrs), _) ->
      match cstrs with
	| Constructors cstrs ->
	    Dumpglob.dump_definition lid false "ind";
	    List.iter (fun (_, (lid, _)) ->
			 Dumpglob.dump_definition lid false "constr") cstrs
	| _ -> () (* dumping is done by vernac_record (called below) *) )
      indl;
  match indl with
  | [ ( _ , _ , _ ,(Record|Structure), Constructors _ ),_ ] ->
      CErrors.error "The Record keyword is for types defined using the syntax { ... }."
  | [ (_ , _ , _ ,Variant, RecordDecl _),_ ] ->
      CErrors.error "The Variant keyword does not support syntax { ... }."
  | [ ( id , bl , c , b, RecordDecl (oc,fs) ), [] ] ->
      vernac_record (match b with Class _ -> Class false | _ -> b)
       poly finite id bl c oc fs
  | [ ( id , bl , c , Class _, Constructors [l]), [] ] ->
      let f =
	let (coe, ((loc, id), ce)) = l in
	let coe' = if coe then Some true else None in
  	  (((coe', AssumExpr ((loc, Name id), ce)), None), [])
      in vernac_record (Class true) poly finite id bl c None [f]
  | [ ( _ , _, _, Class _, Constructors _), [] ] ->
      CErrors.error "Inductive classes not supported"
  | [ ( id , bl , c , Class _, _), _ :: _ ] ->
      CErrors.error "where clause not supported for classes"
  | [ ( _ , _ , _ , _, RecordDecl _ ) , _ ] ->
      CErrors.error "where clause not supported for (co)inductive records"
  | _ -> let unpack = function
      | ( (false, id) , bl , c , _ , Constructors l ) , ntn  -> ( id , bl , c , l ) , ntn
      | ( (true,_),_,_,_,Constructors _),_ ->
          CErrors.error "Variant types do not handle the \"> Name\" syntax, which is reserved for records. Use the \":>\" syntax on constructors instead."
      | _ -> CErrors.error "Cannot handle mutually (co)inductive records."
    in
    let indl = List.map unpack indl in
    do_mutual_inductive indl poly lo finite

let vernac_fixpoint locality poly local l =
  let local = enforce_locality_exp locality local in
  if Dumpglob.dump () then
    List.iter (fun (((lid,_), _, _, _, _), _) -> Dumpglob.dump_definition lid false "def") l;
  do_fixpoint local poly l

let vernac_cofixpoint locality poly local l =
  let local = enforce_locality_exp locality local in
  if Dumpglob.dump () then
    List.iter (fun (((lid,_), _, _, _), _) -> Dumpglob.dump_definition lid false "def") l;
  do_cofixpoint local poly l

let vernac_scheme l =
  if Dumpglob.dump () then
    List.iter (fun (lid, s) ->
	       Option.iter (fun lid -> Dumpglob.dump_definition lid false "def") lid;
	       match s with
	       | InductionScheme (_, r, _)
	       | CaseScheme (_, r, _) 
	       | EqualityScheme r -> dump_global r) l;
  Indschemes.do_scheme l

let vernac_combined_scheme lid l =
  if Dumpglob.dump () then
    (Dumpglob.dump_definition lid false "def";
     List.iter (fun lid -> dump_global (Misctypes.AN (Ident lid))) l);
 Indschemes.do_combined_scheme lid l

let vernac_universe loc poly l =
  if poly && not (Lib.sections_are_opened ()) then
    user_err ?loc ~hdr:"vernac_universe"
		 (str"Polymorphic universes can only be declared inside sections, " ++
		  str "use Monomorphic Universe instead");
  do_universe poly l

let vernac_constraint loc poly l =
  if poly && not (Lib.sections_are_opened ()) then
    user_err ?loc ~hdr:"vernac_constraint"
		 (str"Polymorphic universe constraints can only be declared"
		  ++ str " inside sections, use Monomorphic Constraint instead");
  do_constraint poly l

(**********************)
(* Modules            *)

let vernac_import export refl =
  Library.import_module export (List.map qualid_of_reference refl);
  Lib.add_frozen_state ()

let vernac_declare_module export (loc, id) binders_ast mty_ast =
  (* We check the state of the system (in section, in module type)
     and what module information is supplied *)
  if Lib.sections_are_opened () then
    error "Modules and Module Types are not allowed inside sections.";
  let binders_ast = List.map
   (fun (export,idl,ty) ->
     if not (Option.is_empty export) then
      error "Arguments of a functor declaration cannot be exported. Remove the \"Export\" and \"Import\" keywords from every functor argument."
     else (idl,ty)) binders_ast in
  let mp =
    Declaremods.declare_module Modintern.interp_module_ast
      id binders_ast (Enforce mty_ast) []
  in
  Dumpglob.dump_moddef ?loc mp "mod";
  if_verbose Feedback.msg_info (str "Module " ++ pr_id id ++ str " is declared");
  Option.iter (fun export -> vernac_import export [Ident (Loc.tag id)]) export

let vernac_define_module export (loc, id) binders_ast mty_ast_o mexpr_ast_l =
  (* We check the state of the system (in section, in module type)
     and what module information is supplied *)
  if Lib.sections_are_opened () then
    error "Modules and Module Types are not allowed inside sections.";
  match mexpr_ast_l with
    | [] ->
       check_no_pending_proofs ();
       let binders_ast,argsexport =
        List.fold_right
         (fun (export,idl,ty) (args,argsexport) ->
           (idl,ty)::args, (List.map (fun (_,i) -> export,i)idl)@argsexport) binders_ast
             ([],[]) in
       let mp =
         Declaremods.start_module Modintern.interp_module_ast
           export id binders_ast mty_ast_o
       in
       Dumpglob.dump_moddef ?loc mp "mod";
       if_verbose Feedback.msg_info
         (str "Interactive Module " ++ pr_id id ++ str " started");
       List.iter
         (fun (export,id) ->
           Option.iter
             (fun export -> vernac_import export [Ident (Loc.tag id)]) export
         ) argsexport
    | _::_ ->
       let binders_ast = List.map
        (fun (export,idl,ty) ->
          if not (Option.is_empty export) then
           error "Arguments of a functor definition can be imported only if the definition is interactive. Remove the \"Export\" and \"Import\" keywords from every functor argument."
          else (idl,ty)) binders_ast in
       let mp =
         Declaremods.declare_module Modintern.interp_module_ast
	   id binders_ast mty_ast_o mexpr_ast_l
       in
       Dumpglob.dump_moddef ?loc mp "mod";
       if_verbose Feedback.msg_info
	 (str "Module " ++ pr_id id ++ str " is defined");
       Option.iter (fun export -> vernac_import export [Ident (Loc.tag id)])
         export

let vernac_end_module export (loc,id as lid) =
  let mp = Declaremods.end_module () in
  Dumpglob.dump_modref ?loc mp "mod";
  if_verbose Feedback.msg_info (str "Module " ++ pr_id id ++ str " is defined");
  Option.iter (fun export -> vernac_import export [Ident lid]) export

let vernac_declare_module_type (loc,id) binders_ast mty_sign mty_ast_l =
  if Lib.sections_are_opened () then
    error "Modules and Module Types are not allowed inside sections.";

  match mty_ast_l with
    | [] ->
       check_no_pending_proofs ();
       let binders_ast,argsexport =
	 List.fold_right
         (fun (export,idl,ty) (args,argsexport) ->
           (idl,ty)::args, (List.map (fun (_,i) -> export,i)idl)@argsexport) binders_ast
             ([],[]) in

       let mp =
         Declaremods.start_modtype Modintern.interp_module_ast
           id binders_ast mty_sign
       in
       Dumpglob.dump_moddef ?loc mp "modtype";
       if_verbose Feedback.msg_info
	 (str "Interactive Module Type " ++ pr_id id ++ str " started");
       List.iter
         (fun (export,id) ->
           Option.iter
             (fun export -> vernac_import export [Ident (Loc.tag id)]) export
         ) argsexport

    | _ :: _ ->
	let binders_ast = List.map
          (fun (export,idl,ty) ->
            if not (Option.is_empty export) then
              error "Arguments of a functor definition can be imported only if the definition is interactive. Remove the \"Export\" and \"Import\" keywords from every functor argument."
            else (idl,ty)) binders_ast in
	let mp =
          Declaremods.declare_modtype Modintern.interp_module_ast
	    id binders_ast mty_sign mty_ast_l
        in
        Dumpglob.dump_moddef ?loc mp "modtype";
	if_verbose Feedback.msg_info
	  (str "Module Type " ++ pr_id id ++ str " is defined")

let vernac_end_modtype (loc,id) =
  let mp = Declaremods.end_modtype () in
  Dumpglob.dump_modref ?loc mp "modtype";
  if_verbose Feedback.msg_info (str "Module Type " ++ pr_id id ++ str " is defined")

let vernac_include l =
  Declaremods.declare_include Modintern.interp_module_ast l

(**********************)
(* Gallina extensions *)

(* Sections *)

let vernac_begin_section (_, id as lid) =
  check_no_pending_proofs ();
  Dumpglob.dump_definition lid true "sec";
  Lib.open_section id

let vernac_end_section (loc,_) =
  Dumpglob.dump_reference ?loc
    (DirPath.to_string (Lib.current_dirpath true)) "<>" "sec";
  Lib.close_section ()

let vernac_name_sec_hyp (_,id) set = Proof_using.name_set id set

(* Dispatcher of the "End" command *)

let vernac_end_segment (_,id as lid) =
  check_no_pending_proofs ();
  match Lib.find_opening_node id with
  | Lib.OpenedModule (false,export,_,_) -> vernac_end_module export lid
  | Lib.OpenedModule (true,_,_,_) -> vernac_end_modtype lid
  | Lib.OpenedSection _ -> vernac_end_section lid
  | _ -> assert false

(* Libraries *)

let vernac_require from import qidl =
  let qidl = List.map qualid_of_reference qidl in
  let root = match from with
  | None -> None
  | Some from ->
    let (_, qid) = Libnames.qualid_of_reference from in
    let (hd, tl) = Libnames.repr_qualid qid in
    Some (Libnames.add_dirpath_suffix hd tl)
  in
  let locate (loc, qid) =
    try
      let warn = not !Flags.quiet in
      let (_, dir, f) = Library.locate_qualified_library ?root ~warn qid in
      (dir, f)
    with
      | Library.LibUnmappedDir -> err_unmapped_library ?loc ?from:root qid
      | Library.LibNotFound -> err_notfound_library ?loc ?from:root qid
  in
  let modrefl = List.map locate qidl in
  if Dumpglob.dump () then
    List.iter2 (fun (loc, _) dp -> Dumpglob.dump_libref ?loc dp "lib") qidl (List.map fst modrefl);
  Library.require_library_from_dirpath modrefl import

(* Coercions and canonical structures *)

let vernac_canonical r =
  Recordops.declare_canonical_structure (smart_global r)

let vernac_coercion locality poly local ref qids qidt =
  let local = enforce_locality locality local in
  let target = cl_of_qualid qidt in
  let source = cl_of_qualid qids in
  let ref' = smart_global ref in
  Class.try_add_new_coercion_with_target ref' ~local poly ~source ~target;
  if_verbose Feedback.msg_info (pr_global ref' ++ str " is now a coercion")

let vernac_identity_coercion locality poly local id qids qidt =
  let local = enforce_locality locality local in
  let target = cl_of_qualid qidt in
  let source = cl_of_qualid qids in
  Class.try_add_new_identity_coercion id ~local poly ~source ~target

(* Type classes *)

let vernac_instance abst locality poly sup inst props pri =
  let global = not (make_section_locality locality) in
  Dumpglob.dump_constraint inst false "inst";
  ignore(Classes.new_instance ~abstract:abst ~global poly sup inst props pri)

let vernac_context poly l =
  if not (Classes.context poly l) then Feedback.feedback Feedback.AddedAxiom

let vernac_declare_instances locality insts =
  let glob = not (make_section_locality locality) in
  List.iter (fun (id, info) -> Classes.existing_instance glob id (Some info)) insts

let vernac_declare_class id =
  Record.declare_existing_class (Nametab.global id)

(***********)
(* Solving *)

let command_focus = Proof.new_focus_kind ()
let focus_command_cond = Proof.no_cond command_focus

  (* A command which should be a tactic. It has been
     added by Christine to patch an error in the design of the proof
     machine, and enables to instantiate existential variables when
     there are no more goals to solve. It cannot be a tactic since
     all tactics fail if there are no further goals to prove. *)

let vernac_solve_existential = instantiate_nth_evar_com

let vernac_set_end_tac tac =
  let open Genintern in
  let env = { genv = Global.env (); ltacvars = Id.Set.empty } in
  let _, tac = Genintern.generic_intern env tac in
  if not (refining ()) then
    error "Unknown command of the non proof-editing mode.";
  set_end_tac tac
    (* TO DO verifier s'il faut pas mettre exist s | TacId s ici*)

let vernac_set_used_variables e =
  let env = Global.env () in
  let tys =
    List.map snd (Proof.initial_goals (Proof_global.give_me_the_proof ())) in
  let tys = List.map EConstr.Unsafe.to_constr tys in
  let l = Proof_using.process_expr env e tys in
  let vars = Environ.named_context env in
  List.iter (fun id -> 
    if not (List.exists (NamedDecl.get_id %> Id.equal id) vars) then
      user_err ~hdr:"vernac_set_used_variables"
        (str "Unknown variable: " ++ pr_id id))
    l;
  let _, to_clear = set_used_variables l in
  let to_clear = List.map snd to_clear in
  Proof_global.with_current_proof begin fun _ p ->
    if List.is_empty to_clear then (p, ())
    else
      let tac = Tactics.clear to_clear in
      fst (solve SelectAll None tac p), ()
  end

(*****************************)
(* Auxiliary file management *)

let expand filename =
  Envars.expand_path_macros ~warn:(fun x -> Feedback.msg_warning (str x)) filename

let vernac_add_loadpath implicit pdir ldiropt =
  let pdir = expand pdir in
  let alias = Option.default Nameops.default_root_prefix ldiropt in
  Mltop.add_rec_path Mltop.AddTopML ~unix_path:pdir ~coq_root:alias ~implicit

let vernac_remove_loadpath path =
  Loadpath.remove_load_path (expand path)

  (* Coq syntax for ML or system commands *)

let vernac_add_ml_path isrec path =
  (if isrec then Mltop.add_rec_ml_dir else Mltop.add_ml_dir) (expand path)

let vernac_declare_ml_module locality l =
  let local = make_locality locality in
  Mltop.declare_ml_modules local (List.map expand l)

let vernac_chdir = function
  | None -> Feedback.msg_notice (str (Sys.getcwd()))
  | Some path ->
      begin
	try Sys.chdir (expand path)
	with Sys_error err ->
	  (* Cd is typically used to control the output directory of
	  extraction. A failed Cd could lead to overwriting .ml files
	  so we make it an error. *)
	  CErrors.error ("Cd failed: " ^ err)
      end;
      if_verbose Feedback.msg_info (str (Sys.getcwd()))


(********************)
(* State management *)

let vernac_write_state file =
  Pfedit.delete_all_proofs ();
  let file = CUnix.make_suffix file ".coq" in
  States.extern_state file

let vernac_restore_state file =
  Pfedit.delete_all_proofs ();
  let file = Loadpath.locate_file (CUnix.make_suffix file ".coq") in
  States.intern_state file

(************)
(* Commands *)

let vernac_create_hintdb locality id b =
  let local = make_module_locality locality in
  Hints.create_hint_db local id full_transparent_state b

let vernac_remove_hints locality dbs ids =
  let local = make_module_locality locality in
  Hints.remove_hints local dbs (List.map Smartlocate.global_with_alias ids)

let vernac_hints locality poly local lb h =
  let local = enforce_module_locality locality local in
  Hints.add_hints local lb (Hints.interp_hints poly h)

let vernac_syntactic_definition locality lid x local y =
  Dumpglob.dump_definition lid false "syndef";
  let local = enforce_module_locality locality local in
  Metasyntax.add_syntactic_definition (snd lid) x local y

let vernac_declare_implicits locality r l =
  let local = make_section_locality locality in
  match l with
  | [] ->
      Impargs.declare_implicits local (smart_global r)
  | _::_ as imps ->
      Impargs.declare_manual_implicits local (smart_global r) ~enriching:false
	(List.map (List.map (fun (ex,b,f) -> ex, (b,true,f))) imps)

let warn_arguments_assert =
  CWarnings.create ~name:"arguments-assert" ~category:"vernacular"
         (fun sr ->
          strbrk "This command is just asserting the names of arguments of " ++
            pr_global sr ++ strbrk". If this is what you want add " ++
            strbrk "': assert' to silence the warning. If you want " ++
            strbrk "to clear implicit arguments add ': clear implicits'. " ++
            strbrk "If you want to clear notation scopes add ': clear scopes'")

(* [nargs_for_red] is the number of arguments required to trigger reduction,
   [args] is the main list of arguments statuses,
   [more_implicits] is a list of extra lists of implicit statuses  *)
let vernac_arguments locality reference args more_implicits nargs_for_red flags =
  let assert_flag = List.mem `Assert flags in
  let rename_flag = List.mem `Rename flags in
  let clear_scopes_flag = List.mem `ClearScopes flags in
  let extra_scopes_flag = List.mem `ExtraScopes flags in
  let clear_implicits_flag = List.mem `ClearImplicits flags in
  let default_implicits_flag = List.mem `DefaultImplicits flags in
  let never_unfold_flag = List.mem `ReductionNeverUnfold flags in

  let err_incompat x y =
    error ("Options \""^x^"\" and \""^y^"\" are incompatible.") in

  if assert_flag && rename_flag then
    err_incompat "assert" "rename";
  if Option.has_some nargs_for_red && never_unfold_flag then
    err_incompat "simpl never" "/";
  if never_unfold_flag && List.mem `ReductionDontExposeCase flags then
    err_incompat "simpl never" "simpl nomatch";
  if clear_scopes_flag && extra_scopes_flag then
    err_incompat "clear scopes" "extra scopes";
  if clear_implicits_flag && default_implicits_flag then
    err_incompat "clear implicits" "default implicits";

  let sr = smart_global reference in
  let inf_names =
    let ty = Global.type_of_global_unsafe sr in
    Impargs.compute_implicits_names (Global.env ()) ty
  in
  let prev_names =
    try Arguments_renaming.arguments_names sr with Not_found -> inf_names
  in
  let num_args = List.length inf_names in
  assert (Int.equal num_args (List.length prev_names));

  let names_of args = List.map (fun a -> a.name) args in

  (* Checks *)

  let err_extra_args names =
    user_err ~hdr:"vernac_declare_arguments"
                 (strbrk "Extra arguments: " ++
                    prlist_with_sep pr_comma pr_name names ++ str ".")
  in
  let err_missing_args names =
    user_err ~hdr:"vernac_declare_arguments"
                 (strbrk "The following arguments are not declared: " ++
                    prlist_with_sep pr_comma pr_name names ++ str ".")
  in

  let rec check_extra_args extra_args =
    match extra_args with
    | [] -> ()
    | { notation_scope = None } :: _ -> err_extra_args (names_of extra_args)
    | { name = Anonymous; notation_scope = Some _ } :: args ->
       check_extra_args args
    | _ ->
       error "Extra notation scopes can be set on anonymous and explicit arguments only."
  in

  let args, scopes =
    let scopes = List.map (fun { notation_scope = s } -> s) args in
    if List.length args > num_args then
      let args, extra_args = List.chop num_args args in
      if extra_scopes_flag then
        (check_extra_args extra_args; (args, scopes))
      else err_extra_args (names_of extra_args)
    else args, scopes
  in

  if Option.cata (fun n -> n > num_args) false nargs_for_red then
    error "The \"/\" modifier should be put before any extra scope.";

  let scopes_specified = List.exists Option.has_some scopes in
  
  if scopes_specified && clear_scopes_flag then
    error "The \"clear scopes\" flag is incompatible with scope annotations.";

  let names = List.map (fun { name } -> name) args in
  let names = names :: List.map (List.map fst) more_implicits in

  let rename_flag_required = ref false in
  let example_renaming = ref None in
  let save_example_renaming renaming =
    rename_flag_required := !rename_flag_required
                            || not (Name.equal (fst renaming) Anonymous);
    if Option.is_empty !example_renaming then
      example_renaming := Some renaming
  in

  let rec names_union names1 names2 =
    match names1, names2 with
    | [], [] -> []
    | _ :: _, [] -> names1
    | [], _ :: _ -> names2
    | (Name _ as name) :: names1, Anonymous :: names2
    | Anonymous :: names1, (Name _ as name) :: names2 ->
       name :: names_union names1 names2
    | name1 :: names1, name2 :: names2 ->
       if Name.equal name1 name2 then
         name1 :: names_union names1 names2
       else error "Argument lists should agree on the names they provide."
  in

  let names = List.fold_left names_union [] names in

  let rec rename prev_names names =
    match prev_names, names with
    | [], [] -> []
    | [], _ :: _ -> err_extra_args names
    | _ :: _, [] when assert_flag ->
       (* Error messages are expressed in terms of original names, not
            renamed ones. *)
       err_missing_args (List.lastn (List.length prev_names) inf_names)
    | _ :: _, [] -> prev_names
    | prev :: prev_names, Anonymous :: names ->
       prev :: rename prev_names names
    | prev :: prev_names, (Name id as name) :: names ->
       if not (Name.equal prev name) then save_example_renaming (prev,name);
       name :: rename prev_names names
  in
  
  let names = rename prev_names names in
  let renaming_specified = Option.has_some !example_renaming in

  if !rename_flag_required && not rename_flag then
    user_err ~hdr:"vernac_declare_arguments"
      (strbrk "To rename arguments the \"rename\" flag must be specified."
    ++ spc () ++
       match !example_renaming with
       | None -> mt ()
       | Some (o,n) ->
          str "Argument " ++ pr_name o ++
            str " renamed to " ++ pr_name n ++ str ".");

  let duplicate_names =
    List.duplicates Name.equal (List.filter ((!=) Anonymous) names)
  in
  if not (List.is_empty duplicate_names) then begin
    let duplicates = prlist_with_sep pr_comma pr_name duplicate_names in
    user_err (strbrk "Some argument names are duplicated: " ++ duplicates)
  end;

  (* Parts of this code are overly complicated because the implicit arguments
     API is completely crazy: positions (ExplByPos) are elaborated to
     names. This is broken by design, since not all arguments have names. So
     even though we eventually want to map only positions to implicit statuses,
     we have to check whether the corresponding arguments have names, not to
     trigger an error in the impargs code. Even better, the names we have to
     check are not the current ones (after previous renamings), but the original
     ones (inferred from the type). *)

  let implicits =
    List.map (fun { name; implicit_status = i } -> (name,i)) args
  in
  let implicits = implicits :: more_implicits in

  let open Vernacexpr in
  let rec build_implicits inf_names implicits =
    match inf_names, implicits with
    | _, [] -> []
    | _ :: inf_names, (_, NotImplicit) :: implicits ->
       build_implicits inf_names implicits

    (* With the current impargs API, it is impossible to make an originally
       anonymous argument implicit *)
    | Anonymous :: _, (name, _) :: _ ->
       user_err ~hdr:"vernac_declare_arguments"
                    (strbrk"Argument "++ pr_name name ++ 
                       strbrk " cannot be declared implicit.")

    | Name id :: inf_names, (name, impl) :: implicits ->
       let max = impl = MaximallyImplicit in
       (ExplByName id,max,false) :: build_implicits inf_names implicits
    
    | _ -> assert false (* already checked in [names_union] *)
  in
  
  let implicits = List.map (build_implicits inf_names) implicits in
  let implicits_specified = match implicits with [[]] -> false | _ -> true in

  if implicits_specified && clear_implicits_flag then
    error "The \"clear implicits\" flag is incompatible with implicit annotations";

  if implicits_specified && default_implicits_flag then
    error "The \"default implicits\" flag is incompatible with implicit annotations";

  let rargs =
    Util.List.map_filter (function (n, true) -> Some n | _ -> None)
      (Util.List.map_i (fun i { recarg_like = b } -> i, b) 0 args)
  in

  let rec narrow = function
    | #Reductionops.ReductionBehaviour.flag as x :: tl -> x :: narrow tl
    | [] -> [] | _ :: tl -> narrow tl
  in
  let red_flags = narrow flags in
  let red_modifiers_specified =
    not (List.is_empty rargs) || Option.has_some nargs_for_red
    || not (List.is_empty red_flags)
  in

  if not (List.is_empty rargs) && never_unfold_flag then
    err_incompat "simpl never" "!";


  (* Actions *)

  if renaming_specified then begin
    let local = make_section_locality locality in
    Arguments_renaming.rename_arguments local sr names
  end;

  if scopes_specified || clear_scopes_flag then begin
      let scopes = List.map (Option.map (fun (loc,k) -> 
        try ignore (Notation.find_scope k); k
        with UserError _ ->
          Notation.find_delimiters_scope ?loc k)) scopes
      in
      vernac_arguments_scope locality reference scopes
    end;

  if implicits_specified || clear_implicits_flag then
    vernac_declare_implicits locality reference implicits;

  if default_implicits_flag then
    vernac_declare_implicits locality reference [];

  if red_modifiers_specified then begin
    match sr with
    | ConstRef _ as c ->
       Reductionops.ReductionBehaviour.set
         (make_section_locality locality) c
         (rargs, Option.default ~-1 nargs_for_red, red_flags)
    | _ -> user_err
             (strbrk "Modifiers of the behavior of the simpl tactic "++
              strbrk "are relevant for constants only.")
  end;

 if not (renaming_specified ||
         implicits_specified ||
         scopes_specified ||
         red_modifiers_specified) && (List.is_empty flags) then
    warn_arguments_assert sr

let default_env () = {
  Notation_term.ninterp_var_type = Id.Map.empty;
  ninterp_rec_vars = Id.Map.empty;
}

let vernac_reserve bl =
  let sb_decl = (fun (idl,c) ->
    let env = Global.env() in
    let sigma = Evd.from_env env in
    let t,ctx = Constrintern.interp_type env sigma c in
    let t = Detyping.detype false [] env (Evd.from_ctx ctx) (EConstr.of_constr t) in
    let t,_ = Notation_ops.notation_constr_of_glob_constr (default_env ()) t in
    Reserve.declare_reserved_type idl t)
  in List.iter sb_decl bl

let vernac_generalizable locality =
  let local = make_non_locality locality in
  Implicit_quantifiers.declare_generalizable local

let _ =
  declare_bool_option
    { optsync  = false;
      optdepr  = false;
      optname  = "silent";
      optkey   = ["Silent"];
      optread  = (fun () -> !Flags.quiet);
      optwrite = ((:=) Flags.quiet) }

let _ =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "implicit arguments";
      optkey   = ["Implicit";"Arguments"];
      optread  = Impargs.is_implicit_args;
      optwrite = Impargs.make_implicit_args }

let _ =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "strict implicit arguments";
      optkey   = ["Strict";"Implicit"];
      optread  = Impargs.is_strict_implicit_args;
      optwrite = Impargs.make_strict_implicit_args }

let _ =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "strong strict implicit arguments";
      optkey   = ["Strongly";"Strict";"Implicit"];
      optread  = Impargs.is_strongly_strict_implicit_args;
      optwrite = Impargs.make_strongly_strict_implicit_args }

let _ =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "contextual implicit arguments";
      optkey   = ["Contextual";"Implicit"];
      optread  = Impargs.is_contextual_implicit_args;
      optwrite = Impargs.make_contextual_implicit_args }

let _ =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "implicit status of reversible patterns";
      optkey   = ["Reversible";"Pattern";"Implicit"];
      optread  = Impargs.is_reversible_pattern_implicit_args;
      optwrite = Impargs.make_reversible_pattern_implicit_args }

let _ =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "maximal insertion of implicit";
      optkey   = ["Maximal";"Implicit";"Insertion"];
      optread  = Impargs.is_maximal_implicit_args;
      optwrite = Impargs.make_maximal_implicit_args }

let _ =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "automatic introduction of variables";
      optkey   = ["Automatic";"Introduction"];
      optread  = Flags.is_auto_intros;
      optwrite = make_auto_intros }

let _ =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "coercion printing";
      optkey   = ["Printing";"Coercions"];
      optread  = (fun () -> !Constrextern.print_coercions);
      optwrite = (fun b ->  Constrextern.print_coercions := b) }

let _ =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "printing of existential variable instances";
      optkey   = ["Printing";"Existential";"Instances"];
      optread  = (fun () -> !Detyping.print_evar_arguments);
      optwrite = (:=) Detyping.print_evar_arguments }

let _ =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "implicit arguments printing";
      optkey   = ["Printing";"Implicit"];
      optread  = (fun () -> !Constrextern.print_implicits);
      optwrite = (fun b ->  Constrextern.print_implicits := b) }

let _ =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "implicit arguments defensive printing";
      optkey   = ["Printing";"Implicit";"Defensive"];
      optread  = (fun () -> !Constrextern.print_implicits_defensive);
      optwrite = (fun b ->  Constrextern.print_implicits_defensive := b) }

let _ =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "projection printing using dot notation";
      optkey   = ["Printing";"Projections"];
      optread  = (fun () -> !Constrextern.print_projections);
      optwrite = (fun b ->  Constrextern.print_projections := b) }

let _ =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "notations printing";
      optkey   = ["Printing";"Notations"];
      optread  = (fun () -> not !Constrextern.print_no_symbol);
      optwrite = (fun b ->  Constrextern.print_no_symbol := not b) }

let _ =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "raw printing";
      optkey   = ["Printing";"All"];
      optread  = (fun () -> !Flags.raw_print);
      optwrite = (fun b -> Flags.raw_print := b) }

let _ =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "use of the program extension";
      optkey   = ["Program";"Mode"];
      optread  = (fun () -> !Flags.program_mode);
      optwrite = (fun b -> Flags.program_mode:=b) }

let _ =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "universe polymorphism";
      optkey   = ["Universe"; "Polymorphism"];
      optread  = Flags.is_universe_polymorphism;
      optwrite = Flags.make_universe_polymorphism }

let _ =
  declare_int_option
    { optsync  = true;
      optdepr  = false;
      optname  = "the level of inlining during functor application";
      optkey   = ["Inline";"Level"];
      optread  = (fun () -> Some (Flags.get_inline_level ()));
      optwrite = (fun o ->
	           let lev = Option.default Flags.default_inline_level o in
	           Flags.set_inline_level lev) }

let _ =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "kernel term sharing";
      optkey   = ["Kernel"; "Term"; "Sharing"];
      optread  = (fun () -> !CClosure.share);
      optwrite = (fun b -> CClosure.share := b) }

(* No more undo limit in the new proof engine.
   The command still exists for compatibility (e.g. with ProofGeneral) *)

let _ =
  declare_int_option
    { optsync  = false;
      optdepr  = true;
      optname  = "the undo limit (OBSOLETE)";
      optkey   = ["Undo"];
      optread  = (fun _ -> None);
      optwrite = (fun _ -> ()) }

let _ =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "display compact goal contexts";
      optkey   = ["Printing";"Compact";"Contexts"];
      optread  = (fun () -> Printer.get_compact_context());
      optwrite = (fun b -> Printer.set_compact_context b) }

let _ =
  declare_int_option
    { optsync  = true;
      optdepr  = false;
      optname  = "the printing depth";
      optkey   = ["Printing";"Depth"];
      optread  = Topfmt.get_depth_boxes;
      optwrite = Topfmt.set_depth_boxes }

let _ =
  declare_int_option
    { optsync  = true;
      optdepr  = false;
      optname  = "the printing width";
      optkey   = ["Printing";"Width"];
      optread  = Topfmt.get_margin;
      optwrite = Topfmt.set_margin }

let _ =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "printing of universes";
      optkey   = ["Printing";"Universes"];
      optread  = (fun () -> !Constrextern.print_universes);
      optwrite = (fun b -> Constrextern.print_universes:=b) }
     
let _ =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "dumping bytecode after compilation";
      optkey   = ["Dump";"Bytecode"];
      optread  = Flags.get_dump_bytecode;
      optwrite = Flags.set_dump_bytecode }

let _ =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "explicitly parsing implicit arguments";
      optkey   = ["Parsing";"Explicit"];
      optread  = (fun () -> !Constrintern.parsing_explicit);
      optwrite = (fun b ->  Constrintern.parsing_explicit := b) }

let _ =
  declare_string_option ~preprocess:CWarnings.normalize_flags_string
    { optsync  = true;
      optdepr  = false;
      optname  = "warnings display";
      optkey   = ["Warnings"];
      optread  = CWarnings.get_flags;
      optwrite = CWarnings.set_flags }

let vernac_set_strategy locality l =
  let local = make_locality locality in
  let glob_ref r =
    match smart_global r with
      | ConstRef sp -> EvalConstRef sp
      | VarRef id -> EvalVarRef id
      | _ -> error
          "cannot set an inductive type or a constructor as transparent" in
  let l = List.map (fun (lev,ql) -> (lev,List.map glob_ref ql)) l in
  Redexpr.set_strategy local l

let vernac_set_opacity locality (v,l) =
  let local = make_non_locality locality in
  let glob_ref r =
    match smart_global r with
      | ConstRef sp -> EvalConstRef sp
      | VarRef id -> EvalVarRef id
      | _ -> error
          "cannot set an inductive type or a constructor as transparent" in
  let l = List.map glob_ref l in
  Redexpr.set_strategy local [v,l]

let vernac_set_option locality key = function
  | StringValue s -> set_string_option_value_gen locality key s
  | StringOptValue (Some s) -> set_string_option_value_gen locality key s
  | StringOptValue None -> unset_option_value_gen locality key
  | IntValue n -> set_int_option_value_gen locality key n
  | BoolValue b -> set_bool_option_value_gen locality key b

let vernac_set_append_option locality key s =
  set_string_option_append_value_gen locality key s

let vernac_unset_option locality key =
  unset_option_value_gen locality key

let vernac_add_option key lv =
  let f = function
    | StringRefValue s -> (get_string_table key)#add s
    | QualidRefValue locqid -> (get_ref_table key)#add locqid
  in
  try List.iter f lv with Not_found -> error_undeclared_key key

let vernac_remove_option key lv =
  let f = function
  | StringRefValue s -> (get_string_table key)#remove s
  | QualidRefValue locqid -> (get_ref_table key)#remove locqid
  in
  try List.iter f lv with Not_found -> error_undeclared_key key

let vernac_mem_option key lv =
  let f = function
  | StringRefValue s -> (get_string_table key)#mem s
  | QualidRefValue locqid -> (get_ref_table key)#mem locqid
  in
  try List.iter f lv with Not_found -> error_undeclared_key key

let vernac_print_option key =
  try (get_ref_table key)#print
  with Not_found ->
  try (get_string_table key)#print
  with Not_found ->
  try print_option_value key
  with Not_found -> error_undeclared_key key

let get_current_context_of_args = function
  | Some n -> get_goal_context n
  | None -> get_current_context ()

let query_command_selector ?loc = function
  | None -> None
  | Some (SelectNth n) -> Some n
  | _ -> user_err ?loc ~hdr:"query_command_selector"
      (str "Query commands only support the single numbered goal selector.")

let vernac_check_may_eval ?loc redexp glopt rc =
  let glopt = query_command_selector ?loc glopt in
  let (sigma, env) = get_current_context_of_args glopt in
  let sigma', c = interp_open_constr env sigma rc in
  let c = EConstr.Unsafe.to_constr c in
  let sigma' = Evarconv.solve_unif_constraints_with_heuristics env sigma' in
  Evarconv.check_problems_are_solved env sigma';
  let sigma',nf = Evarutil.nf_evars_and_universes sigma' in
  let pl, uctx = Evd.universe_context sigma' in
  let env = Environ.push_context uctx (Evarutil.nf_env_evar sigma' env) in
  let c = nf c in
  let j =
    if Evarutil.has_undefined_evars sigma' (EConstr.of_constr c) then
      Evarutil.j_nf_evar sigma' (Retyping.get_judgment_of env sigma' (EConstr.of_constr c))
    else
      (* OK to call kernel which does not support evars *)
      Termops.on_judgment EConstr.of_constr (Arguments_renaming.rename_typing env c)
  in
  match redexp with
    | None ->
        let evars_of_term c = Evarutil.undefined_evars_of_term sigma' c in
        let l = Evar.Set.union (evars_of_term j.Environ.uj_val) (evars_of_term j.Environ.uj_type) in
        let j = { j with Environ.uj_type = Reductionops.nf_betaiota sigma' j.Environ.uj_type } in
	Feedback.msg_notice (print_judgment env sigma' j ++
                    pr_ne_evar_set (fnl () ++ str "where" ++ fnl ()) (mt ()) sigma' l ++
                    Printer.pr_universe_ctx sigma uctx)
    | Some r ->
        let (sigma',r_interp) = Hook.get f_interp_redexp env sigma' r in
	let redfun env evm c =
          let (redfun, _) = reduction_of_red_expr env r_interp in
          let evm = Sigma.Unsafe.of_evar_map evm in
          let Sigma (c, _, _) = redfun.Reductionops.e_redfun env evm c in
          c
        in
	Feedback.msg_notice (print_eval redfun env sigma' rc j)

let vernac_declare_reduction locality s r =
  let local = make_locality locality in
  declare_red_expr local s (snd (Hook.get f_interp_redexp (Global.env()) Evd.empty r))

  (* The same but avoiding the current goal context if any *)
let vernac_global_check c =
  let env = Global.env() in
  let sigma = Evd.from_env env in
  let c,ctx = interp_constr env sigma c in
  let senv = Global.safe_env() in
  let cstrs = snd (UState.context_set ctx) in
  let senv = Safe_typing.add_constraints cstrs senv in
  let j = Safe_typing.typing senv c in
  let env = Safe_typing.env_of_safe_env senv in
    Feedback.msg_notice (print_safe_judgment env sigma j)


let get_nth_goal n =
  let pf = get_pftreestate() in
  let {Evd.it=gls ; sigma=sigma; } = Proof.V82.subgoals pf in
  let gl = {Evd.it=List.nth gls (n-1) ; sigma = sigma; } in
  gl
  
exception NoHyp
(* Printing "About" information of a hypothesis of the current goal.
   We only print the type and a small statement to this comes from the
   goal. Precondition: there must be at least one current goal. *)
let print_about_hyp_globs ?loc ref_or_by_not glopt =
  let open Context.Named.Declaration in
  try
    let glnumopt = query_command_selector ?loc glopt in
    let gl,id =
      match glnumopt,ref_or_by_not with
      | None,AN (Ident (_loc,id)) -> (* goal number not given, catch any failure *)
	 (try get_nth_goal 1,id with _ -> raise NoHyp)
      | Some n,AN (Ident (_loc,id)) ->  (* goal number given, catch if wong *)
	 (try get_nth_goal n,id
	  with
	    Failure _ -> user_err ?loc ~hdr:"print_about_hyp_globs"
                          (str "No such goal: " ++ int n ++ str "."))
      | _ , _ -> raise NoHyp in
    let hyps = pf_hyps gl in
    let decl = Context.Named.lookup id hyps in
    let natureofid = match decl with
                     | LocalAssum _ -> "Hypothesis"
                     | LocalDef (_,bdy,_) ->"Constant (let in)" in
    v 0 (pr_id id ++ str":" ++ pr_econstr (NamedDecl.get_type decl) ++ fnl() ++ fnl()
	 ++ str natureofid ++ str " of the goal context.")
  with (* fallback to globals *)
    | NoHyp | Not_found -> print_about ref_or_by_not

	       
let vernac_print ?loc = let open Feedback in function
  | PrintTables -> msg_notice (print_tables ())
  | PrintFullContext-> msg_notice (print_full_context_typ ())
  | PrintSectionContext qid -> msg_notice (print_sec_context_typ qid)
  | PrintInspect n -> msg_notice (inspect n)
  | PrintGrammar ent -> msg_notice (Metasyntax.pr_grammar ent)
  | PrintLoadPath dir -> (* For compatibility ? *) msg_notice (print_loadpath dir)
  | PrintModules -> msg_notice (print_modules ())
  | PrintModule qid -> print_module qid
  | PrintModuleType qid -> print_modtype qid
  | PrintNamespace ns -> print_namespace ns
  | PrintMLLoadPath -> msg_notice (Mltop.print_ml_path ())
  | PrintMLModules -> msg_notice (Mltop.print_ml_modules ())
  | PrintDebugGC -> msg_notice (Mltop.print_gc ())
  | PrintName qid -> dump_global qid; msg_notice (print_name qid)
  | PrintGraph -> msg_notice (Prettyp.print_graph())
  | PrintClasses -> msg_notice (Prettyp.print_classes())
  | PrintTypeClasses -> msg_notice (Prettyp.print_typeclasses())
  | PrintInstances c -> msg_notice (Prettyp.print_instances (smart_global c))
  | PrintCoercions -> msg_notice (Prettyp.print_coercions())
  | PrintCoercionPaths (cls,clt) ->
      msg_notice (Prettyp.print_path_between (cl_of_qualid cls) (cl_of_qualid clt))
  | PrintCanonicalConversions -> msg_notice (Prettyp.print_canonical_projections ())
  | PrintUniverses (b, dst) ->
     let univ = Global.universes () in
     let univ = if b then UGraph.sort_universes univ else univ in
     let pr_remaining =
       if Global.is_joined_environment () then mt ()
       else str"There may remain asynchronous universe constraints"
     in
     begin match dst with
     | None -> msg_notice (UGraph.pr_universes Universes.pr_with_global_universes univ ++ pr_remaining)
     | Some s -> dump_universes_gen univ s
     end
  | PrintHint r -> msg_notice (Hints.pr_hint_ref (smart_global r))
  | PrintHintGoal -> msg_notice (Hints.pr_applicable_hint ())
  | PrintHintDbName s -> msg_notice (Hints.pr_hint_db_by_name s)
  | PrintHintDb -> msg_notice (Hints.pr_searchtable ())
  | PrintScopes ->
      msg_notice (Notation.pr_scopes (Constrextern.without_symbols pr_lglob_constr))
  | PrintScope s ->
      msg_notice (Notation.pr_scope (Constrextern.without_symbols pr_lglob_constr) s)
  | PrintVisibility s ->
      msg_notice (Notation.pr_visibility (Constrextern.without_symbols pr_lglob_constr) s)
  | PrintAbout (ref_or_by_not,glnumopt) ->
     msg_notice (print_about_hyp_globs ?loc ref_or_by_not glnumopt)
  | PrintImplicit qid ->
    dump_global qid; msg_notice (print_impargs qid)
  | PrintAssumptions (o,t,r) ->
      (* Prints all the axioms and section variables used by a term *)
      let gr = smart_global r in
      let cstr = printable_constr_of_global gr in
      let st = Conv_oracle.get_transp_state (Environ.oracle (Global.env())) in
      let nassums =
	Assumptions.assumptions st ~add_opaque:o ~add_transparent:t gr cstr in
      msg_notice (Printer.pr_assumptionset (Global.env ()) nassums)
  | PrintStrategy r -> print_strategy r

let global_module r =
  let (loc,qid) = qualid_of_reference r in
  try Nametab.full_name_module qid
  with Not_found ->
    user_err ?loc ~hdr:"global_module"
     (str "Module/section " ++ pr_qualid qid ++ str " not found.")

let interp_search_restriction = function
  | SearchOutside l -> (List.map global_module l, true)
  | SearchInside l -> (List.map global_module l, false)

open Search

let interp_search_about_item env =
  function
  | SearchSubPattern pat ->
      let _,pat = intern_constr_pattern env pat in
      GlobSearchSubPattern pat
  | SearchString (s,None) when Id.is_valid s ->
      GlobSearchString s
  | SearchString (s,sc) ->
      try
	let ref =
	  Notation.interp_notation_as_global_reference
	    (fun _ -> true) s sc in
	GlobSearchSubPattern (Pattern.PRef ref)
      with UserError _ ->
	user_err ~hdr:"interp_search_about_item"
          (str "Unable to interp \"" ++ str s ++ str "\" either as a reference or as an identifier component")

(* 05f22a5d6d5b8e3e80f1a37321708ce401834430 introduced the
   `search_output_name_only` option to avoid excessive printing when
   searching.

   The motivation was to make search usable for IDE completion,
   however, it is still too slow due to the non-indexed nature of the
   underlying search mechanism.

   In the future we should deprecate the option and provide a fast,
   indexed name-searching interface.
*)
let search_output_name_only = ref false

let _ =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "output-name-only search";
      optkey   = ["Search";"Output";"Name";"Only"];
      optread  = (fun () -> !search_output_name_only);
      optwrite = (:=) search_output_name_only }

let vernac_search ?loc s gopt r =
  let gopt = query_command_selector ?loc gopt in
  let r = interp_search_restriction r in
  let env,gopt =
    match gopt with | None ->
      (* 1st goal by default if it exists, otherwise no goal at all *)
      (try snd (Pfedit.get_goal_context 1) , Some 1
       with _ -> Global.env (),None)
    (* if goal selector is given and wrong, then let exceptions be raised. *)
    | Some g -> snd (Pfedit.get_goal_context g) , Some g
  in
  let get_pattern c = snd (intern_constr_pattern env c) in
  let pr_search ref env c =
    let pr = pr_global ref in
    let pp = if !search_output_name_only
      then pr
      else begin
        let pc = pr_lconstr_env env Evd.empty c in
        hov 2 (pr ++ str":" ++ spc () ++ pc)
      end
    in Feedback.msg_notice pp
  in
  match s with
  | SearchPattern c ->
      (Search.search_pattern gopt (get_pattern c) r |> Search.prioritize_search) pr_search
  | SearchRewrite c ->
      (Search.search_rewrite gopt (get_pattern c) r |> Search.prioritize_search) pr_search
  | SearchHead c ->
      (Search.search_by_head gopt (get_pattern c) r |> Search.prioritize_search) pr_search
  | SearchAbout sl ->
      (Search.search_about gopt (List.map (on_snd (interp_search_about_item env)) sl) r |> Search.prioritize_search) pr_search

let vernac_locate = let open Feedback in function
  | LocateAny (AN qid)  -> msg_notice (print_located_qualid qid)
  | LocateTerm (AN qid) -> msg_notice (print_located_term qid)
  | LocateAny (ByNotation (_, (ntn, sc))) (** TODO : handle Ltac notations *)
  | LocateTerm (ByNotation (_, (ntn, sc))) ->
      msg_notice
        (Notation.locate_notation
          (Constrextern.without_symbols pr_lglob_constr) ntn sc)
  | LocateLibrary qid -> print_located_library qid
  | LocateModule qid -> msg_notice (print_located_module qid)
  | LocateTactic qid -> msg_notice (print_located_tactic qid)
  | LocateFile f -> msg_notice (locate_file f)

let vernac_register id r =
 if Pfedit.refining () then
    error "Cannot register a primitive while in proof editing mode.";
  let t = (Constrintern.global_reference (snd id)) in
  if not (isConst t) then
    error "Register inline: a constant is expected";
  let kn = destConst t in
  match r with
  | RegisterInline -> Global.register_inline (Univ.out_punivs kn)

(********************)
(* Proof management *)

let vernac_focus gln =
  Proof_global.simple_with_current_proof (fun _ p ->
    match gln with
      | None -> Proof.focus focus_command_cond () 1 p
      | Some 0 ->
         CErrors.error "Invalid goal number: 0. Goal numbering starts with 1."
      | Some n ->
         Proof.focus focus_command_cond () n p)

  (* Unfocuses one step in the focus stack. *)
let vernac_unfocus () =
  Proof_global.simple_with_current_proof
    (fun _ p -> Proof.unfocus command_focus p ())

(* Checks that a proof is fully unfocused. Raises an error if not. *)
let vernac_unfocused () =
  let p = Proof_global.give_me_the_proof () in
  if Proof.unfocused p then
    Feedback.msg_notice (str"The proof is indeed fully unfocused.")
  else
    error "The proof is not fully unfocused."


(* BeginSubproof / EndSubproof. 
    BeginSubproof (vernac_subproof) focuses on the first goal, or the goal
    given as argument.
    EndSubproof (vernac_end_subproof) unfocuses from a BeginSubproof, provided
    that the proof of the goal has been completed.
*)
let subproof_kind = Proof.new_focus_kind ()
let subproof_cond = Proof.done_cond subproof_kind

let vernac_subproof gln =
  Proof_global.simple_with_current_proof (fun _ p ->
    match gln with
    | None -> Proof.focus subproof_cond () 1 p
    | Some n -> Proof.focus subproof_cond () n p)

let vernac_end_subproof () =
  Proof_global.simple_with_current_proof (fun _ p ->
    Proof.unfocus subproof_kind p ())

let vernac_bullet (bullet:Proof_global.Bullet.t) =
  Proof_global.simple_with_current_proof (fun _ p ->
    Proof_global.Bullet.put p bullet)

let vernac_show = let open Feedback in function
  | ShowScript -> assert false  (* Only the stm knows the script *)
  | ShowGoal goalref ->
    let info = match goalref with
      | OpenSubgoals -> pr_open_subgoals ()
      | NthGoal n -> pr_nth_open_subgoal n
      | GoalId id -> pr_goal_by_id id
      | GoalUid id -> pr_goal_by_uid id
    in
    msg_notice info
  | ShowGoalImplicitly None ->
      Constrextern.with_implicits msg_notice (pr_open_subgoals ())
  | ShowGoalImplicitly (Some n) ->
      Constrextern.with_implicits msg_notice (pr_nth_open_subgoal n)
  | ShowProof -> show_proof ()
  | ShowNode -> show_node ()
  | ShowExistentials -> show_top_evars ()
  | ShowUniverses -> show_universes ()
  | ShowTree -> show_prooftree ()
  | ShowProofNames ->
      msg_notice (pr_sequence pr_id (Pfedit.get_all_proof_names()))
  | ShowIntros all -> show_intro all
  | ShowMatch id -> show_match id
  | ShowThesis -> show_thesis ()


let vernac_check_guard () =
  let pts = get_pftreestate () in
  let pfterm = List.hd (Proof.partial_proof pts) in
  let message =
    try
      let { Evd.it=gl ; sigma=sigma } = Proof.V82.top_goal pts in
      Inductiveops.control_only_guard (Goal.V82.env sigma gl)
	(EConstr.Unsafe.to_constr pfterm);
      (str "The condition holds up to here")
    with UserError(_,s) ->
      (str ("Condition violated: ") ++s)
  in
  Feedback.msg_notice message

exception End_of_input

(* XXX: This won't properly set the proof mode, as of today, it is
   controlled by the STM. Thus, we would need access information from
   the classifier. The proper fix is to move it to the STM, however,
   the way the proof mode is set there makes the task non trivial
   without a considerable amount of refactoring.
 *)
let vernac_load interp fname =
  let interp x =
    let proof_mode = Proof_global.get_default_proof_mode_name () in
    Proof_global.activate_proof_mode proof_mode;
    interp x in
  let parse_sentence = Flags.with_option Flags.we_are_parsing
    (fun po ->
    match Pcoq.Gram.entry_parse Pcoq.main_entry po with
      | Some x -> x
      | None -> raise End_of_input) in
  let fname =
    Envars.expand_path_macros ~warn:(fun x -> Feedback.msg_warning (str x)) fname in
  let fname = CUnix.make_suffix fname ".v" in
  let input =
    let longfname = Loadpath.locate_file fname in
    let in_chan = open_utf8_file_in longfname in
    Pcoq.Gram.parsable ~file:longfname (Stream.of_channel in_chan) in
  try while true do interp (snd (parse_sentence input)) done
  with End_of_input -> ()

(* "locality" is the prefix "Local" attribute, while the "local" component
 * is the outdated/deprecated "Local" attribute of some vernacular commands
 * still parsed as the obsolete_locality grammar entry for retrocompatibility.
 * loc is the Loc.t of the vernacular command being interpreted. *)
let interp ?proof ?loc locality poly c =
  vernac_pperr_endline (fun () -> str "interpreting: " ++ Ppvernac.pr_vernac c);
  match c with
  (* The below vernac are candidates for removal from the main type
     and to be put into a new doc_command datatype: *)

  | VernacLoad _ -> assert false

  (* Done later in this file *)
  | VernacFail _ -> assert false
  | VernacTime _ -> assert false
  | VernacRedirect _ -> assert false
  | VernacTimeout _ -> assert false
  | VernacStm _ -> assert false

  (* The STM should handle that, but LOAD bypasses the STM... *)
  | VernacAbortAll    -> CErrors.user_err  (str "AbortAll cannot be used through the Load command")
  | VernacRestart     -> CErrors.user_err  (str "Restart cannot be used through the Load command")
  | VernacUndo _      -> CErrors.user_err  (str "Undo cannot be used through the Load command")
  | VernacUndoTo _    -> CErrors.user_err  (str "UndoTo cannot be used through the Load command")
  | VernacBacktrack _ -> CErrors.user_err  (str "Backtrack cannot be used through the Load command")

  (* Toplevel control *)
  | VernacToplevelControl e -> raise e

  (* Resetting *)
  | VernacResetName _  -> anomaly (str "VernacResetName not handled by Stm")
  | VernacResetInitial -> anomaly (str "VernacResetInitial not handled by Stm")
  | VernacBack _       -> anomaly (str "VernacBack not handled by Stm")
  | VernacBackTo _     -> anomaly (str "VernacBackTo not handled by Stm")

  (* This one is possible to handle here *)
  | VernacAbort id    -> CErrors.user_err  (str "Abort cannot be used through the Load command")

  (* Handled elsewhere *)
  | VernacProgram _
  | VernacPolymorphic _
  | VernacLocal _ -> assert false

  (* Syntax *)
  | VernacSyntaxExtension (local,sl) ->
      vernac_syntax_extension locality local sl
  | VernacDelimiters (sc,lr) -> vernac_delimiters sc lr
  | VernacBindScope (sc,rl) -> vernac_bind_scope sc rl
  | VernacOpenCloseScope (local, s) -> vernac_open_close_scope locality local s
  | VernacArgumentsScope (qid,scl) -> vernac_arguments_scope locality qid scl
  | VernacInfix (local,mv,qid,sc) -> vernac_infix locality local mv qid sc
  | VernacNotation (local,c,infpl,sc) ->
      vernac_notation locality local c infpl sc
  | VernacNotationAddFormat(n,k,v) ->
      Metasyntax.add_notation_extra_printing_rule n k v

  (* Gallina *)
  | VernacDefinition (k,lid,d) -> vernac_definition locality poly k lid d
  | VernacStartTheoremProof (k,l,top) -> vernac_start_proof locality poly k l top
  | VernacEndProof e -> vernac_end_proof ?proof e
  | VernacExactProof c -> vernac_exact_proof c
  | VernacAssumption (stre,nl,l) -> vernac_assumption locality poly stre l nl
  | VernacInductive (priv,finite,l) -> vernac_inductive poly priv finite l
  | VernacFixpoint (local, l) -> vernac_fixpoint locality poly local l
  | VernacCoFixpoint (local, l) -> vernac_cofixpoint locality poly local l
  | VernacScheme l -> vernac_scheme l
  | VernacCombinedScheme (id, l) -> vernac_combined_scheme id l
  | VernacUniverse l -> vernac_universe loc poly l
  | VernacConstraint l -> vernac_constraint loc poly l

  (* Modules *)
  | VernacDeclareModule (export,lid,bl,mtyo) ->
      vernac_declare_module export lid bl mtyo
  | VernacDefineModule (export,lid,bl,mtys,mexprl) ->
      vernac_define_module export lid bl mtys mexprl
  | VernacDeclareModuleType (lid,bl,mtys,mtyo) ->
      vernac_declare_module_type lid bl mtys mtyo
  | VernacInclude in_asts ->
      vernac_include in_asts
  (* Gallina extensions *)
  | VernacBeginSection lid -> vernac_begin_section lid

  | VernacEndSegment lid -> vernac_end_segment lid

  | VernacNameSectionHypSet (lid, set) -> vernac_name_sec_hyp lid set

  | VernacRequire (from, export, qidl) -> vernac_require from export qidl
  | VernacImport (export,qidl) -> vernac_import export qidl
  | VernacCanonical qid -> vernac_canonical qid
  | VernacCoercion (local,r,s,t) -> vernac_coercion locality poly local r s t
  | VernacIdentityCoercion (local,(_,id),s,t) ->
      vernac_identity_coercion locality poly local id s t

  (* Type classes *)
  | VernacInstance (abst, sup, inst, props, info) ->
      vernac_instance abst locality poly sup inst props info
  | VernacContext sup -> vernac_context poly sup
  | VernacDeclareInstances insts -> vernac_declare_instances locality insts
  | VernacDeclareClass id -> vernac_declare_class id

  (* Solving *)
  | VernacSolveExistential (n,c) -> vernac_solve_existential n c

  (* Auxiliary file and library management *)
  | VernacAddLoadPath (isrec,s,alias) -> vernac_add_loadpath isrec s alias
  | VernacRemoveLoadPath s -> vernac_remove_loadpath s
  | VernacAddMLPath (isrec,s) -> vernac_add_ml_path isrec s
  | VernacDeclareMLModule l -> vernac_declare_ml_module locality l
  | VernacChdir s -> vernac_chdir s

  (* State management *)
  | VernacWriteState s -> vernac_write_state s
  | VernacRestoreState s -> vernac_restore_state s

  (* Commands *)
  | VernacCreateHintDb (dbname,b) -> vernac_create_hintdb locality dbname b
  | VernacRemoveHints (dbnames,ids) -> vernac_remove_hints locality dbnames ids
  | VernacHints (local,dbnames,hints) ->
      vernac_hints locality poly local dbnames hints
  | VernacSyntacticDefinition (id,c,local,b) ->
      vernac_syntactic_definition locality  id c local b
  | VernacDeclareImplicits (qid,l) ->
      vernac_declare_implicits locality qid l
  | VernacArguments (qid, args, more_implicits, nargs, flags) ->
      vernac_arguments locality qid args more_implicits nargs flags
  | VernacReserve bl -> vernac_reserve bl
  | VernacGeneralizable gen -> vernac_generalizable locality gen
  | VernacSetOpacity qidl -> vernac_set_opacity locality qidl
  | VernacSetStrategy l -> vernac_set_strategy locality l
  | VernacSetOption (key,v) -> vernac_set_option locality key v
  | VernacSetAppendOption (key,v) -> vernac_set_append_option locality key v
  | VernacUnsetOption key -> vernac_unset_option locality key
  | VernacRemoveOption (key,v) -> vernac_remove_option key v
  | VernacAddOption (key,v) -> vernac_add_option key v
  | VernacMemOption (key,v) -> vernac_mem_option key v
  | VernacPrintOption key -> vernac_print_option key
  | VernacCheckMayEval (r,g,c) -> vernac_check_may_eval ?loc r g c
  | VernacDeclareReduction (s,r) -> vernac_declare_reduction locality s r
  | VernacGlobalCheck c -> vernac_global_check c
  | VernacPrint p -> vernac_print ?loc p
  | VernacSearch (s,g,r) -> vernac_search ?loc s g r
  | VernacLocate l -> vernac_locate l
  | VernacRegister (id, r) -> vernac_register id r
  | VernacComments l -> if_verbose Feedback.msg_info (str "Comments ok\n")

  (* Proof management *)
  | VernacGoal t -> vernac_start_proof locality poly Theorem [None,([],t)] false
  | VernacFocus n -> vernac_focus n
  | VernacUnfocus -> vernac_unfocus ()
  | VernacUnfocused -> vernac_unfocused ()
  | VernacBullet b -> vernac_bullet b
  | VernacSubproof n -> vernac_subproof n
  | VernacEndSubproof -> vernac_end_subproof ()
  | VernacShow s -> vernac_show s
  | VernacCheckGuard -> vernac_check_guard ()
  | VernacProof (None, None) ->
      Aux_file.record_in_aux_at ?loc "VernacProof" "tac:no using:no"
  | VernacProof (Some tac, None) ->
      Aux_file.record_in_aux_at ?loc "VernacProof" "tac:yes using:no";
      vernac_set_end_tac tac
  | VernacProof (None, Some l) ->
      Aux_file.record_in_aux_at ?loc "VernacProof" "tac:no using:yes";
      vernac_set_used_variables l
  | VernacProof (Some tac, Some l) -> 
      Aux_file.record_in_aux_at ?loc "VernacProof" "tac:yes using:yes";
      vernac_set_end_tac tac; vernac_set_used_variables l
  | VernacProofMode mn -> Proof_global.set_proof_mode mn

  (* Extensions *)
  | VernacExtend (opn,args) -> Vernacinterp.call ?locality (opn,args)

(* Vernaculars that take a locality flag *)
let check_vernac_supports_locality c l =
  match l, c with
  | None, _ -> ()
  | Some _, (
      VernacOpenCloseScope _
    | VernacSyntaxExtension _ | VernacInfix _ | VernacNotation _
    | VernacDefinition _ | VernacFixpoint _ | VernacCoFixpoint _
    | VernacAssumption _ | VernacStartTheoremProof _
    | VernacCoercion _ | VernacIdentityCoercion _
    | VernacInstance _ | VernacDeclareInstances _
    | VernacDeclareMLModule _
    | VernacCreateHintDb _ | VernacRemoveHints _ | VernacHints _
    | VernacSyntacticDefinition _
    | VernacArgumentsScope _ | VernacDeclareImplicits _ | VernacArguments _
    | VernacGeneralizable _
    | VernacSetOpacity _ | VernacSetStrategy _
    | VernacSetOption _ | VernacSetAppendOption _ | VernacUnsetOption _
    | VernacDeclareReduction _
    | VernacExtend _ 
    | VernacInductive _) -> ()
  | Some _, _ -> CErrors.error "This command does not support Locality"

(* Vernaculars that take a polymorphism flag *)
let check_vernac_supports_polymorphism c p =
  match p, c with
  | None, _ -> ()
  | Some _, (
      VernacDefinition _ | VernacFixpoint _ | VernacCoFixpoint _
    | VernacAssumption _ | VernacInductive _ 
    | VernacStartTheoremProof _
    | VernacCoercion _ | VernacIdentityCoercion _
    | VernacInstance _ | VernacDeclareInstances _
    | VernacHints _ | VernacContext _
    | VernacExtend _ | VernacUniverse _ | VernacConstraint _) -> ()
  | Some _, _ -> CErrors.error "This command does not support Polymorphism"

let enforce_polymorphism = function
  | None -> Flags.is_universe_polymorphism ()
  | Some b -> Flags.make_polymorphic_flag b; b

(** A global default timeout, controlled by option "Set Default Timeout n".
    Use "Unset Default Timeout" to deactivate it (or set it to 0). *)

let default_timeout = ref None

let _ =
  Goptions.declare_int_option
    { Goptions.optsync  = true;
      Goptions.optdepr  = false;
      Goptions.optname  = "the default timeout";
      Goptions.optkey   = ["Default";"Timeout"];
      Goptions.optread  = (fun () -> !default_timeout);
      Goptions.optwrite = ((:=) default_timeout) }

(** When interpreting a command, the current timeout is initially
    the default one, but may be modified locally by a Timeout command. *)

let current_timeout = ref None

let vernac_timeout f =
  match !current_timeout, !default_timeout with
    | Some n, _ | None, Some n ->
      let f () = f (); current_timeout := None in
      Control.timeout n f Timeout
    | None, None -> f ()

let restore_timeout () = current_timeout := None

let locate_if_not_already ?loc (e, info) =
  match Loc.get_loc info with
  | None   -> (e, Option.cata (Loc.add_loc info) info loc)
  | Some l -> (e, info)

exception HasNotFailed
exception HasFailed of std_ppcmds

let with_fail b f =
  if not b then f ()
  else begin try
      (* If the command actually works, ignore its effects on the state.
       * Note that error has to be printed in the right state, hence
       * within the purified function *)
      Future.purify
        (fun v ->
           try f v; raise HasNotFailed
           with
           | HasNotFailed as e -> raise e
           | e ->
              let e = CErrors.push e in
              raise (HasFailed (CErrors.iprint
                (ExplainErr.process_vernac_interp_error ~allow_uncaught:false e))))
        ()
    with e when CErrors.noncritical e ->
      let (e, _) = CErrors.push e in
      match e with
      | HasNotFailed ->
          user_err ~hdr:"Fail" (str "The command has not failed!")
      | HasFailed msg ->
          if not !Flags.quiet || !test_mode || !ide_slave then Feedback.msg_info
            (str "The command has indeed failed with message:" ++ fnl () ++ msg)
      | _ -> assert false
  end

let interp ?(verbosely=true) ?proof (loc,c) =
  let orig_program_mode = Flags.is_program_mode () in
  let rec aux ?locality ?polymorphism isprogcmd = function

    (* This assert case will be removed when fake_ide can understand
       completion feedback *)
    | VernacStm _ -> assert false (* Done by Stm *)

    | VernacProgram c when not isprogcmd -> aux ?locality ?polymorphism true c
    | VernacProgram _ -> CErrors.error "Program mode specified twice"
    | VernacLocal (b, c) when Option.is_empty locality -> 
      aux ~locality:b ?polymorphism isprogcmd c
    | VernacPolymorphic (b, c) when polymorphism = None -> 
      aux ?locality ~polymorphism:b isprogcmd c
    | VernacPolymorphic (b, c) -> CErrors.error "Polymorphism specified twice"
    | VernacLocal _ -> CErrors.error "Locality specified twice"
    | VernacFail v ->
        with_fail true (fun () -> aux ?locality ?polymorphism isprogcmd v)
    | VernacTimeout (n,v) ->
        current_timeout := Some n;
        aux ?locality ?polymorphism isprogcmd v
    | VernacRedirect (s, (_,v)) ->
         Topfmt.with_output_to_file s (aux ?locality ?polymorphism isprogcmd) v
    | VernacTime (_,v) ->
        System.with_time !Flags.time
          (aux ?locality ?polymorphism isprogcmd) v;
    | VernacLoad (_,fname) -> vernac_load (aux false) fname
    | c -> 
        check_vernac_supports_locality c locality;
        check_vernac_supports_polymorphism c polymorphism;
	let poly = enforce_polymorphism polymorphism in
        Obligations.set_program_mode isprogcmd;
        try
          vernac_timeout begin fun () ->
          if verbosely
            then Flags.verbosely (interp ?proof ?loc locality poly) c
            else Flags.silently  (interp ?proof ?loc locality poly) c;
          if orig_program_mode || not !Flags.program_mode || isprogcmd then
            Flags.program_mode := orig_program_mode;
	  ignore (Flags.use_polymorphic_flag ())
          end
        with
        | reraise when
              (match reraise with
              | Timeout -> true
              | e -> CErrors.noncritical e)
          ->
            let e = CErrors.push reraise in
            let e = locate_if_not_already ?loc e in
            let () = restore_timeout () in
            Flags.program_mode := orig_program_mode;
	    ignore (Flags.use_polymorphic_flag ());
            iraise e
  in
    if verbosely then Flags.verbosely (aux false) c
    else aux false c
