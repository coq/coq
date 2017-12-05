(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Concrete syntax of the mathematical vernacular MV V2.6 *)

open Pp
open CErrors
open Util
open Names
open Nameops
open Term
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
open Vernacinterp

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
  let sigma, env = Pfedit.get_current_context () in
  let pprf = Proof.partial_proof p in
  Feedback.msg_notice (Pp.prlist_with_sep Pp.fnl (Printer.pr_econstr_env env sigma) pprf)

let show_top_evars () =
  (* spiwack: new as of Feb. 2010: shows goal evars in addition to non-goal evars. *)
  let pfts = Proof_global.give_me_the_proof () in
  let gls,_,_,_,sigma = Proof.proof pfts in
  Feedback.msg_notice (pr_evars_int sigma 1 (Evd.undefined_map sigma))

let show_universes () =
  let pfts = Proof_global.give_me_the_proof () in
  let gls,_,_,_,sigma = Proof.proof pfts in
  let ctx = Evd.universe_context_set (Evd.nf_constraints sigma) in
    Feedback.msg_notice (Termops.pr_evar_universe_context (Evd.evar_universe_context sigma));
    Feedback.msg_notice (str"Normalized constraints: " ++ Univ.pr_universe_context_set (Termops.pr_evd_level sigma) ctx)

(* Simulate the Intro(s) tactic *)
let show_intro all =
  let open EConstr in
  let pf = Proof_global.give_me_the_proof() in
  let gls,_,_,_,sigma = Proof.proof pf in
  if not (List.is_empty gls) then begin
    let gl = {Evd.it=List.hd gls ; sigma = sigma; } in
    let l,_= decompose_prod_assum sigma (Termops.strip_outer_cast sigma (pf_concl gl)) in
    if all then
      let lid = Tactics.find_intro_names l gl in
      Feedback.msg_notice (hov 0 (prlist_with_sep  spc Id.print lid))
    else if not (List.is_empty l) then
      let n = List.last l in
      Feedback.msg_notice (Id.print (List.hd (Tactics.find_intro_names [n] gl)))
  end

(** Prepare a "match" template for a given inductive type.
    For each branch of the match, we list the constructor name
    followed by enough pattern variables.
    [Not_found] is raised if the given string isn't the qualid of
    a known inductive type. *)

(*

  HH notes in PR #679:

  The Show Match could also be made more robust, for instance in the
  presence of let in the branch of a constructor. A
  decompose_prod_assum would probably suffice for that, but then, it
  is a Context.Rel.Declaration.t which needs to be matched and not
  just a pair (name,type).

  Otherwise, this is OK. After all, the API on inductive types is not
  so canonical in general, and in this simple case, working at the
  low-level of mind_nf_lc seems reasonable (compared to working at the
  higher-level of Inductiveops).

*)
    
let make_cases_aux glob_ref =
  match glob_ref with
    | Globnames.IndRef ind ->
	let {Declarations.mind_nparams = np} , {Declarations.mind_nf_lc = tarr} = Global.lookup_inductive ind in
	Util.Array.fold_right_i
	  (fun i typ l ->
	     let al = List.rev (fst (decompose_prod typ)) in
	     let al = Util.List.skipn np al in
	     let rec rename avoid = function
	       | [] -> []
	       | (n,_)::l ->
		   let n' = Namegen.next_name_away_with_default (Id.to_string Namegen.default_dependent_ident) n avoid in
		   Id.to_string n' :: rename (Id.Set.add n' avoid) l in
	     let al' = rename Id.Set.empty al in
	     let consref = ConstructRef (ith_constructor_of_inductive ind (i + 1)) in
	     (Libnames.string_of_qualid (Nametab.shortest_qualid_of_global Id.Set.empty consref) :: al') :: l)
	  tarr []
    | _ -> raise Not_found

let make_cases s =
  let qualified_name = Libnames.qualid_of_string s in
  let glob_ref = Nametab.locate qualified_name in
  make_cases_aux glob_ref

(** Textual display of a generic "match" template *)

let show_match id =
  let patterns =
    try make_cases_aux (Nametab.global id)
    with Not_found -> user_err Pp.(str "Unknown inductive type.")
  in
  let pr_branch l =
    str "| " ++ hov 1 (prlist_with_sep spc str l) ++ str " =>"
  in
  Feedback.msg_notice (v 1 (str "match # with" ++ fnl () ++
	    prlist_with_sep fnl pr_branch patterns ++ fnl () ++ str "end" ++ fnl ()))

(* "Print" commands *)

let print_path_entry p =
  let dir = DirPath.print (Loadpath.logical p) in
  let path = str (CUnix.escaped_string_of_physical_path (Loadpath.physical p)) in
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
  pr_vertical_list DirPath.print loaded_opened ++ fnl () ++
  str"Loaded and not imported library files: " ++
  pr_vertical_list DirPath.print only_loaded


let print_module r =
  let (loc,qid) = qualid_of_reference r in
  try
    let globdir = Nametab.locate_dir qid in
      match globdir with
          DirModule { obj_dir; obj_mp; _ } ->
            Feedback.msg_notice (Printmod.print_module (Printmod.printable_body obj_dir) obj_mp)
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
    let (mp,_,lbl) = Names.KerName.repr kn in
    let qn = (qualified_minus (List.length ns) mp)@[Names.Label.to_id lbl] in
    print_list Id.print qn
  in
  let print_constant k body =
    (* FIXME: universes *)
    let t = body.Declarations.const_type in
    let sigma, env = Pfedit.get_current_context () in
    print_kn k ++ str":" ++ spc() ++ Printer.pr_type_env env sigma t
  in
  let matches mp = match match_modulepath ns mp with
  | Some [] -> true
  | _ -> false in
  let constants = (Environ.pre_env (Global.env ())).Pre_env.env_globals.Pre_env.env_constants in
  let constants_in_namespace =
    Cmap_env.fold (fun c (body,_) acc ->
      let kn = Constant.user c in
      if matches (KerName.modpath kn) then
        acc++fnl()++hov 2 (print_constant kn body)
      else
        acc
    ) constants (str"")
  in
  Feedback.msg_notice ((print_list Id.print ns)++str":"++fnl()++constants_in_namespace)

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
    | IndRef _ | ConstructRef _ -> user_err Pp.(str "The reference is not unfoldable")
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
       (DirPath.print fulldir ++ strbrk " has been loaded from file " ++
	 str file))
  | Library.LibInPath, fulldir, file ->
      Feedback.msg_info (hov 0
       (DirPath.print fulldir ++ strbrk " is bound to file " ++ str file))

let err_unmapped_library ?loc ?from qid =
  let dir = fst (repr_qualid qid) in
  let prefix = match from with
  | None -> str "."
  | Some from ->
    str " and prefix " ++ DirPath.print from ++ str "."
  in
  user_err ?loc
    ~hdr:"locate_library"
    (strbrk "Cannot find a physical path bound to logical path matching suffix " ++
       DirPath.print dir ++ prefix)

let err_notfound_library ?loc ?from qid =
  let prefix = match from with
  | None -> str "."
  | Some from ->
    str " with prefix " ++ DirPath.print from ++ str "."
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

let vernac_syntax_extension atts infix l =
  let local = enforce_module_locality atts.locality in
  if infix then Metasyntax.check_infix_modifiers (snd l);
  Metasyntax.add_syntax_extension local l

let vernac_delimiters sc = function
  | Some lr -> Metasyntax.add_delimiters sc lr
  | None -> Metasyntax.remove_delimiters sc

let vernac_bind_scope sc cll =
  Metasyntax.add_class_scope sc (List.map scope_class_of_qualid cll)

let vernac_open_close_scope ~atts (b,s) =
  let local = enforce_section_locality atts.locality in
  Notation.open_close_scope (local,b,s)

let vernac_arguments_scope ~atts r scl =
  let local = make_section_locality atts.locality in
  Notation.declare_arguments_scope local (smart_global r) scl

let vernac_infix ~atts =
  let local = enforce_module_locality atts.locality in
  Metasyntax.add_infix local (Global.env())

let vernac_notation ~atts =
  let local = enforce_module_locality atts.locality in
  Metasyntax.add_notation local (Global.env())

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
          user_err Pp.(str "The statement obligations could not be resolved \
                 automatically, write a statement definition first.")
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

let vernac_definition ~atts discharge kind ((loc,id as lid),pl) def =
  let local = enforce_locality_exp atts.locality discharge in
  let hook = vernac_definition_hook atts.polymorphic kind in
  let () = match local with
  | Discharge -> Dumpglob.dump_definition lid true "var"
  | Local | Global -> Dumpglob.dump_definition lid false "def"
  in
  (match def with
    | ProveBody (bl,t) ->   (* local binders, typ *)
          start_proof_and_print (local, atts.polymorphic, DefinitionBody kind)
	    [Some (lid,pl), (bl,t)] hook
    | DefineBody (bl,red_option,c,typ_opt) ->
      let red_option = match red_option with
          | None -> None
          | Some r ->
            let sigma, env = Pfedit.get_current_context () in
            Some (snd (Hook.get f_interp_redexp env sigma r)) in
        do_definition id (local, atts.polymorphic, kind) pl bl red_option c typ_opt hook)

let vernac_start_proof ~atts kind l =
  let local = enforce_locality_exp atts.locality NoDischarge in
  if Dumpglob.dump () then
    List.iter (fun (id, _) ->
      match id with
	| Some (lid,_) -> Dumpglob.dump_definition lid false "prf"
	| None -> ()) l;
  start_proof_and_print (local, atts.polymorphic, Proof kind) l no_hook

let vernac_end_proof ?proof = function
  | Admitted          -> save_proof ?proof Admitted
  | Proved (_,_) as e -> save_proof ?proof e

let vernac_exact_proof c =
  (* spiwack: for simplicity I do not enforce that "Proof proof_term" is
     called only at the begining of a proof. *)
  let status = Pfedit.by (Tactics.exact_proof c) in
  save_proof (Vernacexpr.(Proved(Opaque,None)));
  if not status then Feedback.feedback Feedback.AddedAxiom

let vernac_assumption ~atts discharge kind l nl =
  let local = enforce_locality_exp atts.locality discharge in
  let global = local == Global in
  let kind = local, atts.polymorphic, kind in
  List.iter (fun (is_coe,(idl,c)) ->
    if Dumpglob.dump () then
      List.iter (fun (lid, _) ->
	if global then Dumpglob.dump_definition lid false "ax"
	else Dumpglob.dump_definition lid true "var") idl) l;
  let status = do_assumptions kind nl l in
  if not status then Feedback.feedback Feedback.AddedAxiom

let should_treat_as_cumulative cum poly =
  if poly then
    match cum with
    | GlobalCumulativity | LocalCumulativity -> true
    | GlobalNonCumulativity | LocalNonCumulativity -> false
  else
    match cum with
    | GlobalCumulativity | GlobalNonCumulativity -> false
    | LocalCumulativity -> 
      user_err Pp.(str "The Cumulative prefix can only be used in a polymorphic context.")
    | LocalNonCumulativity ->
      user_err Pp.(str "The NonCumulative prefix can only be used in a polymorphic context.")

let vernac_record cum k poly finite struc binders sort nameopt cfs =
  let is_cumulative = should_treat_as_cumulative cum poly in
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
    ignore(Record.definition_structure (k,is_cumulative,poly,finite,struc,binders,cfs,const,sort))

(** When [poly] is true the type is declared polymorphic. When [lo] is true,
    then the type is declared private (as per the [Private] keyword). [finite]
    indicates whether the type is inductive, co-inductive or
    neither. *)
let vernac_inductive ~atts cum lo finite indl =
  let is_cumulative = should_treat_as_cumulative cum atts.polymorphic in
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
      user_err Pp.(str "The Record keyword is for types defined using the syntax { ... }.")
  | [ (_ , _ , _ ,Variant, RecordDecl _),_ ] ->
      user_err Pp.(str "The Variant keyword does not support syntax { ... }.")
  | [ ( id , bl , c , b, RecordDecl (oc,fs) ), [] ] ->
      vernac_record cum (match b with Class _ -> Class false | _ -> b)
       atts.polymorphic finite id bl c oc fs
  | [ ( id , bl , c , Class _, Constructors [l]), [] ] ->
      let f =
	let (coe, ((loc, id), ce)) = l in
	let coe' = if coe then Some true else None in
  	  (((coe', AssumExpr ((loc, Name id), ce)), None), [])
      in vernac_record cum (Class true) atts.polymorphic finite id bl c None [f]
  | [ ( _ , _, _, Class _, Constructors _), [] ] ->
      user_err Pp.(str "Inductive classes not supported")
  | [ ( id , bl , c , Class _, _), _ :: _ ] ->
      user_err Pp.(str "where clause not supported for classes")
  | [ ( _ , _ , _ , _, RecordDecl _ ) , _ ] ->
      user_err Pp.(str "where clause not supported for (co)inductive records")
  | _ -> let unpack = function
      | ( (false, id) , bl , c , _ , Constructors l ) , ntn  -> ( id , bl , c , l ) , ntn
      | ( (true,_),_,_,_,Constructors _),_ ->
          user_err Pp.(str "Variant types do not handle the \"> Name\" syntax, which is reserved for records. Use the \":>\" syntax on constructors instead.")
      | _ -> user_err Pp.(str "Cannot handle mutually (co)inductive records.")
    in
    let indl = List.map unpack indl in
    do_mutual_inductive indl is_cumulative atts.polymorphic lo finite

let vernac_fixpoint ~atts discharge l =
  let local = enforce_locality_exp atts.locality discharge in
  if Dumpglob.dump () then
    List.iter (fun (((lid,_), _, _, _, _), _) -> Dumpglob.dump_definition lid false "def") l;
  do_fixpoint local atts.polymorphic l

let vernac_cofixpoint ~atts discharge l =
  let local = enforce_locality_exp atts.locality discharge in
  if Dumpglob.dump () then
    List.iter (fun (((lid,_), _, _, _), _) -> Dumpglob.dump_definition lid false "def") l;
  do_cofixpoint local atts.polymorphic l

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

let vernac_universe ~atts l =
  if atts.polymorphic && not (Lib.sections_are_opened ()) then
    user_err ?loc:atts.loc ~hdr:"vernac_universe"
		 (str"Polymorphic universes can only be declared inside sections, " ++
		  str "use Monomorphic Universe instead");
  do_universe atts.polymorphic l

let vernac_constraint ~atts l =
  if atts.polymorphic && not (Lib.sections_are_opened ()) then
    user_err ?loc:atts.loc ~hdr:"vernac_constraint"
		 (str"Polymorphic universe constraints can only be declared"
		  ++ str " inside sections, use Monomorphic Constraint instead");
  do_constraint atts.polymorphic l

(**********************)
(* Modules            *)

let vernac_import export refl =
  Library.import_module export (List.map qualid_of_reference refl)

let vernac_declare_module export (loc, id) binders_ast mty_ast =
  (* We check the state of the system (in section, in module type)
     and what module information is supplied *)
  if Lib.sections_are_opened () then
    user_err Pp.(str "Modules and Module Types are not allowed inside sections.");
  let binders_ast = List.map
   (fun (export,idl,ty) ->
     if not (Option.is_empty export) then
      user_err Pp.(str "Arguments of a functor declaration cannot be exported. Remove the \"Export\" and \"Import\" keywords from every functor argument.")
     else (idl,ty)) binders_ast in
  let mp =
    Declaremods.declare_module Modintern.interp_module_ast
      id binders_ast (Enforce mty_ast) []
  in
  Dumpglob.dump_moddef ?loc mp "mod";
  Flags.if_verbose Feedback.msg_info (str "Module " ++ Id.print id ++ str " is declared");
  Option.iter (fun export -> vernac_import export [Ident (Loc.tag id)]) export

let vernac_define_module export (loc, id) binders_ast mty_ast_o mexpr_ast_l =
  (* We check the state of the system (in section, in module type)
     and what module information is supplied *)
  if Lib.sections_are_opened () then
    user_err Pp.(str "Modules and Module Types are not allowed inside sections.");
  match mexpr_ast_l with
    | [] ->
       Proof_global.check_no_pending_proof ();
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
       Flags.if_verbose Feedback.msg_info
         (str "Interactive Module " ++ Id.print id ++ str " started");
       List.iter
         (fun (export,id) ->
           Option.iter
             (fun export -> vernac_import export [Ident (Loc.tag id)]) export
         ) argsexport
    | _::_ ->
       let binders_ast = List.map
        (fun (export,idl,ty) ->
          if not (Option.is_empty export) then
           user_err Pp.(str "Arguments of a functor definition can be imported only if the definition is interactive. Remove the \"Export\" and \"Import\" keywords from every functor argument.")
          else (idl,ty)) binders_ast in
       let mp =
         Declaremods.declare_module Modintern.interp_module_ast
	   id binders_ast mty_ast_o mexpr_ast_l
       in
       Dumpglob.dump_moddef ?loc mp "mod";
       Flags.if_verbose Feedback.msg_info
	 (str "Module " ++ Id.print id ++ str " is defined");
       Option.iter (fun export -> vernac_import export [Ident (Loc.tag id)])
         export

let vernac_end_module export (loc,id as lid) =
  let mp = Declaremods.end_module () in
  Dumpglob.dump_modref ?loc mp "mod";
  Flags.if_verbose Feedback.msg_info (str "Module " ++ Id.print id ++ str " is defined");
  Option.iter (fun export -> vernac_import export [Ident lid]) export

let vernac_declare_module_type (loc,id) binders_ast mty_sign mty_ast_l =
  if Lib.sections_are_opened () then
    user_err Pp.(str "Modules and Module Types are not allowed inside sections.");

  match mty_ast_l with
    | [] ->
       Proof_global.check_no_pending_proof ();
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
       Flags.if_verbose Feedback.msg_info
	 (str "Interactive Module Type " ++ Id.print id ++ str " started");
       List.iter
         (fun (export,id) ->
           Option.iter
             (fun export -> vernac_import export [Ident (Loc.tag id)]) export
         ) argsexport

    | _ :: _ ->
	let binders_ast = List.map
          (fun (export,idl,ty) ->
            if not (Option.is_empty export) then
              user_err Pp.(str "Arguments of a functor definition can be imported only if the definition is interactive. Remove the \"Export\" and \"Import\" keywords from every functor argument.")
            else (idl,ty)) binders_ast in
	let mp =
          Declaremods.declare_modtype Modintern.interp_module_ast
	    id binders_ast mty_sign mty_ast_l
        in
        Dumpglob.dump_moddef ?loc mp "modtype";
	Flags.if_verbose Feedback.msg_info
	  (str "Module Type " ++ Id.print id ++ str " is defined")

let vernac_end_modtype (loc,id) =
  let mp = Declaremods.end_modtype () in
  Dumpglob.dump_modref ?loc mp "modtype";
  Flags.if_verbose Feedback.msg_info (str "Module Type " ++ Id.print id ++ str " is defined")

let vernac_include l =
  Declaremods.declare_include Modintern.interp_module_ast l

(**********************)
(* Gallina extensions *)

(* Sections *)

let vernac_begin_section (_, id as lid) =
  Proof_global.check_no_pending_proof ();
  Dumpglob.dump_definition lid true "sec";
  Lib.open_section id

let vernac_end_section (loc,_) =
  Dumpglob.dump_reference ?loc
    (DirPath.to_string (Lib.current_dirpath true)) "<>" "sec";
  Lib.close_section ()

let vernac_name_sec_hyp (_,id) set = Proof_using.name_set id set

(* Dispatcher of the "End" command *)

let vernac_end_segment (_,id as lid) =
  Proof_global.check_no_pending_proof ();
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

let vernac_coercion ~atts ref qids qidt =
  let local = enforce_locality atts.locality in
  let target = cl_of_qualid qidt in
  let source = cl_of_qualid qids in
  let ref' = smart_global ref in
  Class.try_add_new_coercion_with_target ref' ~local atts.polymorphic ~source ~target;
  Flags.if_verbose Feedback.msg_info (pr_global ref' ++ str " is now a coercion")

let vernac_identity_coercion ~atts id qids qidt =
  let local = enforce_locality atts.locality in
  let target = cl_of_qualid qidt in
  let source = cl_of_qualid qids in
  Class.try_add_new_identity_coercion id ~local atts.polymorphic ~source ~target

(* Type classes *)

let vernac_instance ~atts abst sup inst props pri =
  let global = not (make_section_locality atts.locality) in
  Dumpglob.dump_constraint inst false "inst";
  ignore(Classes.new_instance ~abstract:abst ~global atts.polymorphic sup inst props pri)

let vernac_context ~atts l =
  if not (Classes.context atts.polymorphic l) then Feedback.feedback Feedback.AddedAxiom

let vernac_declare_instances ~atts insts =
  let glob = not (make_section_locality atts.locality) in
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

let vernac_solve_existential = Pfedit.instantiate_nth_evar_com

let vernac_set_end_tac tac =
  let env = Genintern.empty_glob_sign (Global.env ()) in
  let _, tac = Genintern.generic_intern env tac in
  if not (Proof_global.there_are_pending_proofs ()) then
    user_err Pp.(str "Unknown command of the non proof-editing mode.");
  Proof_global.set_endline_tactic tac
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
        (str "Unknown variable: " ++ Id.print id))
    l;
  let _, to_clear = Proof_global.set_used_variables l in
  let to_clear = List.map snd to_clear in
  Proof_global.with_current_proof begin fun _ p ->
    if List.is_empty to_clear then (p, ())
    else
      let tac = Tactics.clear to_clear in
      fst (Pfedit.solve SelectAll None tac p), ()
  end

(*****************************)
(* Auxiliary file management *)

let expand filename =
  Envars.expand_path_macros ~warn:(fun x -> Feedback.msg_warning (str x)) filename

let vernac_add_loadpath implicit pdir ldiropt =
  let pdir = expand pdir in
  let alias = Option.default Libnames.default_root_prefix ldiropt in
  Mltop.add_rec_path Mltop.AddTopML ~unix_path:pdir ~coq_root:alias ~implicit

let vernac_remove_loadpath path =
  Loadpath.remove_load_path (expand path)

  (* Coq syntax for ML or system commands *)

let vernac_add_ml_path isrec path =
  (if isrec then Mltop.add_rec_ml_dir else Mltop.add_ml_dir) (expand path)

let vernac_declare_ml_module ~atts l =
  let local = make_locality atts.locality in
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
	  user_err Pp.(str ("Cd failed: " ^ err))
      end;
      Flags.if_verbose Feedback.msg_info (str (Sys.getcwd()))


(********************)
(* State management *)

let vernac_write_state file =
  Proof_global.discard_all ();
  let file = CUnix.make_suffix file ".coq" in
  States.extern_state file

let vernac_restore_state file =
  Proof_global.discard_all ();
  let file = Loadpath.locate_file (CUnix.make_suffix file ".coq") in
  States.intern_state file

(************)
(* Commands *)

let vernac_create_hintdb ~atts id b =
  let local = make_module_locality atts.locality in
  Hints.create_hint_db local id full_transparent_state b

let vernac_remove_hints ~atts dbs ids =
  let local = make_module_locality atts.locality in
  Hints.remove_hints local dbs (List.map Smartlocate.global_with_alias ids)

let vernac_hints ~atts lb h =
  let local = enforce_module_locality atts.locality in
  Hints.add_hints local lb (Hints.interp_hints atts.polymorphic h)

let vernac_syntactic_definition ~atts lid x y =
  Dumpglob.dump_definition lid false "syndef";
  let local = enforce_module_locality atts.locality in
  Metasyntax.add_syntactic_definition (Global.env()) (snd lid) x local y

let vernac_declare_implicits ~atts r l =
  let local = make_section_locality atts.locality in
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
let vernac_arguments ~atts reference args more_implicits nargs_for_red flags =
  let assert_flag = List.mem `Assert flags in
  let rename_flag = List.mem `Rename flags in
  let clear_scopes_flag = List.mem `ClearScopes flags in
  let extra_scopes_flag = List.mem `ExtraScopes flags in
  let clear_implicits_flag = List.mem `ClearImplicits flags in
  let default_implicits_flag = List.mem `DefaultImplicits flags in
  let never_unfold_flag = List.mem `ReductionNeverUnfold flags in

  let err_incompat x y =
    user_err Pp.(str ("Options \""^x^"\" and \""^y^"\" are incompatible.")) in

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
    let ty, _ = Global.type_of_global_in_context (Global.env ()) sr in
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
                    prlist_with_sep pr_comma Name.print names ++ str ".")
  in
  let err_missing_args names =
    user_err ~hdr:"vernac_declare_arguments"
                 (strbrk "The following arguments are not declared: " ++
                    prlist_with_sep pr_comma Name.print names ++ str ".")
  in

  let rec check_extra_args extra_args =
    match extra_args with
    | [] -> ()
    | { notation_scope = None } :: _ -> err_extra_args (names_of extra_args)
    | { name = Anonymous; notation_scope = Some _ } :: args ->
       check_extra_args args
    | _ ->
       user_err Pp.(str "Extra notation scopes can be set on anonymous and explicit arguments only.")
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
    user_err Pp.(str "The \"/\" modifier should be put before any extra scope.");

  let scopes_specified = List.exists Option.has_some scopes in
  
  if scopes_specified && clear_scopes_flag then
    user_err Pp.(str "The \"clear scopes\" flag is incompatible with scope annotations.");

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
       else user_err Pp.(str "Argument lists should agree on the names they provide.")
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
          str "Argument " ++ Name.print o ++
            str " renamed to " ++ Name.print n ++ str ".");

  let duplicate_names =
    List.duplicates Name.equal (List.filter ((!=) Anonymous) names)
  in
  if not (List.is_empty duplicate_names) then begin
    let duplicates = prlist_with_sep pr_comma Name.print duplicate_names in
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
                    (strbrk"Argument "++ Name.print name ++ 
                       strbrk " cannot be declared implicit.")

    | Name id :: inf_names, (name, impl) :: implicits ->
       let max = impl = MaximallyImplicit in
       (ExplByName id,max,false) :: build_implicits inf_names implicits
    
    | _ -> assert false (* already checked in [names_union] *)
  in
  
  let implicits = List.map (build_implicits inf_names) implicits in
  let implicits_specified = match implicits with [[]] -> false | _ -> true in

  if implicits_specified && clear_implicits_flag then
    user_err Pp.(str "The \"clear implicits\" flag is incompatible with implicit annotations");

  if implicits_specified && default_implicits_flag then
    user_err Pp.(str "The \"default implicits\" flag is incompatible with implicit annotations");

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
    let local = make_section_locality atts.locality in
    Arguments_renaming.rename_arguments local sr names
  end;

  if scopes_specified || clear_scopes_flag then begin
      let scopes = List.map (Option.map (fun (loc,k) -> 
        try ignore (Notation.find_scope k); k
        with UserError _ ->
          Notation.find_delimiters_scope ?loc k)) scopes
      in
      vernac_arguments_scope ~atts reference scopes
    end;

  if implicits_specified || clear_implicits_flag then
    vernac_declare_implicits ~atts reference implicits;

  if default_implicits_flag then
    vernac_declare_implicits ~atts reference [];

  if red_modifiers_specified then begin
    match sr with
    | ConstRef _ as c ->
       Reductionops.ReductionBehaviour.set
         (make_section_locality atts.locality) c
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
    let t = Detyping.detype Detyping.Now false Id.Set.empty env (Evd.from_ctx ctx) (EConstr.of_constr t) in
    let t,_ = Notation_ops.notation_constr_of_glob_constr (default_env ()) t in
    Reserve.declare_reserved_type idl t)
  in List.iter sb_decl bl

let vernac_generalizable ~atts =
  let local = make_non_locality atts.locality in
  Implicit_quantifiers.declare_generalizable local

let _ =
  declare_bool_option
    { optdepr  = false;
      optname  = "silent";
      optkey   = ["Silent"];
      optread  = (fun () -> !Flags.quiet);
      optwrite = ((:=) Flags.quiet) }

let _ =
  declare_bool_option
    { optdepr  = false;
      optname  = "implicit arguments";
      optkey   = ["Implicit";"Arguments"];
      optread  = Impargs.is_implicit_args;
      optwrite = Impargs.make_implicit_args }

let _ =
  declare_bool_option
    { optdepr  = false;
      optname  = "strict implicit arguments";
      optkey   = ["Strict";"Implicit"];
      optread  = Impargs.is_strict_implicit_args;
      optwrite = Impargs.make_strict_implicit_args }

let _ =
  declare_bool_option
    { optdepr  = false;
      optname  = "strong strict implicit arguments";
      optkey   = ["Strongly";"Strict";"Implicit"];
      optread  = Impargs.is_strongly_strict_implicit_args;
      optwrite = Impargs.make_strongly_strict_implicit_args }

let _ =
  declare_bool_option
    { optdepr  = false;
      optname  = "contextual implicit arguments";
      optkey   = ["Contextual";"Implicit"];
      optread  = Impargs.is_contextual_implicit_args;
      optwrite = Impargs.make_contextual_implicit_args }

let _ =
  declare_bool_option
    { optdepr  = false;
      optname  = "implicit status of reversible patterns";
      optkey   = ["Reversible";"Pattern";"Implicit"];
      optread  = Impargs.is_reversible_pattern_implicit_args;
      optwrite = Impargs.make_reversible_pattern_implicit_args }

let _ =
  declare_bool_option
    { optdepr  = false;
      optname  = "maximal insertion of implicit";
      optkey   = ["Maximal";"Implicit";"Insertion"];
      optread  = Impargs.is_maximal_implicit_args;
      optwrite = Impargs.make_maximal_implicit_args }

let _ =
  declare_bool_option
    { optdepr  = true; (* remove in 8.8 *)
      optname  = "automatic introduction of variables";
      optkey   = ["Automatic";"Introduction"];
      optread  = Flags.is_auto_intros;
      optwrite = Flags.make_auto_intros }

let _ =
  declare_bool_option
    { optdepr  = false;
      optname  = "coercion printing";
      optkey   = ["Printing";"Coercions"];
      optread  = (fun () -> !Constrextern.print_coercions);
      optwrite = (fun b ->  Constrextern.print_coercions := b) }

let _ =
  declare_bool_option
    { optdepr  = false;
      optname  = "printing of existential variable instances";
      optkey   = ["Printing";"Existential";"Instances"];
      optread  = (fun () -> !Detyping.print_evar_arguments);
      optwrite = (:=) Detyping.print_evar_arguments }

let _ =
  declare_bool_option
    { optdepr  = false;
      optname  = "implicit arguments printing";
      optkey   = ["Printing";"Implicit"];
      optread  = (fun () -> !Constrextern.print_implicits);
      optwrite = (fun b ->  Constrextern.print_implicits := b) }

let _ =
  declare_bool_option
    { optdepr  = false;
      optname  = "implicit arguments defensive printing";
      optkey   = ["Printing";"Implicit";"Defensive"];
      optread  = (fun () -> !Constrextern.print_implicits_defensive);
      optwrite = (fun b ->  Constrextern.print_implicits_defensive := b) }

let _ =
  declare_bool_option
    { optdepr  = false;
      optname  = "projection printing using dot notation";
      optkey   = ["Printing";"Projections"];
      optread  = (fun () -> !Constrextern.print_projections);
      optwrite = (fun b ->  Constrextern.print_projections := b) }

let _ =
  declare_bool_option
    { optdepr  = false;
      optname  = "notations printing";
      optkey   = ["Printing";"Notations"];
      optread  = (fun () -> not !Constrextern.print_no_symbol);
      optwrite = (fun b ->  Constrextern.print_no_symbol := not b) }

let _ =
  declare_bool_option
    { optdepr  = false;
      optname  = "raw printing";
      optkey   = ["Printing";"All"];
      optread  = (fun () -> !Flags.raw_print);
      optwrite = (fun b -> Flags.raw_print := b) }

let _ =
  declare_bool_option
    { optdepr  = false;
      optname  = "use of the program extension";
      optkey   = ["Program";"Mode"];
      optread  = (fun () -> !Flags.program_mode);
      optwrite = (fun b -> Flags.program_mode:=b) }

let _ =
  declare_bool_option
    { optdepr  = false;
      optname  = "universe polymorphism";
      optkey   = ["Universe"; "Polymorphism"];
      optread  = Flags.is_universe_polymorphism;
      optwrite = Flags.make_universe_polymorphism }

let _ =
  declare_bool_option
    { optdepr  = false;
      optname  = "Polymorphic inductive cumulativity";
      optkey   = ["Polymorphic"; "Inductive"; "Cumulativity"];
      optread  = Flags.is_polymorphic_inductive_cumulativity;
      optwrite = Flags.make_polymorphic_inductive_cumulativity }

let _ =
  declare_int_option
    { optdepr  = false;
      optname  = "the level of inlining during functor application";
      optkey   = ["Inline";"Level"];
      optread  = (fun () -> Some (Flags.get_inline_level ()));
      optwrite = (fun o ->
	           let lev = Option.default Flags.default_inline_level o in
	           Flags.set_inline_level lev) }

let _ =
  declare_bool_option
    { optdepr  = false;
      optname  = "kernel term sharing";
      optkey   = ["Kernel"; "Term"; "Sharing"];
      optread  = (fun () -> !CClosure.share);
      optwrite = (fun b -> CClosure.share := b) }

let _ =
  declare_bool_option
    { optdepr  = false;
      optname  = "display compact goal contexts";
      optkey   = ["Printing";"Compact";"Contexts"];
      optread  = (fun () -> Printer.get_compact_context());
      optwrite = (fun b -> Printer.set_compact_context b) }

let _ =
  declare_int_option
    { optdepr  = false;
      optname  = "the printing depth";
      optkey   = ["Printing";"Depth"];
      optread  = Topfmt.get_depth_boxes;
      optwrite = Topfmt.set_depth_boxes }

let _ =
  declare_int_option
    { optdepr  = false;
      optname  = "the printing width";
      optkey   = ["Printing";"Width"];
      optread  = Topfmt.get_margin;
      optwrite = Topfmt.set_margin }

let _ =
  declare_bool_option
    { optdepr  = false;
      optname  = "printing of universes";
      optkey   = ["Printing";"Universes"];
      optread  = (fun () -> !Constrextern.print_universes);
      optwrite = (fun b -> Constrextern.print_universes:=b) }
     
let _ =
  declare_bool_option
    { optdepr  = false;
      optname  = "dumping bytecode after compilation";
      optkey   = ["Dump";"Bytecode"];
      optread  = Flags.get_dump_bytecode;
      optwrite = Flags.set_dump_bytecode }

let _ =
  declare_bool_option
    { optdepr  = false;
      optname  = "explicitly parsing implicit arguments";
      optkey   = ["Parsing";"Explicit"];
      optread  = (fun () -> !Constrintern.parsing_explicit);
      optwrite = (fun b ->  Constrintern.parsing_explicit := b) }

let _ =
  declare_string_option ~preprocess:CWarnings.normalize_flags_string
    { optdepr  = false;
      optname  = "warnings display";
      optkey   = ["Warnings"];
      optread  = CWarnings.get_flags;
      optwrite = CWarnings.set_flags }

let _ =
  declare_string_option 
    { optdepr  = false;
      optname  = "native_compute profiler output";
      optkey   = ["NativeCompute"; "Profile"; "Filename"];
      optread  = Nativenorm.get_profile_filename;
      optwrite = Nativenorm.set_profile_filename }

let _ =
  declare_bool_option
    { optdepr  = false;
      optname  = "enable native compute profiling";
      optkey   = ["NativeCompute"; "Profiling"];
      optread  = Nativenorm.get_profiling_enabled;
      optwrite = Nativenorm.set_profiling_enabled }

let vernac_set_strategy ~atts l =
  let local = make_locality atts.locality in
  let glob_ref r =
    match smart_global r with
      | ConstRef sp -> EvalConstRef sp
      | VarRef id -> EvalVarRef id
      | _ -> user_err Pp.(str
          "cannot set an inductive type or a constructor as transparent") in
  let l = List.map (fun (lev,ql) -> (lev,List.map glob_ref ql)) l in
  Redexpr.set_strategy local l

let vernac_set_opacity ~atts (v,l) =
  let local = make_non_locality atts.locality in
  let glob_ref r =
    match smart_global r with
      | ConstRef sp -> EvalConstRef sp
      | VarRef id -> EvalVarRef id
      | _ -> user_err Pp.(str
          "cannot set an inductive type or a constructor as transparent") in
  let l = List.map glob_ref l in
  Redexpr.set_strategy local [v,l]

let vernac_set_option ~atts key = function
  | StringValue s -> set_string_option_value_gen atts.locality key s
  | StringOptValue (Some s) -> set_string_option_value_gen atts.locality key s
  | StringOptValue None -> unset_option_value_gen atts.locality key
  | IntValue n -> set_int_option_value_gen atts.locality key n
  | BoolValue b -> set_bool_option_value_gen atts.locality key b

let vernac_set_append_option ~atts key s =
  set_string_option_append_value_gen atts.locality key s

let vernac_unset_option ~atts key =
  unset_option_value_gen atts.locality key

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
  | Some n -> Pfedit.get_goal_context n
  | None -> Pfedit.get_current_context ()

let query_command_selector ?loc = function
  | None -> None
  | Some (SelectNth n) -> Some n
  | _ -> user_err ?loc ~hdr:"query_command_selector"
      (str "Query commands only support the single numbered goal selector.")

let vernac_check_may_eval ~atts redexp glopt rc =
  let glopt = query_command_selector ?loc:atts.loc glopt in
  let (sigma, env) = get_current_context_of_args glopt in
  let sigma', c = interp_open_constr env sigma rc in
  let c = EConstr.Unsafe.to_constr c in
  let sigma' = Evarconv.solve_unif_constraints_with_heuristics env sigma' in
  Evarconv.check_problems_are_solved env sigma';
  let sigma',nf = Evarutil.nf_evars_and_universes sigma' in
  let uctx = Evd.universe_context_set sigma' in
  let env = Environ.push_context_set uctx (Evarutil.nf_env_evar sigma' env) in
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
                    Printer.pr_universe_ctx_set sigma uctx)
    | Some r ->
        let (sigma',r_interp) = Hook.get f_interp_redexp env sigma' r in
	let redfun env evm c =
          let (redfun, _) = reduction_of_red_expr env r_interp in
          let (_, c) = redfun env evm c in
          c
        in
	Feedback.msg_notice (print_eval redfun env sigma' rc j)

let vernac_declare_reduction ~atts s r =
  let local = make_locality atts.locality in
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
  let pf = Proof_global.give_me_the_proof() in
  let gls,_,_,_,sigma = Proof.proof pf in
  let gl = {Evd.it=List.nth gls (n-1) ; sigma = sigma; } in
  gl
  
exception NoHyp
(* Printing "About" information of a hypothesis of the current goal.
   We only print the type and a small statement to this comes from the
   goal. Precondition: there must be at least one current goal. *)
let print_about_hyp_globs ?loc ref_or_by_not udecl glopt =
  let open Context.Named.Declaration in
  try
    (* FIXME error on non None udecl if we find the hyp. *)
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
    let sigma, env = Pfedit.get_current_context () in
    v 0 (Id.print id ++ str":" ++ pr_econstr_env env sigma (NamedDecl.get_type decl) ++ fnl() ++ fnl()
	 ++ str natureofid ++ str " of the goal context.")
  with (* fallback to globals *)
    | NoHyp | Not_found ->
    let sigma, env = Pfedit.get_current_context () in
    print_about env sigma ref_or_by_not udecl

let vernac_print ~atts env sigma =
  let open Feedback in
  let loc = atts.loc in
  function
  | PrintTables -> msg_notice (print_tables ())
  | PrintFullContext-> msg_notice (print_full_context_typ env sigma)
  | PrintSectionContext qid -> msg_notice (print_sec_context_typ env sigma qid)
  | PrintInspect n -> msg_notice (inspect env sigma n)
  | PrintGrammar ent -> msg_notice (Metasyntax.pr_grammar ent)
  | PrintLoadPath dir -> (* For compatibility ? *) msg_notice (print_loadpath dir)
  | PrintModules -> msg_notice (print_modules ())
  | PrintModule qid -> print_module qid
  | PrintModuleType qid -> print_modtype qid
  | PrintNamespace ns -> print_namespace ns
  | PrintMLLoadPath -> msg_notice (Mltop.print_ml_path ())
  | PrintMLModules -> msg_notice (Mltop.print_ml_modules ())
  | PrintDebugGC -> msg_notice (Mltop.print_gc ())
  | PrintName (qid,udecl) -> dump_global qid; msg_notice (print_name env sigma qid udecl)
  | PrintGraph -> msg_notice (Prettyp.print_graph())
  | PrintClasses -> msg_notice (Prettyp.print_classes())
  | PrintTypeClasses -> msg_notice (Prettyp.print_typeclasses())
  | PrintInstances c -> msg_notice (Prettyp.print_instances (smart_global c))
  | PrintCoercions -> msg_notice (Prettyp.print_coercions env sigma)
  | PrintCoercionPaths (cls,clt) ->
      msg_notice (Prettyp.print_path_between (cl_of_qualid cls) (cl_of_qualid clt))
  | PrintCanonicalConversions -> msg_notice (Prettyp.print_canonical_projections env sigma)
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
  | PrintHint r -> msg_notice (Hints.pr_hint_ref env sigma (smart_global r))
  | PrintHintGoal -> msg_notice (Hints.pr_applicable_hint ())
  | PrintHintDbName s -> msg_notice (Hints.pr_hint_db_by_name env sigma s)
  | PrintHintDb -> msg_notice (Hints.pr_searchtable env sigma)
  | PrintScopes ->
      msg_notice (Notation.pr_scopes (Constrextern.without_symbols (pr_lglob_constr_env env)))
  | PrintScope s ->
      msg_notice (Notation.pr_scope (Constrextern.without_symbols (pr_lglob_constr_env env)) s)
  | PrintVisibility s ->
      msg_notice (Notation.pr_visibility (Constrextern.without_symbols (pr_lglob_constr_env env)) s)
  | PrintAbout (ref_or_by_not,udecl,glnumopt) ->
     msg_notice (print_about_hyp_globs ?loc ref_or_by_not udecl glnumopt)
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
    { optdepr  = false;
      optname  = "output-name-only search";
      optkey   = ["Search";"Output";"Name";"Only"];
      optread  = (fun () -> !search_output_name_only);
      optwrite = (:=) search_output_name_only }

let vernac_search ~atts s gopt r =
  let gopt = query_command_selector ?loc:atts.loc gopt in
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
    let _, env = Pfedit.get_current_context () in
    msg_notice
      (Notation.locate_notation
         (Constrextern.without_symbols (pr_lglob_constr_env env)) ntn sc)
  | LocateLibrary qid -> print_located_library qid
  | LocateModule qid -> msg_notice (print_located_module qid)
  | LocateOther (s, qid) -> msg_notice (print_located_other s qid)
  | LocateFile f -> msg_notice (locate_file f)

let vernac_register id r =
 if Proof_global.there_are_pending_proofs () then
    user_err Pp.(str "Cannot register a primitive while in proof editing mode.");
  let kn = Constrintern.global_reference (snd id) in
  if not (isConstRef kn) then
    user_err Pp.(str "Register inline: a constant is expected");
  match r with
  | RegisterInline -> Global.register_inline (destConstRef kn)

(********************)
(* Proof management *)

let vernac_focus gln =
  Proof_global.simple_with_current_proof (fun _ p ->
    match gln with
      | None -> Proof.focus focus_command_cond () 1 p
      | Some 0 ->
         user_err Pp.(str "Invalid goal number: 0. Goal numbering starts with 1.")
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
    user_err Pp.(str "The proof is not fully unfocused.")


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

let vernac_bullet (bullet : Proof_bullet.t) =
  Proof_global.simple_with_current_proof (fun _ p ->
    Proof_bullet.put p bullet)

let vernac_show = let open Feedback in function
  | ShowScript -> assert false  (* Only the stm knows the script *)
  | ShowGoal goalref ->
    let proof = Proof_global.give_me_the_proof () in
    let info = match goalref with
      | OpenSubgoals -> pr_open_subgoals ~proof
      | NthGoal n -> pr_nth_open_subgoal ~proof n
      | GoalId id -> pr_goal_by_id ~proof id
    in
    msg_notice info
  | ShowProof -> show_proof ()
  | ShowExistentials -> show_top_evars ()
  | ShowUniverses -> show_universes ()
  | ShowProofNames ->
      msg_notice (pr_sequence Id.print (Proof_global.get_all_proof_names()))
  | ShowIntros all -> show_intro all
  | ShowMatch id -> show_match id

let vernac_check_guard () =
  let pts = Proof_global.give_me_the_proof () in
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
    let proof_mode = Proof_global.get_default_proof_mode_name () [@ocaml.warning "-3"] in
    Proof_global.activate_proof_mode proof_mode [@ocaml.warning "-3"];
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
    Pcoq.Gram.parsable ~file:(Loc.InFile longfname) (Stream.of_channel in_chan) in
  try while true do interp (snd (parse_sentence input)) done
  with End_of_input -> ()

(* "locality" is the prefix "Local" attribute, while the "local" component
 * is the outdated/deprecated "Local" attribute of some vernacular commands
 * still parsed as the obsolete_locality grammar entry for retrocompatibility.
 * loc is the Loc.t of the vernacular command being interpreted. *)
let interp ?proof ~atts ~st c =
  let open Vernacinterp in
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

  (* The STM should handle that, but LOAD bypasses the STM... *)
  | VernacAbortAll    -> CErrors.user_err  (str "AbortAll cannot be used through the Load command")
  | VernacRestart     -> CErrors.user_err  (str "Restart cannot be used through the Load command")
  | VernacUndo _      -> CErrors.user_err  (str "Undo cannot be used through the Load command")
  | VernacUndoTo _    -> CErrors.user_err  (str "UndoTo cannot be used through the Load command")
  | VernacBacktrack _ -> CErrors.user_err  (str "Backtrack cannot be used through the Load command")

  (* Toplevel control *)
  | VernacToplevelControl e -> raise e

  (* Resetting *)
  | VernacResetName _  -> anomaly (str "VernacResetName not handled by Stm.")
  | VernacResetInitial -> anomaly (str "VernacResetInitial not handled by Stm.")
  | VernacBack _       -> anomaly (str "VernacBack not handled by Stm.")
  | VernacBackTo _     -> anomaly (str "VernacBackTo not handled by Stm.")

  (* This one is possible to handle here *)
  | VernacAbort id    -> CErrors.user_err  (str "Abort cannot be used through the Load command")

  (* Handled elsewhere *)
  | VernacProgram _
  | VernacPolymorphic _
  | VernacLocal _ -> assert false

  (* Syntax *)
  | VernacSyntaxExtension (infix, sl) ->
      vernac_syntax_extension atts infix sl
  | VernacDelimiters (sc,lr) -> vernac_delimiters sc lr
  | VernacBindScope (sc,rl) -> vernac_bind_scope sc rl
  | VernacOpenCloseScope (b, s) -> vernac_open_close_scope ~atts (b,s)
  | VernacArgumentsScope (qid,scl) -> vernac_arguments_scope ~atts qid scl
  | VernacInfix (mv,qid,sc) -> vernac_infix ~atts mv qid sc
  | VernacNotation (c,infpl,sc) ->
      vernac_notation ~atts c infpl sc
  | VernacNotationAddFormat(n,k,v) ->
      Metasyntax.add_notation_extra_printing_rule n k v

  (* Gallina *)
  | VernacDefinition ((discharge,kind),lid,d) ->
      vernac_definition ~atts discharge kind lid d
  | VernacStartTheoremProof (k,l) -> vernac_start_proof ~atts k l
  | VernacEndProof e -> vernac_end_proof ?proof e
  | VernacExactProof c -> vernac_exact_proof c
  | VernacAssumption ((discharge,kind),nl,l) ->
      vernac_assumption ~atts discharge kind l nl
  | VernacInductive (cum, priv,finite,l) -> vernac_inductive ~atts cum priv finite l
  | VernacFixpoint (discharge, l) -> vernac_fixpoint ~atts discharge l
  | VernacCoFixpoint (discharge, l) -> vernac_cofixpoint ~atts discharge l
  | VernacScheme l -> vernac_scheme l
  | VernacCombinedScheme (id, l) -> vernac_combined_scheme id l
  | VernacUniverse l -> vernac_universe ~atts l
  | VernacConstraint l -> vernac_constraint ~atts l

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
  | VernacCoercion (r,s,t) -> vernac_coercion ~atts r s t
  | VernacIdentityCoercion ((_,id),s,t) ->
      vernac_identity_coercion ~atts id s t

  (* Type classes *)
  | VernacInstance (abst, sup, inst, props, info) ->
      vernac_instance ~atts abst sup inst props info
  | VernacContext sup -> vernac_context ~atts sup
  | VernacDeclareInstances insts -> vernac_declare_instances ~atts insts
  | VernacDeclareClass id -> vernac_declare_class id

  (* Solving *)
  | VernacSolveExistential (n,c) -> vernac_solve_existential n c

  (* Auxiliary file and library management *)
  | VernacAddLoadPath (isrec,s,alias) -> vernac_add_loadpath isrec s alias
  | VernacRemoveLoadPath s -> vernac_remove_loadpath s
  | VernacAddMLPath (isrec,s) -> vernac_add_ml_path isrec s
  | VernacDeclareMLModule l -> vernac_declare_ml_module ~atts l
  | VernacChdir s -> vernac_chdir s

  (* State management *)
  | VernacWriteState s -> vernac_write_state s
  | VernacRestoreState s -> vernac_restore_state s

  (* Commands *)
  | VernacCreateHintDb (dbname,b) -> vernac_create_hintdb ~atts dbname b
  | VernacRemoveHints (dbnames,ids) -> vernac_remove_hints ~atts dbnames ids
  | VernacHints (dbnames,hints) ->
      vernac_hints ~atts dbnames hints
  | VernacSyntacticDefinition (id,c,b) ->
      vernac_syntactic_definition ~atts id c b
  | VernacDeclareImplicits (qid,l) ->
      vernac_declare_implicits ~atts qid l
  | VernacArguments (qid, args, more_implicits, nargs, flags) ->
      vernac_arguments ~atts qid args more_implicits nargs flags
  | VernacReserve bl -> vernac_reserve bl
  | VernacGeneralizable gen -> vernac_generalizable ~atts gen
  | VernacSetOpacity qidl -> vernac_set_opacity ~atts qidl
  | VernacSetStrategy l -> vernac_set_strategy ~atts l
  | VernacSetOption (key,v) -> vernac_set_option ~atts key v
  | VernacSetAppendOption (key,v) -> vernac_set_append_option ~atts key v
  | VernacUnsetOption key -> vernac_unset_option ~atts key
  | VernacRemoveOption (key,v) -> vernac_remove_option key v
  | VernacAddOption (key,v) -> vernac_add_option key v
  | VernacMemOption (key,v) -> vernac_mem_option key v
  | VernacPrintOption key -> vernac_print_option key
  | VernacCheckMayEval (r,g,c) -> vernac_check_may_eval ~atts r g c
  | VernacDeclareReduction (s,r) -> vernac_declare_reduction ~atts s r
  | VernacGlobalCheck c -> vernac_global_check c
  | VernacPrint p ->
    let sigma, env = Pfedit.get_current_context () in
    vernac_print ~atts env sigma p
  | VernacSearch (s,g,r) -> vernac_search ~atts s g r
  | VernacLocate l -> vernac_locate l
  | VernacRegister (id, r) -> vernac_register id r
  | VernacComments l -> Flags.if_verbose Feedback.msg_info (str "Comments ok\n")

  (* Proof management *)
  | VernacGoal t -> vernac_start_proof ~atts Theorem [None,([],t)]
  | VernacFocus n -> vernac_focus n
  | VernacUnfocus -> vernac_unfocus ()
  | VernacUnfocused -> vernac_unfocused ()
  | VernacBullet b -> vernac_bullet b
  | VernacSubproof n -> vernac_subproof n
  | VernacEndSubproof -> vernac_end_subproof ()
  | VernacShow s -> vernac_show s
  | VernacCheckGuard -> vernac_check_guard ()
  | VernacProof (tac, using) ->
    let using = Option.append using (Proof_using.get_default_proof_using ()) in
    let tacs = if Option.is_empty tac then "tac:no" else "tac:yes" in
    let usings = if Option.is_empty using then "using:no" else "using:yes" in
    Aux_file.record_in_aux_at ?loc:atts.loc "VernacProof" (tacs^" "^usings);
    Option.iter vernac_set_end_tac tac;
    Option.iter vernac_set_used_variables using
  | VernacProofMode mn -> Proof_global.set_proof_mode mn [@ocaml.warning "-3"]

  (* Extensions *)
  | VernacExtend (opn,args) ->
    (* XXX: Here we are returning the state! :) *)
    let _st : Vernacstate.t = Vernacinterp.call ~atts opn args ~st in
    ()

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
  | Some _, _ -> user_err Pp.(str "This command does not support Locality")

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
  | Some _, _ -> user_err Pp.(str "This command does not support Polymorphism")

let enforce_polymorphism = function
  | None   -> Flags.is_universe_polymorphism ()
  | Some b -> Flags.make_polymorphic_flag b; b

(** A global default timeout, controlled by option "Set Default Timeout n".
    Use "Unset Default Timeout" to deactivate it (or set it to 0). *)

let default_timeout = ref None

let _ =
  Goptions.declare_int_option
    { Goptions.optdepr  = false;
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
      Control.timeout n f () Timeout
    | None, None -> f ()

let restore_timeout () = current_timeout := None

let locate_if_not_already ?loc (e, info) =
  match Loc.get_loc info with
  | None   -> (e, Option.cata (Loc.add_loc info) info loc)
  | Some l -> (e, info)

exception HasNotFailed
exception HasFailed of Pp.t

(* XXX STATE: this type hints that restoring the state should be the
   caller's responsibility *)
let with_fail st b f =
  if not b
  then f ()
  else begin try
      (* If the command actually works, ignore its effects on the state.
       * Note that error has to be printed in the right state, hence
       * within the purified function *)
      try f (); raise HasNotFailed
      with
      | HasNotFailed as e -> raise e
      | e ->
        let e = CErrors.push e in
        raise (HasFailed (CErrors.iprint
                            (ExplainErr.process_vernac_interp_error ~allow_uncaught:false e)))
    with e when CErrors.noncritical e ->
      (* Restore the previous state XXX Careful here with the cache! *)
      Vernacstate.invalidate_cache ();
      Vernacstate.unfreeze_interp_state st;
      let (e, _) = CErrors.push e in
      match e with
      | HasNotFailed ->
          user_err ~hdr:"Fail" (str "The command has not failed!")
      | HasFailed msg ->
          if not !Flags.quiet || !Flags.test_mode || !Flags.ide_slave then Feedback.msg_info
            (str "The command has indeed failed with message:" ++ fnl () ++ msg)
      | _ -> assert false
  end

let interp ?(verbosely=true) ?proof ~st (loc,c) =
  let orig_program_mode = Flags.is_program_mode () in
  let rec aux ?polymorphism ~atts isprogcmd = function

    | VernacProgram c when not isprogcmd ->
      aux ?polymorphism ~atts true c

    | VernacProgram _ ->
      user_err Pp.(str "Program mode specified twice")

    | VernacPolymorphic (b, c) when polymorphism = None ->
      aux ~polymorphism:b ~atts:atts isprogcmd c

    | VernacPolymorphic (b, c) ->
      user_err Pp.(str "Polymorphism specified twice")

    | VernacLocal (b, c) when Option.is_empty atts.locality ->
      aux ?polymorphism ~atts:{atts with locality = Some b} isprogcmd c

    | VernacLocal _ ->
      user_err Pp.(str "Locality specified twice")

    | VernacFail v ->
      with_fail st true (fun () -> aux ?polymorphism ~atts isprogcmd v)

    | VernacTimeout (n,v) ->
      current_timeout := Some n;
      aux ?polymorphism ~atts isprogcmd v

    | VernacRedirect (s, (_,v)) ->
      Topfmt.with_output_to_file s (aux ?polymorphism ~atts isprogcmd) v

    | VernacTime (_,v) ->
      System.with_time !Flags.time (aux ?polymorphism ~atts isprogcmd) v;

    | VernacLoad (_,fname) -> vernac_load (aux ?polymorphism ~atts false) fname

    | c ->
      check_vernac_supports_locality c atts.locality;
      check_vernac_supports_polymorphism c polymorphism;
      let polymorphic = enforce_polymorphism polymorphism in
      Obligations.set_program_mode isprogcmd;
      try
        vernac_timeout begin fun () ->
          let atts = { atts with polymorphic } in
          if verbosely
          then Flags.verbosely (interp ?proof ~atts ~st) c
          else Flags.silently  (interp ?proof ~atts ~st) c;
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
  let atts = { loc; locality = None; polymorphic = false; } in
  if verbosely
  then Flags.verbosely (aux ~atts orig_program_mode) c
  else aux ~atts orig_program_mode c

(* XXX: There is a bug here in case of an exception, see @gares
   comments on the PR *)
let interp ?verbosely ?proof ~st cmd =
  Vernacstate.unfreeze_interp_state st;
  try
    interp ?verbosely ?proof ~st cmd;
    Vernacstate.freeze_interp_state `No
  with exn ->
    let exn = CErrors.push exn in
    Vernacstate.invalidate_cache ();
    iraise exn
