(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Pp
open Util
open Names
open Coqast
open Topconstr
open Vernacexpr
open Pcoq
open Tactic
open Decl_kinds
open Genarg
open Extend
open Ppextend
open Goptions

open Prim
open Constr
open Vernac_
open Module


let vernac_kw = [ ";"; ","; ">->"; ":<"; "<:" ]
let _ = List.iter (fun s -> Lexer.add_token ("",s)) vernac_kw

(* Rem: do not join the different GEXTEND into one, it breaks native *)
(* compilation on PowerPC and Sun architectures *)

let check_command = Gram.Entry.create "vernac:check_command"
let class_rawexpr = Gram.Entry.create "vernac:class_rawexpr"
let thm_token = Gram.Entry.create "vernac:thm_token"
let def_body = Gram.Entry.create "vernac:def_body"

GEXTEND Gram
  GLOBAL: vernac gallina_ext;
  vernac:
    (* Better to parse ";" here: in case of failure (e.g. in coerce_to_var), *)
    (* ";" is still in the stream and discard_to_dot works correctly         *)
    [ [ g = gallina; ";" -> g 
      | g = gallina_ext; ";" -> g
      | c = command; ";" -> c 
      | c = syntax; ";" -> c
      | "["; l = LIST1 located_vernac; "]"; ";" -> VernacList l
    ] ]
  ;
  vernac: FIRST
    [ [ IDENT "Time"; v = vernac  -> VernacTime v ] ]
  ;
  vernac: LAST
    [ [ gln = OPT[n=natural; ":" -> n];
        tac = subgoal_command; ";" -> tac gln ] ]
  ;
  subgoal_command:
    [ [ c = check_command -> c
      | d = use_default_tac; tac = Tactic.tactic ->
          (fun g ->
            let g = match g with Some gl -> gl | _ -> 1 in
            VernacSolve(g,tac,d)) ] ]
  ;
  located_vernac:
    [ [ v = vernac -> loc, v ] ]
  ;
  use_default_tac:
    [ [ "!!" -> false 
      | -> true ] ]
  ;
END


let test_plurial_form = function
  | [_] ->
      Options.if_verbose warning
   "Keywords Variables/Hypotheses/Parameters expect more than one assumption"
  | _ -> ()

let no_coercion loc (c,x) =
  if c then Util.user_err_loc
    (loc,"no_coercion",Pp.str"no coercion allowed here");
  x

(* Gallina declarations *)
GEXTEND Gram
  GLOBAL: gallina gallina_ext thm_token def_body;

  gallina:
      (* Definition, Theorem, Variable, Axiom, ... *)
    [ [ thm = thm_token; id = base_ident; bl = LIST0 binder; ":";
        c = lconstr ->
          VernacStartTheoremProof (thm, id, (bl, c), false, (fun _ _ -> ()))
      | (f,d,e) = def_token; id = base_ident; b = def_body -> 
          VernacDefinition (d, id, b, f, e)
      | stre = assumption_token; bl = LIST1 simple_binder_coe -> 
	  VernacAssumption (stre, bl)
      | stre = assumptions_token; bl = LIST1 simple_binder_coe ->
	  test_plurial_form bl;
	  VernacAssumption (stre, bl)
      (* Gallina inductive declarations *)
      | OPT[IDENT "Mutual"]; f = finite_token;
        indl = LIST1 inductive_definition SEP "with" ->
          VernacInductive (f,indl)
      | IDENT "Fixpoint"; recs = LIST1 rec_definition SEP "with" ->
          VernacFixpoint recs
      | IDENT "CoFixpoint"; corecs = LIST1 corec_definition SEP "with" ->
          VernacCoFixpoint corecs
      | IDENT "Scheme"; l = LIST1 scheme SEP "with" -> VernacScheme l ] ]
  ;
  gallina_ext:
    [ [ record_token; oc = opt_coercion; name = base_ident;
        ps = LIST0 simple_binder; ":";
	s = lconstr; ":="; cstr = OPT base_ident; "{";
        fs = LIST0 local_decl_expr; "}" ->
	  VernacRecord ((oc,name),ps,s,cstr,fs)
      | f = finite_token; s = csort; id = base_ident;
        indpar = LIST0 simple_binder; ":="; lc = constructor_list -> 
          VernacInductive (f,[id,indpar,s,lc])
    ] ]
  ;
  thm_token:
    [ [ IDENT "Theorem" -> Theorem
      | IDENT "Lemma" -> Lemma
      | IDENT "Fact" -> Fact
      | IDENT "Remark" -> Remark ] ]
  ;
  def_token:
    [ [ IDENT "Definition" -> (fun _ _ -> ()), Global, GDefinition
      | IDENT "Local" -> (fun _ _ -> ()), Local, LDefinition
      | IDENT "SubClass"  -> Class.add_subclass_hook, Global, GCoercion
      | IDENT "Local"; IDENT "SubClass"  ->
          Class.add_subclass_hook, Local, LCoercion ] ] 
  ;
  assumption_token:
    [ [ IDENT "Hypothesis" -> (Local, Logical)
      | IDENT "Variable" -> (Local, Definitional)
      | IDENT "Axiom" -> (Global, Logical)
      | IDENT "Parameter" -> (Global, Definitional) ] ]
  ;
  assumptions_token:
    [ [ IDENT "Hypotheses" -> (Local, Logical)
      | IDENT "Variables" -> (Local, Definitional)
      | IDENT "Parameters" -> (Global, Definitional) ] ]
  ;
  finite_token:
    [ [ IDENT "Inductive" -> true
      | IDENT "CoInductive" -> false ] ]
  ;
  record_token:
    [ [ IDENT "Record" -> () | IDENT "Structure" -> () ] ]
  ;
  (* Simple definitions *)
  def_body:
    [ [ bl = LIST0 binder; ":="; red = reduce; c = lconstr ->
      (match c with
          CCast(_,c,t) -> DefineBody (bl, red, c, Some t)
        | _ -> DefineBody (bl, red, c, None))
      | bl = LIST0 binder; ":"; t = lconstr; ":="; red = reduce; c = lconstr ->
          DefineBody (bl, red, c, Some t)
      | bl = LIST0 binder; ":"; t = lconstr ->
          ProveBody (bl, t) ] ]
  ;
  reduce:
    [ [ IDENT "Eval"; r = Tactic.red_expr; "in" -> Some r
      | -> None ] ]
  ;
  (* Inductives and records *)
  inductive_definition:
    [ [ id = base_ident; indpar = LIST0 simple_binder; ":"; c = lconstr; ":=";
	lc = constructor_list -> (id,indpar,c,lc) ] ]
  ;
  constructor_list:
    [ [ "|"; l = LIST1 constructor_binder SEP "|" -> l
      | l = LIST1 constructor_binder SEP "|" -> l
      |  -> [] ] ]
  ;
  csort:
    [ [ s = sort -> CSort (loc,s) ] ]
  ;
  opt_coercion:
    [ [ ">" -> true
      |  -> false ] ]
  ;
  (* (co)-fixpoints *)
  rec_definition:
    [ [ id = base_ident; bl = LIST1 binder_nodef; ":"; type_ = lconstr;
        ":="; def = lconstr ->
          let ni = List.length (List.flatten (List.map fst bl)) - 1 in
          let loc0 = fst (List.hd (fst (List.hd bl))) in
          let loc1 = join_loc loc0 (constr_loc type_) in
          let loc2 = join_loc loc0 (constr_loc def) in
	  (id, ni, CProdN (loc1,bl,type_), CLambdaN (loc2,bl,def)) ] ]
  ;
  corec_definition:
    [ [ id = base_ident; ":"; c = lconstr; ":="; def = lconstr ->
          (id,c,def) ] ]
  ;
  (* Inductive schemes *)
  scheme:
    [ [ id = base_ident; ":="; dep = dep_scheme; "for"; ind = global;
        IDENT "Sort"; s = sort ->
          (id,dep,ind,s) ] ]
  ;
  dep_scheme:
    [ [ IDENT "Induction" -> true
      | IDENT "Minimality" -> false ] ]
  ;
  (* Various Binders *)
  (* ... without coercions *)
  simple_binder:
    [ [ b = simple_binder_coe -> no_coercion loc b ] ]
  ;
  binder:
    [ [ na = name ->  LocalRawAssum([na],CHole loc)
      | "("; na = name; ")" -> LocalRawAssum([na],CHole loc)
      | "("; na = name; ":"; c = lconstr; ")"
          -> LocalRawAssum([na],c)
      | "("; na = name; ":="; c = lconstr; ")" ->
          LocalRawDef (na,c)
    ] ]
  ;
  binder_nodef:
    [ [ b = binder ->
      (match b with
          LocalRawAssum(l,ty) -> (l,ty)
        | LocalRawDef _ ->
            Util.user_err_loc
              (loc,"fix_param",Pp.str"defined binder not allowed here")) ] ]
  ;
  (* ... with coercions *)
  local_decl_expr:
    [ [ id = base_ident -> (false,AssumExpr(id,CHole loc))
      | "("; id = base_ident; ")" -> (false,AssumExpr(id,CHole loc))
      | "("; id = base_ident; oc = of_type_with_opt_coercion;
             t = lconstr; ")" ->
         (oc,AssumExpr (id,t))
      | "("; id = base_ident; oc = of_type_with_opt_coercion;
             t = lconstr; ":="; b = lconstr; ")" ->
	 (oc,DefExpr (id,b,Some t))
      | "("; id = base_ident; ":="; b = lconstr; ")" ->
         match b with
             CCast(_,b,t) -> (false,DefExpr(id,b,Some t))
           | _ -> (false,DefExpr(id,b,None)) ] ]
  ;
  simple_binder_coe:
    [ [ id=base_ident -> (false,(id,CHole loc))
      | "("; id = base_ident; ")" -> (false,(id,CHole loc))
      | "("; id = base_ident; oc = of_type_with_opt_coercion;
             t = lconstr; ")" ->
         (oc,(id,t)) ] ]
  ;
  constructor_binder:
    [ [ id = base_ident; coe = of_type_with_opt_coercion; c = lconstr ->
        (coe,(id,c)) ] ]
  ;
  of_type_with_opt_coercion:
    [ [ ":>" -> true
      | ":"; ">" -> true
      | ":" -> false ] ]
  ;
END


(* Modules and Sections *)
GEXTEND Gram
  GLOBAL: gallina_ext module_expr module_type;

  gallina_ext:
    [ [ (* Interactive module declaration *)
	IDENT "Module"; id = base_ident; 
	bl = LIST0 module_binder; mty_o = OPT of_module_type; 
	mexpr_o = OPT is_module_expr ->
	  VernacDefineModule (id, bl, mty_o, mexpr_o)
	  
      | IDENT "Module"; "Type"; id = base_ident; 
	bl = LIST0 module_binder; mty_o = OPT is_module_type ->
	  VernacDeclareModuleType (id, bl, mty_o)
	  
      | IDENT "Declare"; IDENT "Module"; id = base_ident; 
	bl = LIST0 module_binder; mty_o = OPT of_module_type; 
	mexpr_o = OPT is_module_expr ->
	  VernacDeclareModule (id, bl, mty_o, mexpr_o)
      (* Section beginning *)
      | IDENT "Section"; id = base_ident -> VernacBeginSection id
      | IDENT "Chapter"; id = base_ident -> VernacBeginSection id

      (* This end a Section a Module or a Module Type *)
      | IDENT "End"; id = base_ident -> VernacEndSegment id

      (* Requiring an already compiled module *)
      | IDENT "Require"; export = export_token; specif = specif_token;
        qidl = LIST1 global ->
          VernacRequire (export, specif, qidl)
      | IDENT "Require"; export = export_token; specif = specif_token;
        filename = STRING -> 
	  VernacRequireFrom (export, specif, filename)
      | IDENT "Import"; qidl = LIST1 global -> VernacImport (false,qidl)
      | IDENT "Export"; qidl = LIST1 global -> VernacImport (true,qidl) ] ]
  ;
  export_token:
    [ [ IDENT "Import" -> Some false
      | IDENT "Export" -> Some true
      | IDENT "Closed" -> None
      |  -> Some false ] ]
  ;
  specif_token:
    [ [ IDENT "Implementation" -> Some false
      | IDENT "Specification" -> Some true
      |  -> None ] ]
  ;
  of_module_type:
    [ [ ":"; mty = module_type -> (mty, true) 
      | "<:"; mty = module_type -> (mty, false) ] ]
  ;
  is_module_type:
    [ [ ":="; mty = module_type -> mty ] ]
  ;
  is_module_expr:
    [ [ ":="; mexpr = module_expr -> mexpr ] ]
  ;

  (* Module binder  *)
  module_binder:
    [ [ "("; id = base_ident; ":"; mty = module_type; ")" ->
          ([id],mty) ] ]
  ;

  (* Module expressions *)
  module_expr:
    [ [ qid = qualid -> CMEident qid
      | me1 = module_expr; me2 = module_expr -> CMEapply (me1,me2)
      | "("; me = module_expr; ")" -> me
(* ... *)
      ] ]
  ;
  with_declaration:
    [ [ IDENT "Definition"; id = base_ident; ":="; c = Constr.constr ->
          CWith_Definition (id,c)
      | IDENT "Module"; id = base_ident; ":="; qid = qualid ->
	  CWith_Module (id,qid)
      ] ]
  ;
  module_type:
    [ [ qid = qualid -> CMTEident qid
(* ... *)
      | mty = module_type; "with"; decl = with_declaration -> 
	  CMTEwith (mty,decl) ] ]
  ;
END

(* Extensions: implicits, coercions, etc. *)   
GEXTEND Gram
  GLOBAL: gallina_ext;

  gallina_ext:
    [ [ (* Transparent and Opaque *)
        IDENT "Transparent"; l = LIST1 global -> VernacSetOpacity (false, l)
      | IDENT "Opaque"; l = LIST1 global -> VernacSetOpacity (true, l)

      (* Canonical structure *)
      | IDENT "Canonical"; IDENT "Structure"; qid = global ->
	  VernacCanonical qid
      | IDENT "Canonical"; IDENT "Structure"; qid = global; d = def_body ->
          let s = Ast.coerce_global_to_id qid in
	  VernacDefinition (Global,s,d,Recordobj.add_object_hook,SCanonical)

      (* Coercions *)
      | IDENT "Coercion"; qid = global; d = def_body ->
          let s = Ast.coerce_global_to_id qid in
	  VernacDefinition (Global,s,d,Class.add_coercion_hook,GCoercion)
      | IDENT "Coercion"; IDENT "Local"; qid = global; d = def_body ->
           let s = Ast.coerce_global_to_id qid in
	  VernacDefinition (Local,s,d,Class.add_coercion_hook,LCoercion)
      | IDENT "Identity"; IDENT "Coercion"; IDENT "Local"; f = base_ident;
         ":"; s = class_rawexpr; ">->"; t = class_rawexpr -> 
	   VernacIdentityCoercion (Local, f, s, t)
      | IDENT "Identity"; IDENT "Coercion"; f = base_ident; ":";
         s = class_rawexpr; ">->"; t = class_rawexpr -> 
	   VernacIdentityCoercion (Global, f, s, t)
      | IDENT "Coercion"; IDENT "Local"; qid = global; ":";
	 s = class_rawexpr; ">->"; t = class_rawexpr -> 
	  VernacCoercion (Local, qid, s, t)
      | IDENT "Coercion"; qid = global; ":"; s = class_rawexpr; ">->";
         t = class_rawexpr ->
	  VernacCoercion (Global, qid, s, t)

      (* Implicit *)
      | IDENT "Syntactic"; IDENT "Definition"; id = IDENT; ":="; c = lconstr;
         n = OPT [ "|"; n = natural -> n ] ->
	   let c = match n with
	     | Some n ->
		 let l = list_tabulate (fun _ -> (CHole (loc),None)) n in
		 CApp (loc,c,l)
	     | None -> c in
	   VernacNotation ("'"^id^"'",c,[],None,None)
      | IDENT "Implicits"; qid = global; "["; l = LIST0 natural; "]" ->
	  VernacDeclareImplicits (qid,Some l)
      | IDENT "Implicits"; qid = global -> VernacDeclareImplicits (qid,None)

      (* For compatibility *)
      | IDENT "Implicit"; IDENT "Arguments"; IDENT "On" ->
	  VernacSetOption
	    (Goptions.SecondaryTable ("Implicit","Arguments"),
             BoolValue true)
      | IDENT "Implicit"; IDENT "Arguments"; IDENT "Off" ->
	  VernacSetOption
	    (Goptions.SecondaryTable ("Implicit","Arguments"),
             BoolValue false) ] ]
  ;
END

GEXTEND Gram
  GLOBAL: command check_command class_rawexpr;

  command:
    [ [ IDENT "Comments"; l = LIST0 comment -> VernacComments l

      (* System directory *)
      | IDENT "Pwd" -> VernacChdir None
      | IDENT "Cd" -> VernacChdir None
      | IDENT "Cd"; dir = STRING -> VernacChdir (Some dir)

      (* Toplevel control *)
      | IDENT "Drop" -> VernacToplevelControl Drop
      | IDENT "ProtectedLoop" -> VernacToplevelControl ProtectedLoop
      | IDENT "Quit" -> VernacToplevelControl Quit

      | IDENT "Load"; verbosely = [ IDENT "Verbose" -> true | -> false ];
	s = [ s = STRING -> s | s = IDENT -> s ] ->
	  VernacLoad (verbosely, s)
      | IDENT "Declare"; IDENT "ML"; IDENT "Module"; l = LIST1 STRING ->
	  VernacDeclareMLModule l

      (* Dump of the universe graph - to file or to stdout *) 
      | IDENT "Dump"; IDENT "Universes"; fopt = OPT STRING ->
	  VernacPrint (PrintUniverses fopt)

      | IDENT "Locate"; l = locatable -> VernacLocate l

      (* Managing load paths *)
      | IDENT "Add"; IDENT "LoadPath"; dir = STRING; alias = as_dirpath ->
	  VernacAddLoadPath (false, dir, alias)
      | IDENT "Add"; IDENT "Rec"; IDENT "LoadPath"; dir = STRING; 
	  alias = as_dirpath -> VernacAddLoadPath (true, dir, alias)
      | IDENT "Remove"; IDENT "LoadPath"; dir = STRING ->
	  VernacRemoveLoadPath dir

       (* For compatibility *)
      | IDENT "AddPath"; dir = STRING; "as"; alias = as_dirpath ->
	  VernacAddLoadPath (false, dir, alias)
      | IDENT "AddRecPath"; dir = STRING; "as"; alias = as_dirpath ->
	  VernacAddLoadPath (true, dir, alias)
      | IDENT "DelPath"; dir = STRING ->
	  VernacRemoveLoadPath dir

      (* Type-Checking (pas dans le refman) *)
      | "Type"; c = lconstr -> VernacGlobalCheck c

      (* Printing (careful factorization of entries) *)
      | IDENT "Print"; p = printable -> VernacPrint p
      | IDENT "Print"; qid = global -> VernacPrint (PrintName qid)
      | IDENT "Print" -> VernacPrint PrintLocalContext 
      | IDENT "Print"; IDENT "Module"; "Type"; qid = global -> 
	  VernacPrint (PrintModuleType qid)
      | IDENT "Print"; IDENT "Module"; qid = global -> 
	  VernacPrint (PrintModule qid)
      | IDENT "Inspect"; n = natural -> VernacPrint (PrintInspect n)

      (* Searching the environment *)
      | IDENT "Search"; qid = global; l = in_or_out_modules -> 
	  VernacSearch (SearchHead qid, l)
      | IDENT "SearchPattern"; c = constr_pattern; l = in_or_out_modules ->
	  VernacSearch (SearchPattern c, l)
      | IDENT "SearchRewrite"; c = constr_pattern; l = in_or_out_modules ->
	  VernacSearch (SearchRewrite c, l)
      | IDENT "SearchAbout"; qid = global; l = in_or_out_modules -> 
	  VernacSearch (SearchAbout qid, l)

      | IDENT "Add"; IDENT "ML"; IDENT "Path"; dir = STRING ->
	  VernacAddMLPath (false, dir)
      | IDENT "Add"; IDENT "Rec"; IDENT "ML"; IDENT "Path"; dir = STRING ->
	  VernacAddMLPath (true, dir)

      (* Pour intervenir sur les tables de paramètres *)
      | "Set"; table = IDENT; field = IDENT; v = option_value ->
  	  VernacSetOption (SecondaryTable (table,field),v)
      | "Set"; table = IDENT; field = IDENT; lv = LIST1 option_ref_value ->
  	  VernacAddOption (SecondaryTable (table,field),lv)
      | "Set"; table = IDENT; field = IDENT ->
  	  VernacSetOption (SecondaryTable (table,field),BoolValue true)
      | IDENT "Unset"; table = IDENT; field = IDENT ->
  	  VernacUnsetOption (SecondaryTable (table,field))
      | IDENT "Unset"; table = IDENT; field = IDENT; lv = LIST1 option_ref_value ->
  	  VernacRemoveOption (SecondaryTable (table,field),lv)
      | "Set"; table = IDENT; value = option_value ->
  	  VernacSetOption (PrimaryTable table, value)
      | "Set"; table = IDENT ->
  	  VernacSetOption (PrimaryTable table, BoolValue true)
      | IDENT "Unset"; table = IDENT ->
  	  VernacUnsetOption (PrimaryTable table)

      | IDENT "Print"; IDENT "Table"; table = IDENT; field = IDENT ->
	  VernacPrintOption (SecondaryTable (table,field))
      | IDENT "Print"; IDENT "Table"; table = IDENT ->
	  VernacPrintOption (PrimaryTable table)

      | IDENT "Add"; table = IDENT; field = IDENT; v = LIST1 option_ref_value
        -> VernacAddOption (SecondaryTable (table,field), v)

      (* Un value global ci-dessous va être caché par un field au dessus! *)
      | IDENT "Add"; table = IDENT; v = LIST1 option_ref_value ->
          VernacAddOption (PrimaryTable table, v)

      | IDENT "Test"; table = IDENT; field = IDENT; v = LIST1 option_ref_value
        -> VernacMemOption (SecondaryTable (table,field), v)
      | IDENT "Test"; table = IDENT; field = IDENT ->
          VernacPrintOption (SecondaryTable (table,field))
      | IDENT "Test"; table = IDENT; v = LIST1 option_ref_value ->
          VernacMemOption (PrimaryTable table, v)
      | IDENT "Test"; table = IDENT ->
          VernacPrintOption (PrimaryTable table)

      | IDENT "Remove"; table = IDENT; field = IDENT; v= LIST1 option_ref_value
        -> VernacRemoveOption (SecondaryTable (table,field), v)
      | IDENT "Remove"; table = IDENT; v = LIST1 option_ref_value ->
	  VernacRemoveOption (PrimaryTable table, v) ] ]
  ;
  check_command: (* TODO: rapprocher Eval et Check *)
    [ [ IDENT "Eval"; r = Tactic.red_expr; "in"; c = lconstr ->
          fun g -> VernacCheckMayEval (Some r, g, c)
      | IDENT "Check"; c = lconstr ->
	  fun g -> VernacCheckMayEval (None, g, c) ] ]
  ;
  printable:
    [ [ IDENT "Term"; qid = global -> PrintName qid
      | IDENT "All" -> PrintFullContext
      | IDENT "Section"; s = global -> PrintSectionContext s
      | IDENT "Grammar"; uni = IDENT; ent = IDENT ->
          (* This should be in "syntax" section but is here for factorization*)
	  PrintGrammar (uni, ent)
      | IDENT "LoadPath" -> PrintLoadPath
      | IDENT "Modules" -> PrintModules

      | IDENT "ML"; IDENT "Path" -> PrintMLLoadPath
      | IDENT "ML"; IDENT "Modules" -> PrintMLModules
      | IDENT "Graph" -> PrintGraph
      | IDENT "Classes" ->  PrintClasses
      | IDENT "Coercions" -> PrintCoercions
      | IDENT "Coercion"; IDENT "Paths"; s = class_rawexpr; t = class_rawexpr
         -> PrintCoercionPaths (s,t)
      | IDENT "Tables" -> PrintTables
      | IDENT "Proof"; qid = global -> PrintOpaqueName qid
      | IDENT "Hint" -> PrintHintGoal
      | IDENT "Hint"; qid = global -> PrintHint qid
      | IDENT "Hint"; "*" -> PrintHintDb
      | IDENT "HintDb"; s = IDENT -> PrintHintDbName s
      | IDENT "Scope"; s = IDENT -> PrintScope s ] ]
  ;
  class_rawexpr:
    [ [ IDENT "FUNCLASS" -> FunClass
      | IDENT "SORTCLASS" -> SortClass
      | qid = global -> RefClass qid ] ]
  ;
  locatable:
    [ [ qid = global -> LocateTerm qid
      | IDENT "File"; f = STRING -> LocateFile f
      | IDENT "Library"; qid = global -> LocateLibrary  qid
      | s = STRING -> LocateNotation s ] ]
  ;
  option_value:
    [ [ n  = integer   -> IntValue n
      | s  = STRING    -> StringValue s ] ]
  ;
  option_ref_value:
    [ [ id = global   -> QualidRefValue id
      | s  = STRING   -> StringRefValue s ] ]
  ;
  as_dirpath:
    [ [ d = OPT [ "as"; d = dirpath -> d ] -> d ] ]
  ;
  in_or_out_modules:
    [ [ IDENT "inside"; l = LIST1 global -> SearchInside l
      | IDENT "outside"; l = LIST1 global -> SearchOutside l
      | -> SearchOutside [] ] ]
  ;
  comment:
    [ [ c = constr -> CommentConstr c
      | s = STRING -> CommentString s
      | n = natural -> CommentInt n ] ]
  ;
END;

GEXTEND Gram
  command:
    [ [ 
(* State management *)
        IDENT "Write"; IDENT "State"; s = IDENT -> VernacWriteState s
      | IDENT "Write"; IDENT "State"; s = STRING -> VernacWriteState s
      | IDENT "Restore"; IDENT "State"; s = IDENT -> VernacRestoreState s
      | IDENT "Restore"; IDENT "State"; s = STRING -> VernacRestoreState s

(* Resetting *)
      | IDENT "Reset"; id = identref -> VernacResetName id
      | IDENT "Reset"; IDENT "Initial" -> VernacResetInitial
      | IDENT "Back" -> VernacBack 1
      | IDENT "Back"; n = natural -> VernacBack n

(* Tactic Debugger *)
      |	IDENT "Debug"; IDENT "On" -> VernacDebug true
      |	IDENT "Debug"; IDENT "Off" -> VernacDebug false

 ] ];
    END
;;

(* Grammar extensions *)
	  
GEXTEND Gram
  GLOBAL: syntax;

  syntax:
   [ [ IDENT "Open"; IDENT "Scope"; sc = IDENT -> VernacOpenScope sc

     | IDENT "Delimits"; IDENT "Scope"; sc = IDENT; "with"; key = IDENT ->
	 VernacDelimiters (sc,key)

     | IDENT "Arguments"; IDENT "Scope"; qid = global;
         "["; scl = LIST0 opt_scope; "]" -> VernacArgumentsScope (qid,scl)

     | IDENT "Infix"; a = entry_prec; n = OPT natural; op = STRING; 
         p = global;
         modl = [ "("; l = LIST1 syntax_modifier SEP ","; ")" -> l | -> [] ];
	 sc = OPT [ ":"; sc = IDENT -> sc ] ->
         let (a,n,b) = Metasyntax.interp_infix_modifiers a n modl in
         VernacInfix (a,n,op,p,b,None,sc)
     | IDENT "Notation"; s = IDENT; ":="; c = constr ->
	 VernacNotation ("'"^s^"'",c,[],None,None)
     | IDENT "Notation"; s = STRING; ":="; c = constr;
         modl = [ "("; l = LIST1 syntax_modifier SEP ","; ")" -> l | -> [] ];
	 sc = OPT [ ":"; sc = IDENT -> sc ] ->
           VernacNotation (s,c,modl,None,sc)

     | IDENT "Grammar"; IDENT "tactic"; IDENT "simple_tactic";
        OPT [ ":"; IDENT "tactic" ]; ":=";
        OPT "|"; tl = LIST0 grammar_tactic_rule SEP "|" -> 
	  VernacTacticGrammar tl

     | IDENT "Grammar"; u = univ;
         tl = LIST1 grammar_entry SEP "with" -> 
	   VernacGrammar (rename_command_entry u,tl)

     | IDENT "Syntax"; u = univ; el = LIST1 syntax_entry SEP "," ->
         VernacSyntax (u,el)

     | IDENT "Uninterpreted"; IDENT "Notation"; s = STRING; 
	 l = [ "("; l = LIST1 syntax_modifier SEP ","; ")" -> l | -> [] ]
	 -> VernacSyntaxExtension (s,l)

     (* "Print" "Grammar" should be here but is in "command" entry in order 
        to factorize with other "Print"-based vernac entries *)
  ] ]
  ;
  univ:
  [ [ univ = IDENT ->
        set_default_action_parser (parser_type_from_name univ); univ ] ]
  ;
  syntax_modifier:
    [ [ x = IDENT; IDENT "at"; IDENT "level"; n = natural -> 
        SetItemLevel ([x],n)
      | x = IDENT; ","; l = LIST1 IDENT SEP ","; IDENT "at"; IDENT "level";
        n = natural -> SetItemLevel (x::l,n)
      | IDENT "at"; IDENT "level"; n = natural -> SetLevel n
      | IDENT "left"; IDENT "associativity" -> SetAssoc Gramext.LeftA
      | IDENT "right"; IDENT "associativity" -> SetAssoc Gramext.RightA
      | IDENT "no"; IDENT "associativity" -> SetAssoc Gramext.NonA
      | x = IDENT; typ = syntax_extension_type -> SetEntryType (x,typ)
      | IDENT "only"; IDENT "parsing" -> SetOnlyParsing ] ]
  ;
  syntax_extension_type:
    [ [ IDENT "ident" -> ETIdent | IDENT "global" -> ETReference
      | IDENT "bigint" -> ETBigint
      | e=IDENT -> ETOther("constr",e)
    ] ]
  ;
  opt_scope:
    [ [ IDENT "_" -> None | sc = IDENT -> Some sc ] ]
  ;
  (* Syntax entries for Grammar. Only grammar_entry is exported *)
  grammar_entry:
    [[ nont = IDENT; set_entry_type; ":=";
       ep = entry_prec; OPT "|"; rl = LIST0 grammar_rule SEP "|" ->
	 (rename_command_entry nont,ep,rl) ]]
  ;
  entry_prec:
    [[ IDENT "LEFTA" -> Some Gramext.LeftA
     | IDENT "RIGHTA" -> Some Gramext.RightA
     | IDENT "NONA" -> Some Gramext.NonA
     | -> None ]]
  ;
  grammar_tactic_rule:
    [[ name = rule_name; "["; s = STRING; pil = LIST0 production_item; "]";
       "->"; "["; t = Tactic.tactic; "]"  -> (name, (s,pil), t) ]]
  ;
  grammar_rule:
    [[ name = rule_name; "["; pil = LIST0 production_item; "]"; "->";
       a = action -> (name, pil, a) ]]
  ;
  rule_name:
    [[ name = IDENT -> name ]]
  ;
  production_item:
    [[ s = STRING -> VTerm s
     | nt = non_terminal; po = OPT [ "("; p = METAIDENT; ")" -> p ] ->
         match po with
           | Some p -> VNonTerm (loc,nt,Some (Names.id_of_string p))
           | _ -> VNonTerm (loc,nt,None) ]]
  ;
  non_terminal:
    [[ u = IDENT; ":"; nt = IDENT ->
        NtQual(rename_command_entry u, rename_command_entry nt)
     | nt = IDENT -> NtShort (rename_command_entry nt) ]]
  ;


  (* Syntax entries for Syntax. Only syntax_entry is exported *)
  syntax_entry:
    [ [ IDENT "level"; p = precedence; ":";
	OPT "|"; rl = LIST1 syntax_rule SEP "|" -> (p,rl) ] ]
  ;
  syntax_rule:
    [ [ nm = IDENT; "["; s = astpat; "]"; "->"; u = unparsing -> (nm,s,u) ] ]
  ;
  precedence:
    [ [ a = natural -> a
(*      | "["; a1 = natural; a2 = natural; a3 = natural; "]" -> (a1,a2,a3)*)
    ] ]
  ;
  unparsing:
    [ [ "["; ll = LIST0 next_hunks; "]" -> ll ] ]
  ;
  next_hunks:
    [ [ IDENT "FNL" -> UNP_FNL
      | IDENT "TAB" -> UNP_TAB
      | c = STRING -> RO c
      | "[";
        x =
          [ b = box; ll = LIST0 next_hunks -> UNP_BOX (b,ll)
          | n = natural; m = natural -> UNP_BRK (n, m)
          | IDENT "TBRK"; n = natural; m = natural -> UNP_TBRK (n, m) ];
        "]" -> x
      | e = Prim.ast; oprec = OPT [ ":"; pr = paren_reln_or_extern -> pr ] ->
          match oprec with
	    | Some (ext,pr) -> PH (e,ext,pr)
            | None -> PH (e,None,Any)
 ]]
  ;
  box:
    [ [ "<"; bk = box_kind; ">" -> bk ] ]
  ;
  box_kind:
    [ [ IDENT "h"; n = natural -> PpHB n
      | IDENT "v"; n = natural -> PpVB n
      | IDENT "hv"; n = natural -> PpHVB n
      | IDENT "hov"; n = natural -> PpHOVB n
      | IDENT "t" -> PpTB ] ]
  ;
  paren_reln_or_extern:
    [ [ IDENT "L" -> None, L
      | IDENT "E" -> None, E
      | pprim = STRING; precrec = OPT [ ":"; p = precedence -> p ] ->
	  match precrec with
	    | Some p -> Some pprim, Prec p
            | None -> Some pprim, Any ] ]
  ;
  (* meta-syntax entries *)
  astpat:
    [ [ "<<" ; a = Prim.ast; ">>" -> a 
      | a = Constr.lconstr -> 
	  Termast.ast_of_rawconstr 
	  (Constrintern.interp_rawconstr Evd.empty (Global.env()) a)
    ] ]
  ; 
  action:
    [ [ IDENT "let"; p = Prim.astlist; et = set_internal_entry_type;
        "="; e1 = action; "in"; e = action -> Ast.CaseAction (loc,e1,et,[p,e])
      | IDENT "case"; a = action; et = set_internal_entry_type; "of";
        cl = LIST1 case SEP "|"; IDENT "esac" -> Ast.CaseAction (loc,a,et,cl)
      | "["; a = default_action_parser; "]" -> Ast.SimpleAction (loc,a) ] ]
  ;
  case:
    [[ p = Prim.astlist; "->"; a = action -> (p,a) ]]
  ;
  set_internal_entry_type:
    [[ ":"; IDENT "ast"; IDENT "list" -> Ast.ETastl
     | [ ":"; IDENT "ast" -> () | -> () ] -> Ast.ETast ]]
  ;
  set_entry_type:
    [[ ":"; et = entry_type -> set_default_action_parser et
     | -> () ]]
  ;
  entry_type:
    [[ IDENT "ast"; IDENT "list" -> Util.error "type ast list no longer supported"
     | IDENT "ast" -> Util.error "type ast no longer supported"
     | IDENT "constr" -> ConstrParser
     | IDENT "pattern" -> CasesPatternParser
     | IDENT "tactic" -> assert false
     | IDENT "vernac" -> Util.error "vernac extensions no longer supported" ] ]
  ;
END

(* Reinstall tactic and vernac extensions *)
let _ = Egrammar.reset_extend_grammars_v8()
