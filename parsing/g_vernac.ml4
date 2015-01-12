(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Compat
open Errors
open Util
open Names
open Constrexpr
open Constrexpr_ops
open Extend
open Vernacexpr
open Decl_kinds
open Misctypes
open Tok (* necessary for camlp4 *)

open Pcoq
open Pcoq.Tactic
open Pcoq.Prim
open Pcoq.Constr
open Pcoq.Vernac_
open Pcoq.Module

let vernac_kw = [ ";"; ","; ">->"; ":<"; "<:"; "where"; "at" ]
let _ = List.iter Lexer.add_keyword vernac_kw

(* Rem: do not join the different GEXTEND into one, it breaks native *)
(* compilation on PowerPC and Sun architectures *)

let query_command = Gram.entry_create "vernac:query_command"

let tactic_mode = Gram.entry_create "vernac:tactic_command"
let noedit_mode = Gram.entry_create "vernac:noedit_command"
let subprf = Gram.entry_create "vernac:subprf"

let class_rawexpr = Gram.entry_create "vernac:class_rawexpr"
let thm_token = Gram.entry_create "vernac:thm_token"
let def_body = Gram.entry_create "vernac:def_body"
let decl_notation = Gram.entry_create "vernac:decl_notation"
let record_field = Gram.entry_create "vernac:record_field"
let of_type_with_opt_coercion = Gram.entry_create "vernac:of_type_with_opt_coercion"
let subgoal_command = Gram.entry_create "proof_mode:subgoal_command"
let instance_name = Gram.entry_create "vernac:instance_name"
let section_subset_descr = Gram.entry_create "vernac:section_subset_descr"

let command_entry = ref noedit_mode
let set_command_entry e = command_entry := e
let get_command_entry () = !command_entry


(* Registers the Classic Proof Mode (which uses [tactic_mode] as a parser for
    proof editing and changes nothing else). Then sets it as the default proof mode. *)
let set_tactic_mode () = set_command_entry tactic_mode
let set_noedit_mode () = set_command_entry noedit_mode
let _ = Proof_global.register_proof_mode {Proof_global.
					    name = "Classic" ;
					    set = set_tactic_mode ;
					    reset = set_noedit_mode
					 }

let make_bullet s =
  let n = String.length s in
  match s.[0] with
  | '-' -> Dash n
  | '+' -> Plus n
  | '*' -> Star n
  | _ -> assert false

let default_command_entry =
  Gram.Entry.of_parser "command_entry"
    (fun strm -> Gram.parse_tokens_after_filter (get_command_entry ()) strm)

GEXTEND Gram
  GLOBAL: vernac gallina_ext tactic_mode noedit_mode subprf subgoal_command;
  vernac: FIRST
    [ [ IDENT "Time"; l = vernac_list -> VernacTime l
      | IDENT "Timeout"; n = natural; v = vernac -> VernacTimeout(n,v)
      | IDENT "Fail"; v = vernac -> VernacFail v

      | IDENT "Local"; v = vernac_poly -> VernacLocal (true, v)
      | IDENT "Global"; v = vernac_poly -> VernacLocal (false, v)

      (* Stm backdoor *)
      | IDENT "Stm"; IDENT "JoinDocument"; "." -> VernacStm JoinDocument
      | IDENT "Stm"; IDENT "Finish"; "." -> VernacStm Finish
      | IDENT "Stm"; IDENT "Wait"; "." -> VernacStm Wait
      | IDENT "Stm"; IDENT "PrintDag"; "." -> VernacStm PrintDag
      | IDENT "Stm"; IDENT "Observe"; id = INT; "." ->
          VernacStm (Observe (Stateid.of_int (int_of_string id)))
      | IDENT "Stm"; IDENT "Command"; v = vernac_aux -> VernacStm (Command v)
      | IDENT "Stm"; IDENT "PGLast"; v = vernac_aux -> VernacStm (PGLast v)

      | v = vernac_poly -> v ] 
    ]
  ;
  vernac_poly: 
    [ [ IDENT "Polymorphic"; v = vernac_aux -> VernacPolymorphic (true, v)
      | IDENT "Monomorphic"; v = vernac_aux -> VernacPolymorphic (false, v) 
      | v = vernac_aux -> v ]
    ]
  ;
  vernac_aux:
    (* Better to parse "." here: in case of failure (e.g. in coerce_to_var), *)
    (* "." is still in the stream and discard_to_dot works correctly         *)
    [ [ IDENT "Program"; g = gallina; "." -> VernacProgram g
      | IDENT "Program"; g = gallina_ext; "." -> VernacProgram g
      | g = gallina; "." -> g
      | g = gallina_ext; "." -> g
      | c = command; "." -> c
      | c = syntax; "." -> c
      | c = subprf -> c
    ] ]
  ;
  vernac_list:
    [ [ c = located_vernac -> [c] ] ]
  ;
  vernac_aux: LAST
    [ [ prfcom = default_command_entry -> prfcom ] ]
  ;
  noedit_mode:
    [ [ c = subgoal_command -> c None] ]
  ;

  selector:
    [ [ n=natural; ":" -> SelectNth n
      | "["; id = ident; "]"; ":" -> SelectId id
      | IDENT "all" ; ":" -> SelectAll
      | IDENT "par" ; ":" -> SelectAllParallel ] ]
  ;

  tactic_mode:
  [ [ gln = OPT selector;
      tac = subgoal_command -> tac gln ] ]
  ;

  subprf:
  [ [ s = BULLET -> VernacBullet (make_bullet s)
    | "{" -> VernacSubproof None
    | "}" -> VernacEndSubproof
    ] ]
  ;

  subgoal_command: 
    [ [ c = query_command; "." ->
                  begin function
                    | Some (SelectNth g) -> c (Some g)
                    | None -> c None
                    | _ ->
                        VernacError (UserError ("",str"Typing and evaluation commands, cannot be used with the \"all:\" selector."))
                  end
      | info = OPT [IDENT "Info";n=natural -> n];
        tac = Tactic.tactic;
        use_dft_tac = [ "." -> false | "..." -> true ] ->
        (fun g ->
            let g = Option.default (Proof_global.get_default_goal_selector ()) g in
            VernacSolve(g,info,tac,use_dft_tac)) ] ]
  ;
  located_vernac:
    [ [ v = vernac -> !@loc, v ] ]
  ;
END

let test_plurial_form = function
  | [(_,([_],_))] ->
      Flags.if_verbose msg_warning
   (strbrk "Keywords Variables/Hypotheses/Parameters expect more than one assumption")
  | _ -> ()

let test_plurial_form_types = function
  | [([_],_)] ->
      Flags.if_verbose msg_warning
   (strbrk "Keywords Implicit Types expect more than one type")
  | _ -> ()

(* Gallina declarations *)
GEXTEND Gram
  GLOBAL: gallina gallina_ext thm_token def_body of_type_with_opt_coercion
    record_field decl_notation rec_definition;

  gallina:
      (* Definition, Theorem, Variable, Axiom, ... *)
    [ [ thm = thm_token; id = identref; bl = binders; ":"; c = lconstr;
        l = LIST0
          [ "with"; id = identref; bl = binders; ":"; c = lconstr ->
          (Some id,(bl,c,None)) ] ->
          VernacStartTheoremProof (thm, (Some id,(bl,c,None))::l, false)
      | stre = assumption_token; nl = inline; bl = assum_list ->
	  VernacAssumption (stre, nl, bl)
      | stre = assumptions_token; nl = inline; bl = assum_list ->
	  test_plurial_form bl;
	  VernacAssumption (stre, nl, bl)
      | d = def_token; id = identref; b = def_body ->
          VernacDefinition (d, id, b)
      | IDENT "Let"; id = identref; b = def_body ->
          VernacDefinition ((Some Discharge, Definition), id, b)
      (* Gallina inductive declarations *)
      | priv = private_token; f = finite_token;
        indl = LIST1 inductive_definition SEP "with" ->
	  let (k,f) = f in
	  let indl=List.map (fun ((a,b,c,d),e) -> ((a,b,c,k,d),e)) indl in
          VernacInductive (priv,f,indl)
      | "Fixpoint"; recs = LIST1 rec_definition SEP "with" ->
          VernacFixpoint (None, recs)
      | IDENT "Let"; "Fixpoint"; recs = LIST1 rec_definition SEP "with" ->
          VernacFixpoint (Some Discharge, recs)
      | "CoFixpoint"; corecs = LIST1 corec_definition SEP "with" ->
          VernacCoFixpoint (None, corecs)
      | IDENT "Let"; "CoFixpoint"; corecs = LIST1 corec_definition SEP "with" ->
          VernacCoFixpoint (Some Discharge, corecs)
      | IDENT "Scheme"; l = LIST1 scheme SEP "with" -> VernacScheme l
      | IDENT "Combined"; IDENT "Scheme"; id = identref; IDENT "from";
	      l = LIST1 identref SEP "," -> VernacCombinedScheme (id, l)
      | IDENT "Register"; IDENT "Inline"; id = identref ->
          VernacRegister(id, RegisterInline)
      | IDENT "Universe"; l = LIST1 identref -> VernacUniverse l
      | IDENT "Universes"; l = LIST1 identref -> VernacUniverse l
      | IDENT "Constraint"; l = LIST1 univ_constraint SEP "," -> VernacConstraint l
  ] ]
  ;

  thm_token:
    [ [ "Theorem" -> Theorem
      | IDENT "Lemma" -> Lemma
      | IDENT "Fact" -> Fact
      | IDENT "Remark" -> Remark
      | IDENT "Corollary" -> Corollary
      | IDENT "Proposition" -> Proposition
      | IDENT "Property" -> Property ] ]
  ;
  def_token:
    [ [ "Definition" -> (None, Definition)
      | IDENT "Example" -> (None, Example)
      | IDENT "SubClass" -> (None, SubClass) ] ]
  ;
  assumption_token:
    [ [ "Hypothesis" -> (Some Discharge, Logical)
      | "Variable" -> (Some Discharge, Definitional)
      | "Axiom" -> (None, Logical)
      | "Parameter" -> (None, Definitional)
      | IDENT "Conjecture" -> (None, Conjectural) ] ]
  ;
  assumptions_token:
    [ [ IDENT "Hypotheses" -> (Some Discharge, Logical)
      | IDENT "Variables" -> (Some Discharge, Definitional)
      | IDENT "Axioms" -> (None, Logical)
      | IDENT "Parameters" -> (None, Definitional) ] ]
  ;
  inline:
    [ [ IDENT "Inline"; "("; i = INT; ")" -> InlineAt (int_of_string i)
      | IDENT "Inline" -> DefaultInline
      | -> NoInline] ]
  ;
  univ_constraint:
    [ [ l = identref; ord = [ "<" -> Univ.Lt | "=" -> Univ.Eq | "<=" -> Univ.Le ];
	r = identref -> (l, ord, r) ] ]
  ;
  finite_token:
    [ [ "Inductive" -> (Inductive_kw,Finite)
      | "CoInductive" -> (CoInductive,CoFinite)
      | "Variant" -> (Variant,BiFinite)
      | IDENT "Record" -> (Record,BiFinite)
      | IDENT "Structure" -> (Structure,BiFinite)
      | IDENT "Class" -> (Class true,BiFinite) ] ]
  ;
  private_token:
    [ [ IDENT "Private" -> true | -> false ] ]
  ;
  (* Simple definitions *)
  def_body:
    [ [ bl = binders; ":="; red = reduce; c = lconstr ->
      (match c with
          CCast(_,c, CastConv t) -> DefineBody (bl, red, c, Some t)
        | _ -> DefineBody (bl, red, c, None))
    | bl = binders; ":"; t = lconstr; ":="; red = reduce; c = lconstr ->
	DefineBody (bl, red, c, Some t)
    | bl = binders; ":"; t = lconstr ->
        ProveBody (bl, t) ] ]
  ;
  reduce:
    [ [ IDENT "Eval"; r = Tactic.red_expr; "in" -> Some r
      | -> None ] ]
  ;
  one_decl_notation:
    [ [ ntn = ne_lstring; ":="; c = constr;
        scopt = OPT [ ":"; sc = IDENT -> sc] -> (ntn,c,scopt) ] ]
  ;
  decl_notation:
    [ [ "where"; l = LIST1 one_decl_notation SEP IDENT "and" -> l
    | -> [] ] ]
  ;
  (* Inductives and records *)
  opt_constructors_or_fields:
    [ [ ":="; lc = constructor_list_or_record_decl -> lc
      | -> RecordDecl (None, []) ] ]
  ;
  inductive_definition:
    [ [ oc = opt_coercion; id = identref; indpar = binders;
        c = OPT [ ":"; c = lconstr -> c ];
        lc=opt_constructors_or_fields; ntn = decl_notation ->
	   (((oc,id),indpar,c,lc),ntn) ] ]
  ;
  constructor_list_or_record_decl:
    [ [ "|"; l = LIST1 constructor SEP "|" -> Constructors l
      | id = identref ; c = constructor_type; "|"; l = LIST0 constructor SEP "|" ->
	  Constructors ((c id)::l)
      | id = identref ; c = constructor_type -> Constructors [ c id ]
      | cstr = identref; "{"; fs = LIST0 record_field SEP ";"; "}" ->
	  RecordDecl (Some cstr,fs)
      | "{";fs = LIST0 record_field SEP ";"; "}" -> RecordDecl (None,fs)
      |  -> Constructors [] ] ]
  ;
(*
  csort:
    [ [ s = sort -> CSort (loc,s) ] ]
  ;
*)
  opt_coercion:
    [ [ ">" -> true
      |  -> false ] ]
  ;
  (* (co)-fixpoints *)
  rec_definition:
    [ [ id = identref;
	bl = binders_fixannot;
        ty = type_cstr;
	def = OPT [":="; def = lconstr -> def]; ntn = decl_notation ->
	  let bl, annot = bl in ((id,annot,bl,ty,def),ntn) ] ]
  ;
  corec_definition:
    [ [ id = identref; bl = binders; ty = type_cstr;
        def = OPT [":="; def = lconstr -> def]; ntn = decl_notation ->
          ((id,bl,ty,def),ntn) ] ]
  ;
  type_cstr:
    [ [ ":"; c=lconstr -> c
      | -> CHole (!@loc, None, Misctypes.IntroAnonymous, None) ] ]
  ;
  (* Inductive schemes *)
  scheme:
    [ [ kind = scheme_kind -> (None,kind)
      | id = identref; ":="; kind = scheme_kind -> (Some id,kind) ] ]
  ;
  scheme_kind:
    [ [ IDENT "Induction"; "for"; ind = smart_global;
          IDENT "Sort"; s = sort-> InductionScheme(true,ind,s)
      | IDENT "Minimality"; "for"; ind = smart_global;
          IDENT "Sort"; s = sort-> InductionScheme(false,ind,s)
      | IDENT "Elimination"; "for"; ind = smart_global;
          IDENT "Sort"; s = sort-> CaseScheme(true,ind,s)
      | IDENT "Case"; "for"; ind = smart_global;
          IDENT "Sort"; s = sort-> CaseScheme(false,ind,s)
      | IDENT "Equality"; "for" ; ind = smart_global -> EqualityScheme(ind) ] ]
  ;
  (* Various Binders *)
(*
  (* ... without coercions *)
  binder_nodef:
    [ [ b = binder_let ->
      (match b with
          LocalRawAssum(l,ty) -> (l,ty)
        | LocalRawDef _ ->
            Util.user_err_loc
              (loc,"fix_param",Pp.str"defined binder not allowed here.")) ] ]
  ;
*)
  (* ... with coercions *)
  record_field:
  [ [ bd = record_binder; pri = OPT [ "|"; n = natural -> n ];
      ntn = decl_notation -> (bd,pri),ntn ] ]
  ;
  record_binder_body:
    [ [ l = binders; oc = of_type_with_opt_coercion;
         t = lconstr -> fun id -> (oc,AssumExpr (id,mkCProdN (!@loc) l t))
      | l = binders; oc = of_type_with_opt_coercion;
         t = lconstr; ":="; b = lconstr -> fun id ->
	   (oc,DefExpr (id,mkCLambdaN (!@loc) l b,Some (mkCProdN (!@loc) l t)))
      | l = binders; ":="; b = lconstr -> fun id ->
         match b with
	 | CCast(_,b, (CastConv t|CastVM t|CastNative t)) ->
	     (None,DefExpr(id,mkCLambdaN (!@loc) l b,Some (mkCProdN (!@loc) l t)))
         | _ ->
	     (None,DefExpr(id,mkCLambdaN (!@loc) l b,None)) ] ]
  ;
  record_binder:
    [ [ id = name -> (None,AssumExpr(id,CHole (!@loc, None, Misctypes.IntroAnonymous, None)))
      | id = name; f = record_binder_body -> f id ] ]
  ;
  assum_list:
    [ [ bl = LIST1 assum_coe -> bl | b = simple_assum_coe -> [b] ] ]
  ;
  assum_coe:
    [ [ "("; a = simple_assum_coe; ")" -> a ] ]
  ;
  simple_assum_coe:
    [ [ idl = LIST1 identref; oc = of_type_with_opt_coercion; c = lconstr ->
        (not (Option.is_empty oc),(idl,c)) ] ]
  ;

  constructor_type:
    [[ l = binders;
      t= [ coe = of_type_with_opt_coercion; c = lconstr ->
	            fun l id -> (not (Option.is_empty coe),(id,mkCProdN (!@loc) l c))
            |  ->
		 fun l id -> (false,(id,mkCProdN (!@loc) l (CHole (!@loc, None, Misctypes.IntroAnonymous, None)))) ]
	 -> t l
     ]]
;

  constructor:
    [ [ id = identref; c=constructor_type -> c id ] ]
  ;
  of_type_with_opt_coercion:
    [ [ ":>>" -> Some false
	| ":>"; ">" -> Some false
	| ":>" -> Some true
	| ":"; ">"; ">" -> Some false
	| ":"; ">" -> Some true
	| ":" -> None ] ]
  ;
END

let only_identrefs =
  Gram.Entry.of_parser "test_only_identrefs"
    (fun strm ->
      let rec aux n =
      match get_tok (Util.stream_nth n strm) with
        | KEYWORD "." -> ()
        | KEYWORD ")" -> ()
        | IDENT _ -> aux (n+1)
        | _ -> raise Stream.Failure in
      aux 0)

(* Modules and Sections *)
GEXTEND Gram
  GLOBAL: gallina_ext module_expr module_type section_subset_descr;

  gallina_ext:
    [ [ (* Interactive module declaration *)
        IDENT "Module"; export = export_token; id = identref;
	bl = LIST0 module_binder; sign = of_module_type;
	body = is_module_expr ->
	  VernacDefineModule (export, id, bl, sign, body)
      | IDENT "Module"; "Type"; id = identref;
	bl = LIST0 module_binder; sign = check_module_types;
	body = is_module_type ->
	  VernacDeclareModuleType (id, bl, sign, body)
      | IDENT "Declare"; IDENT "Module"; export = export_token; id = identref;
	bl = LIST0 module_binder; ":"; mty = module_type_inl ->
	  VernacDeclareModule (export, id, bl, mty)
      (* Section beginning *)
      | IDENT "Section"; id = identref -> VernacBeginSection id
      | IDENT "Chapter"; id = identref -> VernacBeginSection id

      (* This end a Section a Module or a Module Type *)
      | IDENT "End"; id = identref -> VernacEndSegment id

      (* Naming a set of section hyps *)
      | IDENT "Collection"; id = identref; ":="; expr = section_subset_descr ->
          VernacNameSectionHypSet (id, expr)

      (* Requiring an already compiled module *)
      | IDENT "Require"; export = export_token; qidl = LIST1 global ->
          VernacRequire (export, qidl)
      | IDENT "From" ; ns = global ; IDENT "Require"; export = export_token
	; qidl = LIST1 global ->
	let qidl = List.map (Libnames.join_reference ns) qidl in
	VernacRequire (export, qidl)
      | IDENT "Import"; qidl = LIST1 global -> VernacImport (false,qidl)
      | IDENT "Export"; qidl = LIST1 global -> VernacImport (true,qidl)
      | IDENT "Include"; e = module_type_inl; l = LIST0 ext_module_expr ->
	  VernacInclude(e::l)
      | IDENT "Include"; "Type"; e = module_type_inl; l = LIST0 ext_module_type ->
	  Flags.if_verbose
            msg_warning (strbrk "Include Type is deprecated; use Include instead");
          VernacInclude(e::l) ] ]
  ;
  export_token:
    [ [ IDENT "Import" -> Some false
      | IDENT "Export" -> Some true
      |  -> None ] ]
  ;
  ext_module_type:
    [ [ "<+"; mty = module_type_inl -> mty ] ]
  ;
  ext_module_expr:
    [ [ "<+"; mexpr = module_expr_inl -> mexpr ] ]
  ;
  check_module_type:
    [ [ "<:"; mty = module_type_inl -> mty ] ]
  ;
  check_module_types:
    [ [ mtys = LIST0 check_module_type -> mtys ] ]
  ;
  of_module_type:
    [ [ ":"; mty = module_type_inl -> Enforce mty
      | mtys = check_module_types -> Check mtys ] ]
  ;
  is_module_type:
    [ [ ":="; mty = module_type_inl ; l = LIST0 ext_module_type -> (mty::l)
      | -> [] ] ]
  ;
  is_module_expr:
    [ [ ":="; mexpr = module_expr_inl; l = LIST0 ext_module_expr -> (mexpr::l)
      | -> [] ] ]
  ;
  functor_app_annot:
    [ [ "["; IDENT "inline"; "at"; IDENT "level"; i = INT; "]" ->
        InlineAt (int_of_string i)
      | "["; IDENT "no"; IDENT "inline"; "]" -> NoInline
      | -> DefaultInline
      ] ]
  ;
  module_expr_inl:
    [ [ "!"; me = module_expr -> (me,NoInline)
      | me = module_expr; a = functor_app_annot -> (me,a) ] ]
  ;
  module_type_inl:
    [ [ "!"; me = module_type -> (me,NoInline)
      | me = module_type; a = functor_app_annot -> (me,a) ] ]
  ;
  (* Module binder  *)
  module_binder:
    [ [ "("; export = export_token; idl = LIST1 identref; ":";
         mty = module_type_inl; ")" -> (export,idl,mty) ] ]
  ;
  (* Module expressions *)
  module_expr:
    [ [ me = module_expr_atom -> me
      | me1 = module_expr; me2 = module_expr_atom -> CMapply (!@loc,me1,me2)
      ] ]
  ;
  module_expr_atom:
    [ [ qid = qualid -> CMident qid | "("; me = module_expr; ")" -> me ] ]
  ;
  with_declaration:
    [ [ "Definition"; fqid = fullyqualid; ":="; c = Constr.lconstr ->
          CWith_Definition (fqid,c)
      | IDENT "Module"; fqid = fullyqualid; ":="; qid = qualid ->
	  CWith_Module (fqid,qid)
      ] ]
  ;
  module_type:
    [ [ qid = qualid -> CMident qid
      | "("; mt = module_type; ")" -> mt
      | mty = module_type; me = module_expr_atom -> CMapply (!@loc,mty,me)
      | mty = module_type; "with"; decl = with_declaration ->
          CMwith (!@loc,mty,decl)
      ] ]
  ;
  section_subset_descr:
    [ [ IDENT "All" -> SsAll
      | "Type" -> SsType
      | only_identrefs; l = LIST0 identref -> SsExpr (SsSet l)
      | e = section_subset_expr -> SsExpr e ] ]
  ;
  section_subset_expr:
    [ "35" 
      [ "-"; e = section_subset_expr -> SsCompl e ]
    | "50"
      [ e1 = section_subset_expr; "-"; e2 = section_subset_expr->SsSubstr(e1,e2)
      | e1 = section_subset_expr; "+"; e2 = section_subset_expr->SsUnion(e1,e2)]
    | "0"
      [ i = identref -> SsSet [i]
      | "("; only_identrefs; l = LIST0 identref; ")"-> SsSet l
      | "("; e = section_subset_expr; ")"-> e ] ]
  ;
END

(* Extensions: implicits, coercions, etc. *)
GEXTEND Gram
  GLOBAL: gallina_ext instance_name;

  gallina_ext:
    [ [ (* Transparent and Opaque *)
        IDENT "Transparent"; l = LIST1 smart_global ->
          VernacSetOpacity (Conv_oracle.transparent, l)
      | IDENT "Opaque"; l = LIST1 smart_global ->
          VernacSetOpacity (Conv_oracle.Opaque, l)
      | IDENT "Strategy"; l =
          LIST1 [ v=strategy_level; "["; q=LIST1 smart_global; "]" -> (v,q)] ->
            VernacSetStrategy l
      (* Canonical structure *)
      | IDENT "Canonical"; IDENT "Structure"; qid = global ->
	  VernacCanonical (AN qid)
      | IDENT "Canonical"; IDENT "Structure"; ntn = by_notation ->
	  VernacCanonical (ByNotation ntn)
      | IDENT "Canonical"; IDENT "Structure"; qid = global;
          d = def_body ->
          let s = coerce_reference_to_id qid in
	  VernacDefinition
	    ((Some Global,CanonicalStructure),(Loc.ghost,s),d)

      (* Coercions *)
      | IDENT "Coercion"; qid = global; d = def_body ->
          let s = coerce_reference_to_id qid in
	  VernacDefinition ((None,Coercion),(Loc.ghost,s),d)
      | IDENT "Coercion"; IDENT "Local"; qid = global; d = def_body ->
           let s = coerce_reference_to_id qid in
	  VernacDefinition ((Some Decl_kinds.Local,Coercion),(Loc.ghost,s),d)
      | IDENT "Identity"; IDENT "Coercion"; IDENT "Local"; f = identref;
         ":"; s = class_rawexpr; ">->"; t = class_rawexpr ->
	   VernacIdentityCoercion (true, f, s, t)
      | IDENT "Identity"; IDENT "Coercion"; f = identref; ":";
         s = class_rawexpr; ">->"; t = class_rawexpr ->
	   VernacIdentityCoercion (false, f, s, t)
      | IDENT "Coercion"; IDENT "Local"; qid = global; ":";
	 s = class_rawexpr; ">->"; t = class_rawexpr ->
	  VernacCoercion (true, AN qid, s, t)
      | IDENT "Coercion"; IDENT "Local"; ntn = by_notation; ":";
	 s = class_rawexpr; ">->"; t = class_rawexpr ->
	  VernacCoercion (true, ByNotation ntn, s, t)
      | IDENT "Coercion"; qid = global; ":"; s = class_rawexpr; ">->";
         t = class_rawexpr ->
	  VernacCoercion (false, AN qid, s, t)
      | IDENT "Coercion"; ntn = by_notation; ":"; s = class_rawexpr; ">->";
         t = class_rawexpr ->
	  VernacCoercion (false, ByNotation ntn, s, t)

      | IDENT "Context"; c = binders ->
	  VernacContext c

      | IDENT "Instance"; namesup = instance_name; ":";
	 expl = [ "!" -> Decl_kinds.Implicit | -> Decl_kinds.Explicit ] ; t = operconstr LEVEL "200";
	 pri = OPT [ "|"; i = natural -> i ] ;
	 props = [ ":="; "{"; r = record_declaration; "}" -> Some (true,r) |
	     ":="; c = lconstr -> Some (false,c) | -> None ] ->
	   VernacInstance (false,snd namesup,(fst namesup,expl,t),props,pri)

      | IDENT "Existing"; IDENT "Instance"; id = global;
          pri = OPT [ "|"; i = natural -> i ] ->
	  VernacDeclareInstances ([id], pri)
      | IDENT "Existing"; IDENT "Instances"; ids = LIST1 global;
          pri = OPT [ "|"; i = natural -> i ] ->
	  VernacDeclareInstances (ids, pri)

      | IDENT "Existing"; IDENT "Class"; is = global -> VernacDeclareClass is

      (* Arguments *)
      | IDENT "Arguments"; qid = smart_global; 
        impl = LIST1 [ l = LIST0
        [ item = argument_spec ->
            let id, r, s = item in [`Id (id,r,s,false,false)]
        | "/" -> [`Slash]
        | "("; items = LIST1 argument_spec; ")"; sc = OPT scope ->
            let f x = match sc, x with
            | None, x -> x | x, None -> Option.map (fun y -> !@loc, y) x
            | Some _, Some _ -> error "scope declared twice" in
            List.map (fun (id,r,s) -> `Id(id,r,f s,false,false)) items
        | "["; items = LIST1 argument_spec; "]"; sc = OPT scope ->
            let f x = match sc, x with
            | None, x -> x | x, None -> Option.map (fun y -> !@loc, y) x
            | Some _, Some _ -> error "scope declared twice" in
            List.map (fun (id,r,s) -> `Id(id,r,f s,true,false)) items
        | "{"; items = LIST1 argument_spec; "}"; sc = OPT scope ->
            let f x = match sc, x with
            | None, x -> x | x, None -> Option.map (fun y -> !@loc, y) x
            | Some _, Some _ -> error "scope declared twice" in
            List.map (fun (id,r,s) -> `Id(id,r,f s,true,true)) items
        ] -> l ] SEP ",";
        mods = OPT [ ":"; l = LIST1 arguments_modifier SEP "," -> l ] ->
         let mods = match mods with None -> [] | Some l -> List.flatten l in
         let impl = List.map List.flatten impl in
         let rec aux n (narg, impl) = function
           | `Id x :: tl -> aux (n+1) (narg, impl@[x]) tl
           | `Slash :: tl -> aux (n+1) (n, impl) tl
           | [] -> narg, impl in
         let nargs, impl = List.split (List.map (aux 0 (-1, [])) impl) in
         let nargs, rest = List.hd nargs, List.tl nargs in
         if List.exists (fun arg -> not (Int.equal arg nargs)) rest then
           error "All arguments lists must have the same length";
         let err_incompat x y =
           error ("Options \""^x^"\" and \""^y^"\" are incompatible") in
         if nargs > 0 && List.mem `ReductionNeverUnfold mods then
           err_incompat "simpl never" "/";
         if List.mem `ReductionNeverUnfold mods &&
            List.mem `ReductionDontExposeCase mods then
           err_incompat "simpl never" "simpl nomatch";
         VernacArguments (qid, impl, nargs, mods)

     (* moved there so that camlp5 factors it with the previous rule *)
     | IDENT "Arguments"; IDENT "Scope"; qid = smart_global;
       "["; scl = LIST0 [ "_" -> None | sc = IDENT -> Some sc ]; "]" ->
        msg_warning (strbrk "Arguments Scope is deprecated; use Arguments instead");
        VernacArgumentsScope (qid,scl)

      (* Implicit *)
      | IDENT "Implicit"; IDENT "Arguments"; qid = smart_global;
	   pos = LIST0 [ "["; l = LIST0 implicit_name; "]" ->
	     List.map (fun (id,b,f) -> (ExplByName id,b,f)) l ] ->
	   Flags.if_verbose
             msg_warning (strbrk "Implicit Arguments is deprecated; use Arguments instead");
	   VernacDeclareImplicits (qid,pos)

      | IDENT "Implicit"; "Type"; bl = reserv_list ->
	   VernacReserve bl

      | IDENT "Implicit"; IDENT "Types"; bl = reserv_list ->
          test_plurial_form_types bl;
           VernacReserve bl

      | IDENT "Generalizable"; 
	   gen = [IDENT "All"; IDENT "Variables" -> Some []
	     | IDENT "No"; IDENT "Variables" -> None
	     | ["Variable" | IDENT "Variables"];
		  idl = LIST1 identref -> Some idl ] ->
	     VernacGeneralizable gen ] ]
  ;
  arguments_modifier:
    [ [ IDENT "simpl"; IDENT "nomatch" -> [`ReductionDontExposeCase]
      | IDENT "simpl"; IDENT "never" -> [`ReductionNeverUnfold]
      | IDENT "default"; IDENT "implicits" -> [`DefaultImplicits]
      | IDENT "clear"; IDENT "implicits" -> [`ClearImplicits]
      | IDENT "clear"; IDENT "scopes" -> [`ClearScopes]
      | IDENT "rename" -> [`Rename]
      | IDENT "assert" -> [`Assert]
      | IDENT "extra"; IDENT "scopes" -> [`ExtraScopes]
      | IDENT "clear"; IDENT "scopes"; IDENT "and"; IDENT "implicits" ->
          [`ClearImplicits; `ClearScopes]
      | IDENT "clear"; IDENT "implicits"; IDENT "and"; IDENT "scopes" ->
          [`ClearImplicits; `ClearScopes]
      ] ]
  ;
  implicit_name:
    [ [ "!"; id = ident -> (id, false, true)
    | id = ident -> (id,false,false)
    | "["; "!"; id = ident; "]" -> (id,true,true)
    | "["; id = ident; "]" -> (id,true, false) ] ]
  ;
  scope:
    [ [ "%"; key = IDENT -> key ] ]
  ;
  argument_spec: [
       [ b = OPT "!"; id = name ; s = OPT scope ->
       snd id, not (Option.is_empty b), Option.map (fun x -> !@loc, x) s
    ]
  ];
  strategy_level:
    [ [ IDENT "expand" -> Conv_oracle.Expand
      | IDENT "opaque" -> Conv_oracle.Opaque
      | n=INT -> Conv_oracle.Level (int_of_string n)
      | "-"; n=INT -> Conv_oracle.Level (- int_of_string n)
      | IDENT "transparent" -> Conv_oracle.transparent ] ]
  ;
  instance_name:
    [ [ name = identref; sup = OPT binders ->
	  (let (loc,id) = name in (loc, Name id)),
          (Option.default [] sup)
      | -> (!@loc, Anonymous), []  ] ]
  ;
  reserv_list:
    [ [ bl = LIST1 reserv_tuple -> bl | b = simple_reserv -> [b] ] ]
  ;
  reserv_tuple:
    [ [ "("; a = simple_reserv; ")" -> a ] ]
  ;
  simple_reserv:
    [ [ idl = LIST1 identref; ":"; c = lconstr -> (idl,c) ] ]
  ;

END

GEXTEND Gram
  GLOBAL: command query_command class_rawexpr;

  command:
    [ [ IDENT "Ltac";
        l = LIST1 tacdef_body SEP "with" ->
          VernacDeclareTacticDefinition (true, l)

      | IDENT "Comments"; l = LIST0 comment -> VernacComments l

      (* Hack! Should be in grammar_ext, but camlp4 factorize badly *)
      | IDENT "Declare"; IDENT "Instance"; namesup = instance_name; ":";
	 expl = [ "!" -> Decl_kinds.Implicit | -> Decl_kinds.Explicit ] ; t = operconstr LEVEL "200";
	 pri = OPT [ "|"; i = natural -> i ] ->
	   VernacInstance (true, snd namesup, (fst namesup, expl, t), None, pri)

      (* System directory *)
      | IDENT "Pwd" -> VernacChdir None
      | IDENT "Cd" -> VernacChdir None
      | IDENT "Cd"; dir = ne_string -> VernacChdir (Some dir)

      (* Toplevel control *)
      | IDENT "Drop" -> VernacToplevelControl Drop
      | IDENT "Quit" -> VernacToplevelControl Quit

      | IDENT "Load"; verbosely = [ IDENT "Verbose" -> true | -> false ];
	s = [ s = ne_string -> s | s = IDENT -> s ] ->
	  VernacLoad (verbosely, s)
      | IDENT "Declare"; IDENT "ML"; IDENT "Module"; l = LIST1 ne_string ->
	  VernacDeclareMLModule l

      | IDENT "Locate"; l = locatable -> VernacLocate l

      (* Managing load paths *)
      | IDENT "Add"; IDENT "LoadPath"; dir = ne_string; alias = as_dirpath ->
	  VernacAddLoadPath (false, dir, alias)
      | IDENT "Add"; IDENT "Rec"; IDENT "LoadPath"; dir = ne_string;
	  alias = as_dirpath -> VernacAddLoadPath (true, dir, alias)
      | IDENT "Remove"; IDENT "LoadPath"; dir = ne_string ->
	  VernacRemoveLoadPath dir

       (* For compatibility *)
      | IDENT "AddPath"; dir = ne_string; "as"; alias = as_dirpath ->
	  VernacAddLoadPath (false, dir, alias)
      | IDENT "AddRecPath"; dir = ne_string; "as"; alias = as_dirpath ->
	  VernacAddLoadPath (true, dir, alias)
      | IDENT "DelPath"; dir = ne_string ->
	  VernacRemoveLoadPath dir

      (* Type-Checking (pas dans le refman) *)
      | "Type"; c = lconstr -> VernacGlobalCheck c

      (* Printing (careful factorization of entries) *)
      | IDENT "Print"; p = printable -> VernacPrint p
      | IDENT "Print"; qid = smart_global -> VernacPrint (PrintName qid)
      | IDENT "Print"; IDENT "Module"; "Type"; qid = global ->
	  VernacPrint (PrintModuleType qid)
      | IDENT "Print"; IDENT "Module"; qid = global ->
	  VernacPrint (PrintModule qid)
      | IDENT "Print"; IDENT "Namespace" ; ns = dirpath ->
          VernacPrint (PrintNamespace ns)
      | IDENT "Inspect"; n = natural -> VernacPrint (PrintInspect n)

      | IDENT "Add"; IDENT "ML"; IDENT "Path"; dir = ne_string ->
	  VernacAddMLPath (false, dir)
      | IDENT "Add"; IDENT "Rec"; IDENT "ML"; IDENT "Path"; dir = ne_string ->
	  VernacAddMLPath (true, dir)

      (* For acting on parameter tables *)
      | "Set"; table = option_table; v = option_value ->
  	  VernacSetOption (table,v)
      | "Set"; table = option_table ->
  	  VernacSetOption (table,BoolValue true)
      | IDENT "Unset"; table = option_table ->
  	  VernacUnsetOption table

      | IDENT "Print"; IDENT "Table"; table = option_table ->
	  VernacPrintOption table

      | IDENT "Add"; table = IDENT; field = IDENT; v = LIST1 option_ref_value
        -> VernacAddOption ([table;field], v)
      (* A global value below will be hidden by a field above! *)
      (* In fact, we give priority to secondary tables *)
      (* No syntax for tertiary tables due to conflict *)
      (* (but they are unused anyway) *)
      | IDENT "Add"; table = IDENT; v = LIST1 option_ref_value ->
          VernacAddOption ([table], v)

      | IDENT "Test"; table = option_table; "for"; v = LIST1 option_ref_value
        -> VernacMemOption (table, v)
      | IDENT "Test"; table = option_table ->
          VernacPrintOption table

      | IDENT "Remove"; table = IDENT; field = IDENT; v= LIST1 option_ref_value
        -> VernacRemoveOption ([table;field], v)
      | IDENT "Remove"; table = IDENT; v = LIST1 option_ref_value ->
	  VernacRemoveOption ([table], v) ]] 
  ;
  query_command: (* TODO: rapprocher Eval et Check *)
    [ [ IDENT "Eval"; r = Tactic.red_expr; "in"; c = lconstr ->
          fun g -> VernacCheckMayEval (Some r, g, c)
      | IDENT "Compute"; c = lconstr ->
	  fun g -> VernacCheckMayEval (Some (Genredexpr.CbvVm None), g, c)
      | IDENT "Check"; c = lconstr ->
	 fun g -> VernacCheckMayEval (None, g, c)
      (* Searching the environment *)
      | IDENT "About"; qid = smart_global ->
	 fun g -> VernacPrint (PrintAbout (qid,g))
      | IDENT "SearchHead"; c = constr_pattern; l = in_or_out_modules ->
	  fun g -> VernacSearch (SearchHead c,g, l)
      | IDENT "SearchPattern"; c = constr_pattern; l = in_or_out_modules ->
	  fun g -> VernacSearch (SearchPattern c,g, l)
      | IDENT "SearchRewrite"; c = constr_pattern; l = in_or_out_modules ->
	  fun g -> VernacSearch (SearchRewrite c,g, l)
      | IDENT "Search"; s = searchabout_query; l = searchabout_queries ->
	  let (sl,m) = l in fun g -> VernacSearch (SearchAbout (s::sl),g, m)
      (* compatibility: SearchAbout *)
      | IDENT "SearchAbout"; s = searchabout_query; l = searchabout_queries ->
	  fun g -> let (sl,m) = l in VernacSearch (SearchAbout (s::sl),g, m)
      (* compatibility: SearchAbout with "[ ... ]" *)
      | IDENT "SearchAbout"; "["; sl = LIST1 searchabout_query; "]";
	  l = in_or_out_modules -> fun g -> VernacSearch (SearchAbout sl,g, l)
      ] ]
  ;
  printable:
    [ [ IDENT "Term"; qid = smart_global -> PrintName qid
      | IDENT "All" -> PrintFullContext
      | IDENT "Section"; s = global -> PrintSectionContext s
      | IDENT "Grammar"; ent = IDENT ->
          (* This should be in "syntax" section but is here for factorization*)
	  PrintGrammar ent
      | IDENT "LoadPath"; dir = OPT dirpath -> PrintLoadPath dir
      | IDENT "Modules" ->
          error "Print Modules is obsolete; use Print Libraries instead"
      | IDENT "Libraries" -> PrintModules

      | IDENT "ML"; IDENT "Path" -> PrintMLLoadPath
      | IDENT "ML"; IDENT "Modules" -> PrintMLModules
      | IDENT "Debug"; IDENT "GC" -> PrintDebugGC
      | IDENT "Graph" -> PrintGraph
      | IDENT "Classes" ->  PrintClasses
      | IDENT "TypeClasses" -> PrintTypeClasses
      | IDENT "Instances"; qid = smart_global -> PrintInstances qid
      | IDENT "Ltac"; qid = global -> PrintLtac qid
      | IDENT "Coercions" -> PrintCoercions
      | IDENT "Coercion"; IDENT "Paths"; s = class_rawexpr; t = class_rawexpr
         -> PrintCoercionPaths (s,t)
      | IDENT "Canonical"; IDENT "Projections" -> PrintCanonicalConversions
      | IDENT "Tables" -> PrintTables
      | IDENT "Options" -> PrintTables (* A Synonymous to Tables *)
      | IDENT "Hint" -> PrintHintGoal
      | IDENT "Hint"; qid = smart_global -> PrintHint qid
      | IDENT "Hint"; "*" -> PrintHintDb
      | IDENT "HintDb"; s = IDENT -> PrintHintDbName s
      | "Rewrite"; IDENT "HintDb"; s = IDENT -> PrintRewriteHintDbName s
      | IDENT "Scopes" -> PrintScopes
      | IDENT "Scope"; s = IDENT -> PrintScope s
      | IDENT "Visibility"; s = OPT [x = IDENT -> x ] -> PrintVisibility s
      | IDENT "Implicit"; qid = smart_global -> PrintImplicit qid
      | IDENT "Universes"; fopt = OPT ne_string -> PrintUniverses (false, fopt)
      | IDENT "Sorted"; IDENT "Universes"; fopt = OPT ne_string -> PrintUniverses (true, fopt)
      | IDENT "Assumptions"; qid = smart_global -> PrintAssumptions (false, false, qid)
      | IDENT "Opaque"; IDENT "Dependencies"; qid = smart_global -> PrintAssumptions (true, false, qid)
      | IDENT "Transparent"; IDENT "Dependencies"; qid = smart_global -> PrintAssumptions (false, true, qid)
      | IDENT "All"; IDENT "Dependencies"; qid = smart_global -> PrintAssumptions (true, true, qid)
      | IDENT "Strategy"; qid = smart_global -> PrintStrategy (Some qid)
      | IDENT "Strategies" -> PrintStrategy None ] ]
  ;
  class_rawexpr:
    [ [ IDENT "Funclass" -> FunClass
      | IDENT "Sortclass" -> SortClass
      | qid = smart_global -> RefClass qid ] ]
  ;
  locatable:
    [ [ qid = smart_global -> LocateAny qid
      | IDENT "Term"; qid = smart_global -> LocateTerm qid
      | IDENT "File"; f = ne_string -> LocateFile f
      | IDENT "Library"; qid = global -> LocateLibrary qid
      | IDENT "Module"; qid = global -> LocateModule qid
      | IDENT "Ltac"; qid = global -> LocateTactic qid ] ]
  ;
  option_value:
    [ [ n  = integer   -> IntValue (Some n)
      | s  = STRING    -> StringValue s ] ]
  ;
  option_ref_value:
    [ [ id = global   -> QualidRefValue id
      | s  = STRING   -> StringRefValue s ] ]
  ;
  option_table:
    [ [ fl = LIST1 [ x = IDENT -> x ] -> fl ]]
  ;
  as_dirpath:
    [ [ d = OPT [ "as"; d = dirpath -> d ] -> d ] ]
  ;
  ne_in_or_out_modules:
    [ [ IDENT "inside"; l = LIST1 global -> SearchInside l
      | IDENT "outside"; l = LIST1 global -> SearchOutside l ] ]
  ;
  in_or_out_modules:
    [ [ m = ne_in_or_out_modules -> m
      | -> SearchOutside [] ] ]
  ;
  comment:
    [ [ c = constr -> CommentConstr c
      | s = STRING -> CommentString s
      | n = natural -> CommentInt n ] ]
  ;
  positive_search_mark:
    [ [ "-" -> false | -> true ] ]
  ;
  scope:
    [ [ "%"; key = IDENT -> key ] ]
  ;
  searchabout_query:
    [ [ b = positive_search_mark; s = ne_string; sc = OPT scope ->
            (b, SearchString (s,sc))
      | b = positive_search_mark; p = constr_pattern ->
            (b, SearchSubPattern p)
      ] ]
  ;
  searchabout_queries:
    [ [ m = ne_in_or_out_modules -> ([],m)
      | s = searchabout_query; l = searchabout_queries ->
        let (sl,m) = l in (s::sl,m)
      | -> ([],SearchOutside [])
      ] ]
  ;
END;

GEXTEND Gram
  command:
    [ [
(* State management *)
        IDENT "Write"; IDENT "State"; s = IDENT -> VernacWriteState s
      | IDENT "Write"; IDENT "State"; s = ne_string -> VernacWriteState s
      | IDENT "Restore"; IDENT "State"; s = IDENT -> VernacRestoreState s
      | IDENT "Restore"; IDENT "State"; s = ne_string -> VernacRestoreState s

(* Resetting *)
      | IDENT "Reset"; IDENT "Initial" -> VernacResetInitial
      | IDENT "Reset"; id = identref -> VernacResetName id
      | IDENT "Back" -> VernacBack 1
      | IDENT "Back"; n = natural -> VernacBack n
      | IDENT "BackTo"; n = natural -> VernacBackTo n
      | IDENT "Backtrack"; n = natural ; m = natural ; p = natural ->
	  VernacBacktrack (n,m,p)

(* Tactic Debugger *)
      |	IDENT "Debug"; IDENT "On" ->
          VernacSetOption (["Ltac";"Debug"], BoolValue true)

      |	IDENT "Debug"; IDENT "Off" ->
          VernacSetOption (["Ltac";"Debug"], BoolValue false)

(* registration of a custom reduction *)

      | IDENT "Declare"; IDENT "Reduction"; s = IDENT; ":=";
         r = Tactic.red_expr ->
	   VernacDeclareReduction (s,r)

 ] ];
    END
;;

(* Grammar extensions *)

GEXTEND Gram
  GLOBAL: syntax;

  syntax:
   [ [ IDENT "Open"; local = obsolete_locality; IDENT "Scope"; sc = IDENT ->
         VernacOpenCloseScope (local,(true,sc))

     | IDENT "Close"; local = obsolete_locality; IDENT "Scope"; sc = IDENT ->
         VernacOpenCloseScope (local,(false,sc))

     | IDENT "Delimit"; IDENT "Scope"; sc = IDENT; "with"; key = IDENT ->
	 VernacDelimiters (sc,key)

     | IDENT "Bind"; IDENT "Scope"; sc = IDENT; "with";
       refl = LIST1 smart_global -> VernacBindScope (sc,refl)

     | IDENT "Infix"; local = obsolete_locality;
	 op = ne_lstring; ":="; p = constr;
         modl = [ "("; l = LIST1 syntax_modifier SEP ","; ")" -> l | -> [] ];
	 sc = OPT [ ":"; sc = IDENT -> sc ] ->
         VernacInfix (local,(op,modl),p,sc)
     | IDENT "Notation"; local = obsolete_locality; id = identref;
	 idl = LIST0 ident; ":="; c = constr; b = only_parsing ->
           VernacSyntacticDefinition
	     (id,(idl,c),local,b)
     | IDENT "Notation"; local = obsolete_locality; s = ne_lstring; ":=";
	 c = constr;
         modl = [ "("; l = LIST1 syntax_modifier SEP ","; ")" -> l | -> [] ];
	 sc = OPT [ ":"; sc = IDENT -> sc ] ->
           VernacNotation (local,c,(s,modl),sc)
     | IDENT "Format"; IDENT "Notation"; n = STRING; s = STRING; fmt = STRING ->
           VernacNotationAddFormat (n,s,fmt)

     | IDENT "Tactic"; IDENT "Notation"; n = tactic_level;
	 pil = LIST1 production_item; ":="; t = Tactic.tactic
         -> VernacTacticNotation (n,pil,t)

     | IDENT "Reserved"; IDENT "Infix"; s = ne_lstring;
	 l = [ "("; l = LIST1 syntax_modifier SEP ","; ")" -> l | -> [] ] ->
	   Metasyntax.check_infix_modifiers l;
	   let (loc,s) = s in
	   VernacSyntaxExtension (false,((loc,"x '"^s^"' y"),l))

     | IDENT "Reserved"; IDENT "Notation"; local = obsolete_locality;
	 s = ne_lstring;
	 l = [ "("; l = LIST1 syntax_modifier SEP ","; ")" -> l | -> [] ]
	 -> VernacSyntaxExtension (local,(s,l))

     (* "Print" "Grammar" should be here but is in "command" entry in order
        to factorize with other "Print"-based vernac entries *)
  ] ]
  ;
  only_parsing:
    [ [ "("; IDENT "only"; IDENT "parsing"; ")" ->
         Some Flags.Current
      | "("; IDENT "compat"; s = STRING; ")" ->
         Some (Coqinit.get_compat_version s)
      | -> None ] ]
  ;
  obsolete_locality:
    [ [ IDENT "Local" -> true | -> false ] ]
  ;
  tactic_level:
    [ [ "("; "at"; IDENT "level"; n = natural; ")" -> n | -> 0 ] ]
  ;
  level:
    [ [ IDENT "level"; n = natural -> NumLevel n
      | IDENT "next"; IDENT "level" -> NextLevel ] ]
  ;
  syntax_modifier:
    [ [ "at"; IDENT "level"; n = natural -> SetLevel n
      | IDENT "left"; IDENT "associativity" -> SetAssoc LeftA
      | IDENT "right"; IDENT "associativity" -> SetAssoc RightA
      | IDENT "no"; IDENT "associativity" -> SetAssoc NonA
      | IDENT "only"; IDENT "parsing" ->
        SetOnlyParsing Flags.Current
      | IDENT "compat"; s = STRING ->
        SetOnlyParsing (Coqinit.get_compat_version s)
      | IDENT "format"; s1 = [s = STRING -> (!@loc,s)];
                        s2 = OPT [s = STRING -> (!@loc,s)] ->
          begin match s1, s2 with
          | (_,k), Some s -> SetFormat(k,s)
          | s, None -> SetFormat ("text",s) end
      | x = IDENT; ","; l = LIST1 [id = IDENT -> id ] SEP ","; "at";
        lev = level -> SetItemLevel (x::l,lev)
      | x = IDENT; "at"; lev = level -> SetItemLevel ([x],lev)
      | x = IDENT; typ = syntax_extension_type -> SetEntryType (x,typ)
    ] ]
  ;
  syntax_extension_type:
    [ [ IDENT "ident" -> ETName | IDENT "global" -> ETReference
      | IDENT "bigint" -> ETBigint
      | IDENT "binder" -> ETBinder true
      | IDENT "closed"; IDENT "binder" -> ETBinder false
    ] ]
  ;
  production_item:
    [ [ s = ne_string -> TacTerm s
      | nt = IDENT;
        po = OPT [ "("; p = ident; sep = [ -> "" | ","; sep = STRING -> sep ];
                   ")" -> (p,sep) ] -> TacNonTerm (!@loc,nt,po) ] ]
  ;
END
