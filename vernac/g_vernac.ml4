(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open CErrors
open Util
open Names
open Glob_term
open Vernacexpr
open Constrexpr
open Constrexpr_ops
open Extend
open Decl_kinds
open Declaremods
open Declarations
open Namegen
open Tok (* necessary for camlp5 *)

open Pcoq
open Pcoq.Prim
open Pcoq.Constr
open Pcoq.Module
open Pvernac.Vernac_

let vernac_kw = [ ";"; ","; ">->"; ":<"; "<:"; "where"; "at" ]
let _ = List.iter CLexer.add_keyword vernac_kw

(* Rem: do not join the different GEXTEND into one, it breaks native *)
(* compilation on PowerPC and Sun architectures *)

let query_command = Gram.entry_create "vernac:query_command"

let subprf = Gram.entry_create "vernac:subprf"

let class_rawexpr = Gram.entry_create "vernac:class_rawexpr"
let thm_token = Gram.entry_create "vernac:thm_token"
let def_body = Gram.entry_create "vernac:def_body"
let decl_notation = Gram.entry_create "vernac:decl_notation"
let record_field = Gram.entry_create "vernac:record_field"
let of_type_with_opt_coercion = Gram.entry_create "vernac:of_type_with_opt_coercion"
let instance_name = Gram.entry_create "vernac:instance_name"
let section_subset_expr = Gram.entry_create "vernac:section_subset_expr"

let make_bullet s =
  let open Proof_bullet in
  let n = String.length s in
  match s.[0] with
  | '-' -> Dash n
  | '+' -> Plus n
  | '*' -> Star n
  | _ -> assert false

let parse_compat_version ?(allow_old = true) = let open Flags in function
  | "8.8" -> Current
  | "8.7" -> V8_7
  | "8.6" -> V8_6
  | ("8.5" | "8.4" | "8.3" | "8.2" | "8.1" | "8.0") as s ->
    CErrors.user_err ~hdr:"get_compat_version"
      Pp.(str "Compatibility with version " ++ str s ++ str " not supported.")
  | s ->
    CErrors.user_err ~hdr:"get_compat_version"
      Pp.(str "Unknown compatibility version \"" ++ str s ++ str "\".")

GEXTEND Gram
  GLOBAL: vernac_control gallina_ext noedit_mode subprf;
  vernac_control: FIRST
    [ [ IDENT "Time"; c = located_vernac -> VernacTime (false,c)
      | IDENT "Redirect"; s = ne_string; c = located_vernac -> VernacRedirect (s, c)
      | IDENT "Timeout"; n = natural; v = vernac_control -> VernacTimeout(n,v)
      | IDENT "Fail"; v = vernac_control -> VernacFail v
      | (f, v) = vernac -> VernacExpr(f, v) ]
    ]
  ;
  vernac:
    [ [ IDENT "Local"; (f, v) = vernac_poly -> (VernacLocal true :: f, v)
      | IDENT "Global"; (f, v) = vernac_poly -> (VernacLocal false :: f, v)

      | v = vernac_poly -> v ]
    ]
  ;
  vernac_poly:
    [ [ IDENT "Polymorphic"; (f, v) = vernac_aux -> (VernacPolymorphic true :: f, v)
      | IDENT "Monomorphic"; (f, v) = vernac_aux -> (VernacPolymorphic false :: f, v)
      | v = vernac_aux -> v ]
    ]
  ;
  vernac_aux:
    (* Better to parse "." here: in case of failure (e.g. in coerce_to_var), *)
    (* "." is still in the stream and discard_to_dot works correctly         *)
    [ [ IDENT "Program"; g = gallina; "." -> ([VernacProgram], g)
      | IDENT "Program"; (f, g) = gallina_ext; "." -> (VernacProgram :: f, g)
      | g = gallina; "." -> ([], g)
      | g = gallina_ext; "." -> g
      | c = command; "." -> ([], c)
      | c = syntax; "." -> ([], c)
      | c = subprf -> ([], c)
    ] ]
  ;
  vernac_aux: LAST
    [ [ prfcom = command_entry -> ([], prfcom) ] ]
  ;
  noedit_mode:
    [ [ c = query_command -> c None] ]
  ;

  subprf:
  [ [ s = BULLET -> VernacBullet (make_bullet s)
    | "{" -> VernacSubproof None
    | "}" -> VernacEndSubproof
    ] ]
  ;

  located_vernac:
    [ [ v = vernac_control -> CAst.make ~loc:!@loc v ] ]
  ;
END

let warn_plural_command =
  CWarnings.create ~name:"plural-command" ~category:"pedantic" ~default:CWarnings.Disabled
         (fun kwd -> strbrk (Printf.sprintf "Command \"%s\" expects more than one assumption." kwd))

let test_plural_form loc kwd = function
  | [(_,([_],_))] ->
     warn_plural_command ~loc:!@loc kwd
  | _ -> ()

let test_plural_form_types loc kwd = function
  | [([_],_)] ->
     warn_plural_command ~loc:!@loc kwd
  | _ -> ()

let lname_of_lident : lident -> lname =
  CAst.map (fun s -> Name s)

let name_of_ident_decl : ident_decl -> name_decl =
  on_fst lname_of_lident

(* Gallina declarations *)
GEXTEND Gram
  GLOBAL: gallina gallina_ext thm_token def_body of_type_with_opt_coercion
    record_field decl_notation rec_definition ident_decl univ_decl;

  gallina:
      (* Definition, Theorem, Variable, Axiom, ... *)
    [ [ thm = thm_token; id = ident_decl; bl = binders; ":"; c = lconstr;
        l = LIST0
          [ "with"; id = ident_decl; bl = binders; ":"; c = lconstr ->
          (id,(bl,c)) ] ->
          VernacStartTheoremProof (thm, (id,(bl,c))::l)
      | stre = assumption_token; nl = inline; bl = assum_list ->
	  VernacAssumption (stre, nl, bl)
      | (kwd,stre) = assumptions_token; nl = inline; bl = assum_list ->
	  test_plural_form loc kwd bl;
	  VernacAssumption (stre, nl, bl)
      | d = def_token; id = ident_decl; b = def_body ->
          VernacDefinition (d, name_of_ident_decl id, b)
      | IDENT "Let"; id = identref; b = def_body ->
          VernacDefinition ((DoDischarge, Let), (lname_of_lident id, None), b)
      (* Gallina inductive declarations *)
      | cum = OPT cumulativity_token; priv = private_token; f = finite_token;
        indl = LIST1 inductive_definition SEP "with" ->
	  let (k,f) = f in
          let indl=List.map (fun ((a,b,c,d),e) -> ((a,b,c,k,d),e)) indl in
          VernacInductive (cum, priv,f,indl)
      | "Fixpoint"; recs = LIST1 rec_definition SEP "with" ->
          VernacFixpoint (NoDischarge, recs)
      | IDENT "Let"; "Fixpoint"; recs = LIST1 rec_definition SEP "with" ->
          VernacFixpoint (DoDischarge, recs)
      | "CoFixpoint"; corecs = LIST1 corec_definition SEP "with" ->
          VernacCoFixpoint (NoDischarge, corecs)
      | IDENT "Let"; "CoFixpoint"; corecs = LIST1 corec_definition SEP "with" ->
          VernacCoFixpoint (DoDischarge, corecs)
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
    [ [ "Definition" -> (NoDischarge,Definition)
      | IDENT "Example" -> (NoDischarge,Example)
      | IDENT "SubClass" -> (NoDischarge,SubClass) ] ]
  ;
  assumption_token:
    [ [ "Hypothesis" -> (DoDischarge, Logical)
      | "Variable" -> (DoDischarge, Definitional)
      | "Axiom" -> (NoDischarge, Logical)
      | "Parameter" -> (NoDischarge, Definitional)
      | IDENT "Conjecture" -> (NoDischarge, Conjectural) ] ]
  ;
  assumptions_token:
    [ [ IDENT "Hypotheses" -> ("Hypotheses", (DoDischarge, Logical))
      | IDENT "Variables" -> ("Variables", (DoDischarge, Definitional))
      | IDENT "Axioms" -> ("Axioms", (NoDischarge, Logical))
      | IDENT "Parameters" -> ("Parameters", (NoDischarge, Definitional))
      | IDENT "Conjectures" -> ("Conjectures", (NoDischarge, Conjectural)) ] ]
  ;
  inline:
    [ [ IDENT "Inline"; "("; i = INT; ")" -> InlineAt (int_of_string i)
      | IDENT "Inline" -> DefaultInline
      | -> NoInline] ]
  ;
  univ_constraint:
    [ [ l = universe_level; ord = [ "<" -> Univ.Lt | "=" -> Univ.Eq | "<=" -> Univ.Le ];
	r = universe_level -> (l, ord, r) ] ]
  ;
  univ_decl :
    [ [  "@{" ; l = LIST0 identref; ext = [ "+" -> true | -> false ];
         cs = [ "|"; l' = LIST0 univ_constraint SEP ",";
                ext = [ "+" -> true | -> false ]; "}" -> (l',ext)
              | ext = [ "}" -> true | "|}" -> false ] -> ([], ext) ]
         ->
         let open UState in
         { univdecl_instance = l;
           univdecl_extensible_instance = ext;
           univdecl_constraints = fst cs;
           univdecl_extensible_constraints = snd cs }
    ] ]
  ;
  ident_decl:
    [ [ i = identref; l = OPT univ_decl -> (i, l)
  ] ]
  ;
  finite_token:
    [ [ IDENT "Inductive" -> (Inductive_kw,Finite)
      | IDENT "CoInductive" -> (CoInductive,CoFinite)
      | IDENT "Variant" -> (Variant,BiFinite)
      | IDENT "Record" -> (Record,BiFinite)
      | IDENT "Structure" -> (Structure,BiFinite)
      | IDENT "Class" -> (Class true,BiFinite) ] ]
  ;
  cumulativity_token:
    [ [ IDENT "Cumulative" -> VernacCumulative
      | IDENT "NonCumulative" -> VernacNonCumulative ] ]
  ;
  private_token:
    [ [ IDENT "Private" -> true | -> false ] ]
  ;
  (* Simple definitions *)
  def_body:
    [ [ bl = binders; ":="; red = reduce; c = lconstr ->
      if List.exists (function CLocalPattern _ -> true | _ -> false) bl
      then
        (* FIXME: "red" will be applied to types in bl and Cast with remain *)
        let c = mkCLambdaN ~loc:!@loc bl c in
	DefineBody ([], red, c, None)
      else
        (match c with
        | { CAst.v = CCast(c, CastConv t) } -> DefineBody (bl, red, c, Some t)
        | _ -> DefineBody (bl, red, c, None))
    | bl = binders; ":"; t = lconstr; ":="; red = reduce; c = lconstr ->
        let ((bl, c), tyo) =
          if List.exists (function CLocalPattern _ -> true | _ -> false) bl
          then
            (* FIXME: "red" will be applied to types in bl and Cast with remain *)
            let c = CAst.make ~loc:!@loc @@ CCast (c, CastConv t) in
            (([],mkCLambdaN ~loc:!@loc bl c), None)
          else ((bl, c), Some t)
        in
	DefineBody (bl, red, c, tyo)
    | bl = binders; ":"; t = lconstr ->
        ProveBody (bl, t) ] ]
  ;
  reduce:
    [ [ IDENT "Eval"; r = red_expr; "in" -> Some r
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
    [ [ oc = opt_coercion; id = ident_decl; indpar = binders;
        c = OPT [ ":"; c = lconstr -> c ];
        lc=opt_constructors_or_fields; ntn = decl_notation ->
	   (((oc,id),indpar,c,lc),ntn) ] ]
  ;
  constructor_list_or_record_decl:
    [ [ "|"; l = LIST1 constructor SEP "|" -> Constructors l
      | id = identref ; c = constructor_type; "|"; l = LIST0 constructor SEP "|" ->
	  Constructors ((c id)::l)
      | id = identref ; c = constructor_type -> Constructors [ c id ]
      | cstr = identref; "{"; fs = record_fields; "}" ->
	  RecordDecl (Some cstr,fs)
      | "{";fs = record_fields; "}" -> RecordDecl (None,fs)
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
    [ [ id = ident_decl;
	bl = binders_fixannot;
        ty = type_cstr;
	def = OPT [":="; def = lconstr -> def]; ntn = decl_notation ->
	  let bl, annot = bl in ((id,annot,bl,ty,def),ntn) ] ]
  ;
  corec_definition:
    [ [ id = ident_decl; bl = binders; ty = type_cstr;
        def = OPT [":="; def = lconstr -> def]; ntn = decl_notation ->
          ((id,bl,ty,def),ntn) ] ]
  ;
  type_cstr:
    [ [ ":"; c=lconstr -> c
      | -> CAst.make ~loc:!@loc @@ CHole (None, IntroAnonymous, None) ] ]
  ;
  (* Inductive schemes *)
  scheme:
    [ [ kind = scheme_kind -> (None,kind)
      | id = identref; ":="; kind = scheme_kind -> (Some id,kind) ] ]
  ;
  scheme_kind:
    [ [ IDENT "Induction"; "for"; ind = smart_global;
          IDENT "Sort"; s = sort_family-> InductionScheme(true,ind,s)
      | IDENT "Minimality"; "for"; ind = smart_global;
          IDENT "Sort"; s = sort_family-> InductionScheme(false,ind,s)
      | IDENT "Elimination"; "for"; ind = smart_global;
          IDENT "Sort"; s = sort_family-> CaseScheme(true,ind,s)
      | IDENT "Case"; "for"; ind = smart_global;
          IDENT "Sort"; s = sort_family-> CaseScheme(false,ind,s)
      | IDENT "Equality"; "for" ; ind = smart_global -> EqualityScheme(ind) ] ]
  ;
  (* Various Binders *)
(*
  (* ... without coercions *)
  binder_nodef:
    [ [ b = binder_let ->
      (match b with
          CLocalAssum(l,ty) -> (l,ty)
        | CLocalDef _ ->
            Util.user_err_loc
              (loc,"fix_param",Pp.str"defined binder not allowed here.")) ] ]
  ;
*)
  (* ... with coercions *)
  record_field:
  [ [ bd = record_binder; pri = OPT [ "|"; n = natural -> n ];
      ntn = decl_notation -> (bd,pri),ntn ] ]
  ;
  record_fields:
    [ [ f = record_field; ";"; fs = record_fields -> f :: fs
      | f = record_field; ";" -> [f]
      | f = record_field -> [f]
      | -> []
    ] ]
  ;
  record_binder_body:
    [ [ l = binders; oc = of_type_with_opt_coercion;
         t = lconstr -> fun id -> (oc,AssumExpr (id,mkCProdN ~loc:!@loc l t))
      | l = binders; oc = of_type_with_opt_coercion;
         t = lconstr; ":="; b = lconstr -> fun id ->
	   (oc,DefExpr (id,mkCLambdaN ~loc:!@loc l b,Some (mkCProdN ~loc:!@loc l t)))
      | l = binders; ":="; b = lconstr -> fun id ->
         match b.CAst.v with
	 | CCast(b', (CastConv t|CastVM t|CastNative t)) ->
	     (None,DefExpr(id,mkCLambdaN ~loc:!@loc l b',Some (mkCProdN ~loc:!@loc l t)))
         | _ ->
	     (None,DefExpr(id,mkCLambdaN ~loc:!@loc l b,None)) ] ]
  ;
  record_binder:
    [ [ id = name -> (None,AssumExpr(id, CAst.make ~loc:!@loc @@ CHole (None, IntroAnonymous, None)))
      | id = name; f = record_binder_body -> f id ] ]
  ;
  assum_list:
    [ [ bl = LIST1 assum_coe -> bl | b = simple_assum_coe -> [b] ] ]
  ;
  assum_coe:
    [ [ "("; a = simple_assum_coe; ")" -> a ] ]
  ;
  simple_assum_coe:
    [ [ idl = LIST1 ident_decl; oc = of_type_with_opt_coercion; c = lconstr ->
        (not (Option.is_empty oc),(idl,c)) ] ]
  ;

  constructor_type:
    [[ l = binders;
      t= [ coe = of_type_with_opt_coercion; c = lconstr ->
	            fun l id -> (not (Option.is_empty coe),(id,mkCProdN ~loc:!@loc l c))
            |  ->
                 fun l id -> (false,(id,mkCProdN ~loc:!@loc l (CAst.make ~loc:!@loc @@ CHole (None, IntroAnonymous, None)))) ]
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

let only_starredidentrefs =
  Gram.Entry.of_parser "test_only_starredidentrefs"
    (fun strm ->
      let rec aux n =
      match Util.stream_nth n strm with
        | KEYWORD "." -> ()
        | KEYWORD ")" -> ()
        | (IDENT _ | KEYWORD "Type" | KEYWORD "*") -> aux (n+1)
        | _ -> raise Stream.Failure in
      aux 0)
let starredidentreflist_to_expr l =
  match l with
  | [] -> SsEmpty
  | x :: xs -> List.fold_right (fun i acc -> SsUnion(i,acc)) xs x

let warn_deprecated_include_type =
  CWarnings.create ~name:"deprecated-include-type" ~category:"deprecated"
         (fun () -> strbrk "Include Type is deprecated; use Include instead")

(* Modules and Sections *)
GEXTEND Gram
  GLOBAL: gallina_ext module_expr module_type section_subset_expr;

  gallina_ext:
    [ [ (* Interactive module declaration *)
        IDENT "Module"; export = export_token; id = identref;
	bl = LIST0 module_binder; sign = of_module_type;
	body = is_module_expr ->
        [], VernacDefineModule (export, id, bl, sign, body)
      | IDENT "Module"; "Type"; id = identref;
	bl = LIST0 module_binder; sign = check_module_types;
	body = is_module_type ->
        [], VernacDeclareModuleType (id, bl, sign, body)
      | IDENT "Declare"; IDENT "Module"; export = export_token; id = identref;
	bl = LIST0 module_binder; ":"; mty = module_type_inl ->
        [], VernacDeclareModule (export, id, bl, mty)
      (* Section beginning *)
      | IDENT "Section"; id = identref -> [], VernacBeginSection id
      | IDENT "Chapter"; id = identref -> [], VernacBeginSection id

      (* This end a Section a Module or a Module Type *)
      | IDENT "End"; id = identref -> [], VernacEndSegment id

      (* Naming a set of section hyps *)
      | IDENT "Collection"; id = identref; ":="; expr = section_subset_expr ->
        [], VernacNameSectionHypSet (id, expr)

      (* Requiring an already compiled module *)
      | IDENT "Require"; export = export_token; qidl = LIST1 global ->
        [], VernacRequire (None, export, qidl)
      | IDENT "From" ; ns = global ; IDENT "Require"; export = export_token
	; qidl = LIST1 global ->
        [], VernacRequire (Some ns, export, qidl)
      | IDENT "Import"; qidl = LIST1 global -> [], VernacImport (false,qidl)
      | IDENT "Export"; qidl = LIST1 global -> [], VernacImport (true,qidl)
      | IDENT "Include"; e = module_type_inl; l = LIST0 ext_module_expr ->
        [], VernacInclude(e::l)
      | IDENT "Include"; "Type"; e = module_type_inl; l = LIST0 ext_module_type ->
	 warn_deprecated_include_type ~loc:!@loc ();
        [], VernacInclude(e::l) ] ]
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
      | me1 = module_expr; me2 = module_expr_atom -> CAst.make ~loc:!@loc @@ CMapply (me1,me2)
      ] ]
  ;
  module_expr_atom:
    [ [ qid = qualid -> CAst.make ~loc:!@loc @@ CMident qid | "("; me = module_expr; ")" -> me ] ]
  ;
  with_declaration:
    [ [ "Definition"; fqid = fullyqualid; udecl = OPT univ_decl; ":="; c = Constr.lconstr ->
          CWith_Definition (fqid,udecl,c)
      | IDENT "Module"; fqid = fullyqualid; ":="; qid = qualid ->
	  CWith_Module (fqid,qid)
      ] ]
  ;
  module_type:
    [ [ qid = qualid -> CAst.make ~loc:!@loc @@ CMident qid
      | "("; mt = module_type; ")" -> mt
      | mty = module_type; me = module_expr_atom ->
          CAst.make ~loc:!@loc @@ CMapply (mty,me)
      | mty = module_type; "with"; decl = with_declaration ->
          CAst.make ~loc:!@loc @@ CMwith (mty,decl)
      ] ]
  ;
  (* Proof using *)
  section_subset_expr:
    [ [ only_starredidentrefs; l = LIST0 starredidentref ->
          starredidentreflist_to_expr l
      | e = ssexpr -> e ]]
  ;
  starredidentref:
    [ [ i = identref -> SsSingl i
      | i = identref; "*" -> SsFwdClose(SsSingl i)
      | "Type" -> SsType
      | "Type"; "*" -> SsFwdClose SsType ]]
  ;
  ssexpr:
    [ "35" 
      [ "-"; e = ssexpr -> SsCompl e ]
    | "50"
      [ e1 = ssexpr; "-"; e2 = ssexpr->SsSubstr(e1,e2)
      | e1 = ssexpr; "+"; e2 = ssexpr->SsUnion(e1,e2)]
    | "0"
      [ i = starredidentref -> i
      | "("; only_starredidentrefs; l = LIST0 starredidentref; ")"->
          starredidentreflist_to_expr l
      | "("; only_starredidentrefs; l = LIST0 starredidentref; ")"; "*" ->
          SsFwdClose(starredidentreflist_to_expr l)
      | "("; e = ssexpr; ")"-> e 
      | "("; e = ssexpr; ")"; "*" -> SsFwdClose e ] ]
  ;
END

(* Extensions: implicits, coercions, etc. *)
GEXTEND Gram
  GLOBAL: gallina_ext instance_name hint_info;

  gallina_ext:
    [ [ (* Transparent and Opaque *)
        IDENT "Transparent"; l = LIST1 smart_global ->
        [], VernacSetOpacity (Conv_oracle.transparent, l)
      | IDENT "Opaque"; l = LIST1 smart_global ->
        [], VernacSetOpacity (Conv_oracle.Opaque, l)
      | IDENT "Strategy"; l =
          LIST1 [ v=strategy_level; "["; q=LIST1 smart_global; "]" -> (v,q)] ->
        [], VernacSetStrategy l
      (* Canonical structure *)
      | IDENT "Canonical"; IDENT "Structure"; qid = global ->
          [], VernacCanonical CAst.(make ~loc:!@loc @@ AN qid)
      | IDENT "Canonical"; IDENT "Structure"; ntn = by_notation ->
          [], VernacCanonical CAst.(make ~loc:!@loc @@ ByNotation ntn)
      | IDENT "Canonical"; IDENT "Structure"; qid = global; d = def_body ->
          let s = coerce_reference_to_id qid in
        [], VernacDefinition ((NoDischarge,CanonicalStructure),((CAst.make (Name s)),None),d)

      (* Coercions *)
      | IDENT "Coercion"; qid = global; d = def_body ->
          let s = coerce_reference_to_id qid in
        [], VernacDefinition ((NoDischarge,Coercion),((CAst.make (Name s)),None),d)
      | IDENT "Identity"; IDENT "Coercion"; f = identref; ":";
         s = class_rawexpr; ">->"; t = class_rawexpr ->
        [], VernacIdentityCoercion (f, s, t)
      | IDENT "Coercion"; qid = global; ":"; s = class_rawexpr; ">->";
         t = class_rawexpr ->
        [], VernacCoercion (CAst.make ~loc:!@loc @@ AN qid, s, t)
      | IDENT "Coercion"; ntn = by_notation; ":"; s = class_rawexpr; ">->";
         t = class_rawexpr ->
        [], VernacCoercion (CAst.make ~loc:!@loc @@ ByNotation ntn, s, t)

      | IDENT "Context"; c = LIST1 binder ->
        [], VernacContext (List.flatten c)

      | IDENT "Instance"; namesup = instance_name; ":";
	 expl = [ "!" -> Decl_kinds.Implicit | -> Decl_kinds.Explicit ] ; t = operconstr LEVEL "200";
	 info = hint_info ;
	 props = [ ":="; "{"; r = record_declaration; "}" -> Some (true,r) |
	     ":="; c = lconstr -> Some (false,c) | -> None ] ->
        [], VernacInstance (false,snd namesup,(fst namesup,expl,t),props,info)

      | IDENT "Existing"; IDENT "Instance"; id = global;
          info = hint_info ->
        [], VernacDeclareInstances [id, info]

      | IDENT "Existing"; IDENT "Instances"; ids = LIST1 global;
        pri = OPT [ "|"; i = natural -> i ] ->
         let info = { Typeclasses.hint_priority = pri; hint_pattern = None } in
         let insts = List.map (fun i -> (i, info)) ids in
        [], VernacDeclareInstances insts

      | IDENT "Existing"; IDENT "Class"; is = global -> [], VernacDeclareClass is

      (* Arguments *)
      | IDENT "Arguments"; qid = smart_global; 
        args = LIST0 argument_spec_block;
        more_implicits = OPT
          [ ","; impl = LIST1
            [ impl = LIST0 more_implicits_block -> List.flatten impl]
            SEP "," -> impl
          ];
        mods = OPT [ ":"; l = LIST1 arguments_modifier SEP "," -> l ] ->
         let mods = match mods with None -> [] | Some l -> List.flatten l in
         let slash_position = ref None in
         let rec parse_args i = function
           | [] -> []
           | `Id x :: args -> x :: parse_args (i+1) args
           | `Slash :: args ->
              if Option.is_empty !slash_position then
                (slash_position := Some i; parse_args i args)
              else
                user_err Pp.(str "The \"/\" modifier can occur only once")
         in
         let args = parse_args 0 (List.flatten args) in
         let more_implicits = Option.default [] more_implicits in
         [], VernacArguments (qid, args, more_implicits, !slash_position, mods)

      | IDENT "Implicit"; "Type"; bl = reserv_list ->
        [], VernacReserve bl

      | IDENT "Implicit"; IDENT "Types"; bl = reserv_list ->
          test_plural_form_types loc "Implicit Types" bl;
        [], VernacReserve bl

      | IDENT "Generalizable"; 
	   gen = [IDENT "All"; IDENT "Variables" -> Some []
	     | IDENT "No"; IDENT "Variables" -> None
	     | ["Variable" | IDENT "Variables"];
		  idl = LIST1 identref -> Some idl ] ->
        [], VernacGeneralizable gen ] ]
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
  scope:
    [ [ "%"; key = IDENT -> key ] ]
  ;
  argument_spec: [
       [ b = OPT "!"; id = name ; s = OPT scope ->
       id.CAst.v, not (Option.is_empty b), Option.map (fun x -> CAst.make ~loc:!@loc x) s
    ]
  ];
  (* List of arguments implicit status, scope, modifiers *)
  argument_spec_block: [
    [ item = argument_spec ->
      let name, recarg_like, notation_scope = item in
      [`Id { name=name; recarg_like=recarg_like;
             notation_scope=notation_scope;
             implicit_status = NotImplicit}]
    | "/" -> [`Slash]
    | "("; items = LIST1 argument_spec; ")"; sc = OPT scope ->
       let f x = match sc, x with
         | None, x -> x | x, None -> Option.map (fun y -> CAst.make ~loc:!@loc y) x
         | Some _, Some _ -> user_err Pp.(str "scope declared twice") in
       List.map (fun (name,recarg_like,notation_scope) ->
           `Id { name=name; recarg_like=recarg_like;
                 notation_scope=f notation_scope;
                 implicit_status = NotImplicit}) items
    | "["; items = LIST1 argument_spec; "]"; sc = OPT scope ->
       let f x = match sc, x with
         | None, x -> x | x, None -> Option.map (fun y -> CAst.make ~loc:!@loc y) x
         | Some _, Some _ -> user_err Pp.(str "scope declared twice") in
       List.map (fun (name,recarg_like,notation_scope) ->
           `Id { name=name; recarg_like=recarg_like;
                 notation_scope=f notation_scope;
                 implicit_status = Implicit}) items
    | "{"; items = LIST1 argument_spec; "}"; sc = OPT scope ->
       let f x = match sc, x with
         | None, x -> x | x, None -> Option.map (fun y -> CAst.make ~loc:!@loc y) x
         | Some _, Some _ -> user_err Pp.(str "scope declared twice") in
       List.map (fun (name,recarg_like,notation_scope) ->
           `Id { name=name; recarg_like=recarg_like;
                 notation_scope=f notation_scope;
                 implicit_status = MaximallyImplicit}) items
    ]
  ];
  (* Same as [argument_spec_block], but with only implicit status and names *)
  more_implicits_block: [
    [ name = name -> [(name.CAst.v, Vernacexpr.NotImplicit)]
    | "["; items = LIST1 name; "]" ->
       List.map (fun name -> (name.CAst.v, Vernacexpr.Implicit)) items
    | "{"; items = LIST1 name; "}" ->
       List.map (fun name -> (name.CAst.v, Vernacexpr.MaximallyImplicit)) items
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
    [ [ name = ident_decl; sup = OPT binders ->
          (CAst.map (fun id -> Name id) (fst name), snd name),
          (Option.default [] sup)
      | -> ((CAst.make ~loc:!@loc Anonymous), None), []  ] ]
  ;
  hint_info:
    [ [ "|"; i = OPT natural; pat = OPT constr_pattern ->
         { Typeclasses.hint_priority = i; hint_pattern = pat }
      | -> { Typeclasses.hint_priority = None; hint_pattern = None } ] ]
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
  GLOBAL: command query_command class_rawexpr gallina_ext;

  gallina_ext:
    [ [ IDENT "Export"; "Set"; table = option_table; v = option_value ->
        [], VernacSetOption (true, table, v)
      | IDENT "Export"; IDENT "Unset"; table = option_table ->
        [], VernacUnsetOption (true, table)
    ] ];

  command:
    [ [ IDENT "Comments"; l = LIST0 comment -> VernacComments l

      (* Hack! Should be in grammar_ext, but camlp5 factorizes badly *)
      | IDENT "Declare"; IDENT "Instance"; namesup = instance_name; ":";
	 expl = [ "!" -> Decl_kinds.Implicit | -> Decl_kinds.Explicit ] ; t = operconstr LEVEL "200";
	 info = hint_info ->
	   VernacInstance (true, snd namesup, (fst namesup, expl, t), None, info)

      (* System directory *)
      | IDENT "Pwd" -> VernacChdir None
      | IDENT "Cd" -> VernacChdir None
      | IDENT "Cd"; dir = ne_string -> VernacChdir (Some dir)

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
      | IDENT "Print"; qid = smart_global; l = OPT univ_name_list -> VernacPrint (PrintName (qid,l))
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
          VernacSetOption (false, table, v)
      | IDENT "Unset"; table = option_table ->
          VernacUnsetOption (false, table)

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
    [ [ IDENT "Eval"; r = red_expr; "in"; c = lconstr; "." ->
          fun g -> VernacCheckMayEval (Some r, g, c)
      | IDENT "Compute"; c = lconstr; "." ->
	  fun g -> VernacCheckMayEval (Some (Genredexpr.CbvVm None), g, c)
      | IDENT "Check"; c = lconstr; "." ->
	 fun g -> VernacCheckMayEval (None, g, c)
      (* Searching the environment *)
      | IDENT "About"; qid = smart_global; l = OPT univ_name_list; "." ->
         fun g -> VernacPrint (PrintAbout (qid,l,g))
      | IDENT "SearchHead"; c = constr_pattern; l = in_or_out_modules; "." ->
	  fun g -> VernacSearch (SearchHead c,g, l)
      | IDENT "SearchPattern"; c = constr_pattern; l = in_or_out_modules; "." ->
	  fun g -> VernacSearch (SearchPattern c,g, l)
      | IDENT "SearchRewrite"; c = constr_pattern; l = in_or_out_modules; "." ->
	  fun g -> VernacSearch (SearchRewrite c,g, l)
      | IDENT "Search"; s = searchabout_query; l = searchabout_queries; "." ->
	  let (sl,m) = l in fun g -> VernacSearch (SearchAbout (s::sl),g, m)
      (* compatibility: SearchAbout *)
      | IDENT "SearchAbout"; s = searchabout_query; l = searchabout_queries; "." ->
	  fun g -> let (sl,m) = l in VernacSearch (SearchAbout (s::sl),g, m)
      (* compatibility: SearchAbout with "[ ... ]" *)
      | IDENT "SearchAbout"; "["; sl = LIST1 searchabout_query; "]";
	l = in_or_out_modules; "." ->
         fun g -> VernacSearch (SearchAbout sl,g, l)
      ] ]
  ;
  printable:
    [ [ IDENT "Term"; qid = smart_global; l = OPT univ_name_list -> PrintName (qid,l)
      | IDENT "All" -> PrintFullContext
      | IDENT "Section"; s = global -> PrintSectionContext s
      | IDENT "Grammar"; ent = IDENT ->
          (* This should be in "syntax" section but is here for factorization*)
	  PrintGrammar ent
      | IDENT "LoadPath"; dir = OPT dirpath -> PrintLoadPath dir
      | IDENT "Modules" ->
          user_err Pp.(str "Print Modules is obsolete; use Print Libraries instead")
      | IDENT "Libraries" -> PrintModules

      | IDENT "ML"; IDENT "Path" -> PrintMLLoadPath
      | IDENT "ML"; IDENT "Modules" -> PrintMLModules
      | IDENT "Debug"; IDENT "GC" -> PrintDebugGC
      | IDENT "Graph" -> PrintGraph
      | IDENT "Classes" ->  PrintClasses
      | IDENT "TypeClasses" -> PrintTypeClasses
      | IDENT "Instances"; qid = smart_global -> PrintInstances qid
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
      | IDENT "Module"; qid = global -> LocateModule qid ] ]
  ;
  option_value:
    [ [ -> BoolValue true
      | n  = integer   -> IntValue (Some n)
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
  univ_name_list:
    [ [  "@{" ; l = LIST0 name; "}" -> l ] ]
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

(* Tactic Debugger *)
      |	IDENT "Debug"; IDENT "On" ->
          VernacSetOption (false, ["Ltac";"Debug"], BoolValue true)

      |	IDENT "Debug"; IDENT "Off" ->
          VernacSetOption (false, ["Ltac";"Debug"], BoolValue false)

(* registration of a custom reduction *)

      | IDENT "Declare"; IDENT "Reduction"; s = IDENT; ":=";
         r = red_expr ->
	   VernacDeclareReduction (s,r)

 ] ];
    END
;;

(* Grammar extensions *)

GEXTEND Gram
  GLOBAL: syntax;

  syntax:
   [ [ IDENT "Open"; IDENT "Scope"; sc = IDENT ->
         VernacOpenCloseScope (true,sc)

     | IDENT "Close"; IDENT "Scope"; sc = IDENT ->
         VernacOpenCloseScope (false,sc)

     | IDENT "Delimit"; IDENT "Scope"; sc = IDENT; "with"; key = IDENT ->
	 VernacDelimiters (sc, Some key)
     | IDENT "Undelimit"; IDENT "Scope"; sc = IDENT ->
	 VernacDelimiters (sc, None)

     | IDENT "Bind"; IDENT "Scope"; sc = IDENT; "with";
       refl = LIST1 class_rawexpr -> VernacBindScope (sc,refl)

     | IDENT "Infix"; op = ne_lstring; ":="; p = constr;
         modl = [ "("; l = LIST1 syntax_modifier SEP ","; ")" -> l | -> [] ];
	 sc = OPT [ ":"; sc = IDENT -> sc ] ->
         VernacInfix ((op,modl),p,sc)
     | IDENT "Notation"; id = identref;
	 idl = LIST0 ident; ":="; c = constr; b = only_parsing ->
           VernacSyntacticDefinition
             (id,(idl,c),b)
     | IDENT "Notation"; s = lstring; ":=";
	 c = constr;
         modl = [ "("; l = LIST1 syntax_modifier SEP ","; ")" -> l | -> [] ];
	 sc = OPT [ ":"; sc = IDENT -> sc ] ->
           VernacNotation (c,(s,modl),sc)
     | IDENT "Format"; IDENT "Notation"; n = STRING; s = STRING; fmt = STRING ->
           VernacNotationAddFormat (n,s,fmt)

     | IDENT "Reserved"; IDENT "Infix"; s = ne_lstring;
	 l = [ "("; l = LIST1 syntax_modifier SEP ","; ")" -> l | -> [] ] ->
           let s = CAst.map (fun s -> "x '"^s^"' y") s in
           VernacSyntaxExtension (true,(s,l))

     | IDENT "Reserved"; IDENT "Notation";
	 s = ne_lstring;
	 l = [ "("; l = LIST1 syntax_modifier SEP ","; ")" -> l | -> [] ]
         -> VernacSyntaxExtension (false, (s,l))

     (* "Print" "Grammar" should be here but is in "command" entry in order
        to factorize with other "Print"-based vernac entries *)
  ] ]
  ;
  only_parsing:
    [ [ "("; IDENT "only"; IDENT "parsing"; ")" ->
         Some Flags.Current
      | "("; IDENT "compat"; s = STRING; ")" ->
         Some (parse_compat_version s)
      | -> None ] ]
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
      | IDENT "only"; IDENT "printing" -> SetOnlyPrinting
      | IDENT "only"; IDENT "parsing" -> SetOnlyParsing
      | IDENT "compat"; s = STRING ->
        SetCompatVersion (parse_compat_version s)
      | IDENT "format"; s1 = [s = STRING -> CAst.make ~loc:!@loc s];
                        s2 = OPT [s = STRING -> CAst.make ~loc:!@loc s] ->
          begin match s1, s2 with
          | { CAst.v = k }, Some s -> SetFormat(k,s)
          | s, None -> SetFormat ("text",s) end
      | x = IDENT; ","; l = LIST1 [id = IDENT -> id ] SEP ","; "at";
        lev = level -> SetItemLevel (x::l,lev)
      | x = IDENT; "at"; lev = level -> SetItemLevel ([x],lev)
      | x = IDENT; "at"; lev = level; b = constr_as_binder_kind -> SetItemLevelAsBinder ([x],b,Some lev)
      | x = IDENT; b = constr_as_binder_kind -> SetItemLevelAsBinder ([x],b,None)
      | x = IDENT; typ = syntax_extension_type -> SetEntryType (x,typ)
    ] ]
  ;
  syntax_extension_type:
    [ [ IDENT "ident" -> ETName | IDENT "global" -> ETReference
      | IDENT "bigint" -> ETBigint
      | IDENT "binder" -> ETBinder true
      | IDENT "constr"; n = OPT at_level; b = constr_as_binder_kind -> ETConstrAsBinder (b,n)
      | IDENT "pattern" -> ETPattern (false,None)
      | IDENT "pattern"; "at"; IDENT "level"; n = natural -> ETPattern (false,Some n)
      | IDENT "strict"; IDENT "pattern" -> ETPattern (true,None)
      | IDENT "strict"; IDENT "pattern"; "at"; IDENT "level"; n = natural -> ETPattern (true,Some n)
      | IDENT "closed"; IDENT "binder" -> ETBinder false
    ] ]
  ;
  at_level:
    [ [ "at"; n = level -> n ] ]
  ;
  constr_as_binder_kind:
    [ [ "as"; IDENT "ident" -> Notation_term.AsIdent
      | "as"; IDENT "pattern" -> Notation_term.AsIdentOrPattern
      | "as"; IDENT "strict"; IDENT "pattern" -> Notation_term.AsStrictPattern ] ]
  ;
END
