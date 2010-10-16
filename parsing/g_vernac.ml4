(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4deps: "parsing/grammar.cma" i*)


open Pp
open Compat
open Tok
open Util
open Names
open Topconstr
open Extend
open Vernacexpr
open Pcoq
open Tactic
open Decl_kinds
open Genarg
open Ppextend
open Goptions

open Prim
open Constr
open Vernac_
open Module

let vernac_kw = [ ";"; ","; ">->"; ":<"; "<:"; "where"; "at" ]
let _ = List.iter Lexer.add_keyword vernac_kw

(* Rem: do not join the different GEXTEND into one, it breaks native *)
(* compilation on PowerPC and Sun architectures *)

let check_command = Gram.entry_create "vernac:check_command"

let tactic_mode = Gram.entry_create "vernac:tactic_command"
let noedit_mode = Gram.entry_create "vernac:noedit_command"
let bullet = Gram.entry_create "vernac:bullet"

let class_rawexpr = Gram.entry_create "vernac:class_rawexpr"
let thm_token = Gram.entry_create "vernac:thm_token"
let def_body = Gram.entry_create "vernac:def_body"
let decl_notation = Gram.entry_create "vernac:decl_notation"
let typeclass_context = Gram.entry_create "vernac:typeclass_context"
let record_field = Gram.entry_create "vernac:record_field"
let of_type_with_opt_coercion = Gram.entry_create "vernac:of_type_with_opt_coercion"
let subgoal_command = Gram.entry_create "proof_mode:subgoal_command"
let instance_name = Gram.entry_create "vernac:instance_name"

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

let default_command_entry =
  Gram.Entry.of_parser "command_entry"
    (fun strm -> Gram.parse_tokens_after_filter (get_command_entry ()) strm)

let no_hook _ _ = ()
GEXTEND Gram
  GLOBAL: vernac gallina_ext tactic_mode noedit_mode bullet subgoal_command;
  vernac: FIRST
    [ [ IDENT "Time"; v = vernac -> VernacTime v
      | IDENT "Timeout"; n = natural; v = vernac -> VernacTimeout(n,v)
      | IDENT "Fail"; v = vernac -> VernacFail v
      | locality; v = vernac_aux -> v ] ]
  ;
  vernac_aux:
    (* Better to parse "." here: in case of failure (e.g. in coerce_to_var), *)
    (* "." is still in the stream and discard_to_dot works correctly         *)
    [ [ g = gallina; "." -> g
      | g = gallina_ext; "." -> g
      | c = command; "." -> c
      | c = syntax; "." -> c
      | "["; l = LIST1 located_vernac; "]"; "." -> VernacList l
    ] ]
  ;
  vernac_aux: LAST
    [ [ prfcom = default_command_entry -> prfcom ] ]
  ;
  locality:
    [ [ IDENT "Local" -> locality_flag := Some (loc,true)
      | IDENT "Global" -> locality_flag := Some (loc,false)
      | -> locality_flag := None ] ]
  ;
  noedit_mode:
    [ [ c = subgoal_command -> c None None] ]
  ;
  tactic_mode:
  [ [ gln = OPT[n=natural; ":" -> n];
      tac = subgoal_command -> tac gln None 
    | b = bullet; tac = subgoal_command -> tac None (Some b)] ]
  ;
  bullet:
  [ [ "-" -> Dash
    | "*" -> Star
    | "+" -> Plus ] ]
  ;
  subgoal_command: 
    [ [ c = check_command; "." -> fun g _ -> c g
      | tac = Tactic.tactic;
        use_dft_tac = [ "." -> false | "..." -> true ] ->
          (fun g b ->
            let g = Option.default 1 g in
            VernacSolve(g,b,tac,use_dft_tac)) ] ]
  ;
  located_vernac:
    [ [ v = vernac -> loc, v ] ]
  ;
END

let test_plurial_form = function
  | [(_,([_],_))] ->
      Flags.if_verbose warning
   "Keywords Variables/Hypotheses/Parameters expect more than one assumption"
  | _ -> ()

let test_plurial_form_types = function
  | [([_],_)] ->
      Flags.if_verbose warning
   "Keywords Implicit Types expect more than one type"
  | _ -> ()

(* Gallina declarations *)
GEXTEND Gram
  GLOBAL: gallina gallina_ext thm_token def_body of_type_with_opt_coercion
    typeclass_context typeclass_constraint record_field decl_notation rec_definition;

  gallina:
      (* Definition, Theorem, Variable, Axiom, ... *)
    [ [ thm = thm_token; id = identref; bl = binders; ":"; c = lconstr;
        l = LIST0
          [ "with"; id = identref; bl = binders; ":"; c = lconstr ->
            (Some id,(bl,c,None)) ] ->
          VernacStartTheoremProof (thm,(Some id,(bl,c,None))::l, false, no_hook)
      | stre = assumption_token; nl = inline; bl = assum_list ->
	  VernacAssumption (stre, nl, bl)
      | stre = assumptions_token; nl = inline; bl = assum_list ->
	  test_plurial_form bl;
	  VernacAssumption (stre, nl, bl)
      | IDENT "Boxed";"Definition";id = identref; b = def_body ->
	  VernacDefinition ((Global,true,Definition), id, b, no_hook)
      | IDENT "Unboxed";"Definition";id = identref; b = def_body ->
	  VernacDefinition ((Global,false,Definition), id, b, no_hook)
      | (f,d) = def_token; id = identref; b = def_body ->
          VernacDefinition (d, id, b, f)
      (* Gallina inductive declarations *)
      | f = finite_token;
        indl = LIST1 inductive_definition SEP "with" ->
	  let (k,f) = f in
	  let indl=List.map (fun ((a,b,c,d),e) -> ((a,b,c,k,d),e)) indl in
          VernacInductive (f,false,indl)
      | IDENT "Boxed";"Fixpoint"; recs = LIST1 rec_definition SEP "with" ->
          VernacFixpoint (recs,true)
      | IDENT "Unboxed";"Fixpoint"; recs = LIST1 rec_definition SEP "with" ->
          VernacFixpoint (recs,false)
       | "Fixpoint"; recs = LIST1 rec_definition SEP "with" ->
          VernacFixpoint (recs,Flags.boxed_definitions())
      | "CoFixpoint"; corecs = LIST1 corec_definition SEP "with" ->
          VernacCoFixpoint (corecs,false)
      | IDENT "Scheme"; l = LIST1 scheme SEP "with" -> VernacScheme l
      | IDENT "Combined"; IDENT "Scheme"; id = identref; IDENT "from";
	l = LIST1 identref SEP "," -> VernacCombinedScheme (id, l)
      | IDENT "RegisterInd";id=identref; "as"; r = register_ind_token ->
        VernacRegister(id,PrimInd r) 
      | IDENT "Register"; id=identref; ":"; t = lconstr; "as"; 
        r = register_token ->
         VernacRegister(id,PrimOp(t,r)) 
      | IDENT "Register"; id = identref; "as"; "Inline" ->
         VernacRegister(id,PrimInline)
     ] ]
  ;

  gallina_ext:
    [ [ b = record_token; infer = infer_token; oc = opt_coercion; name = identref;
        ps = binders;
	s = OPT [ ":"; s = lconstr -> s ];
	cfs = [ ":="; l = constructor_list_or_record_decl -> l
	  | -> RecordDecl (None, []) ] ->
	  let (recf,indf) = b in
	    VernacInductive (indf,infer,[((oc,name),ps,s,recf,cfs),[]])
  ] ]
  ;
  typeclass_context:
    [ [ "["; l=LIST1 typeclass_constraint SEP ","; "]" -> l
    | -> [] ] ]
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
    [ [ "Definition" ->
	no_hook, (Global, Flags.boxed_definitions(), Definition)
      | IDENT "Let" ->
	no_hook, (Local, Flags.boxed_definitions(), Definition)
      | IDENT "Example" ->
	no_hook, (Global, Flags.boxed_definitions(), Example)
      | IDENT "SubClass"  ->
          Class.add_subclass_hook, (use_locality_exp (), false, SubClass) ] ]
  ;
  assumption_token:
    [ [ "Hypothesis" -> (Local, Logical)
      | "Variable" -> (Local, Definitional)
      | "Axiom" -> (Global, Logical)
      | "Parameter" -> (Global, Definitional)
      | IDENT "Conjecture" -> (Global, Conjectural) ] ]
  ;
  assumptions_token:
    [ [ IDENT "Hypotheses" -> (Local, Logical)
      | IDENT "Variables" -> (Local, Definitional)
      | IDENT "Axioms" -> (Global, Logical)
      | IDENT "Parameters" -> (Global, Definitional) ] ]
  ;
 
 
  register_ind_token:
    [ [ "ind_bool" -> Native.PIT_bool
      | "ind_carry" -> Native.PIT_carry
      | "ind_pair" -> Native.PIT_pair
      | "ind_cmp" -> Native.PIT_cmp 
      | "ind_eq"  -> Native.PIT_eq] ]
  ;

  register_token:
    [ [ r = register_prim_token -> Native.OT_op r 
      | r = register_type_token -> Native.OT_type r ] ]
  ;
  
  register_type_token:
    [ [ "int31_type" -> Native.PT_int31  
      | "array_type" -> Native.PT_array ] ]
  ;

  register_prim_token:
    [ [ "int31_print" -> Native.Ocaml_prim Native.Int31print
      | "array_make" -> Native.Ocaml_prim Native.ArrayMake
      | "array_get" -> Native.Ocaml_prim Native.ArrayGet
      | "array_default" -> Native.Ocaml_prim Native.ArrayGetdefault
      | "array_set" -> Native.Ocaml_prim Native.ArraySet
      | "array_copy" -> Native.Ocaml_prim Native.ArrayCopy
      | "array_reroot" -> Native.Ocaml_prim Native.ArrayReroot
      | "array_length" -> Native.Ocaml_prim Native.ArrayLength
     
      | "int31_foldi" -> Native.Oiterator Native.Int31foldi
      | "int31_foldi_down" -> Native.Oiterator Native.Int31foldi_down

      | "int31_head0" -> Native.Oprim Native.Int31head0
      | "int31_tail0" -> Native.Oprim Native.Int31tail0
      | "int31_add" -> Native.Oprim Native. Int31add
      | "int31_sub" -> Native.Oprim Native.Int31sub
      | "int31_mul" -> Native.Oprim Native.Int31mul
      | "int31_div" -> Native.Oprim Native.Int31div
      | "int31_mod" -> Native.Oprim Native.Int31mod
      | "int31_lsr" -> Native.Oprim Native.Int31lsr
      | "int31_lsl" -> Native.Oprim Native.Int31lsl
      | "int31_land" -> Native.Oprim Native.Int31land
      | "int31_lor" -> Native.Oprim Native.Int31lor
      | "int31_lxor" -> Native.Oprim Native.Int31lxor
      | "int31_addc" -> Native.Oprim Native.Int31addc
      | "int31_subc" -> Native.Oprim Native.Int31subc
      | "int31_addcarryc" -> Native.Oprim Native.Int31addCarryC
      | "int31_subcarryc" -> Native.Oprim Native.Int31subCarryC
      | "int31_mulc" -> Native.Oprim Native.Int31mulc
      | "int31_diveucl" -> Native.Oprim Native.Int31diveucl
      | "int31_div21" -> Native.Oprim Native.Int31div21
      | "int31_addmuldiv" -> Native.Oprim Native.Int31addMulDiv
      | "int31_eq" -> Native.Oprim Native.Int31eq
      | "int31_lt" -> Native.Oprim Native.Int31lt
      | "int31_le" -> Native.Oprim Native.Int31le
      | "int31_compare" -> Native.Oprim Native.Int31compare 
      | "int31_eqb_correct" ->  Native.Oprim Native.Int31eqb_correct] ]
    ;

  inline:
    [ ["Inline" -> true |  -> false] ]
  ;
  finite_token:
    [ [ "Inductive" -> (Inductive_kw,Finite)
      | "CoInductive" -> (CoInductive,CoFinite) ] ]
  ;
  infer_token:
    [ [ IDENT "Infer" -> true | -> false ] ]
  ;
  record_token:
    [ [ IDENT "Record" -> (Record,BiFinite)
      | IDENT "Structure" -> (Structure,BiFinite)
      | IDENT "Class" -> (Class true,BiFinite) ] ]
  ;
  (* Simple definitions *)
  def_body:
    [ [ bl = binders; ":="; red = reduce; c = lconstr ->
      (match c with
          CCast(_,c, Rawterm.CastConv (k,t)) -> DefineBody (bl, red, c, Some t)
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
  inductive_definition:
    [ [ id = identref; oc = opt_coercion; indpar = binders;
        c = OPT [ ":"; c = lconstr -> c ];
        ":="; lc = constructor_list_or_record_decl; ntn = decl_notation ->
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
      | -> CHole (loc, None) ] ]
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
    [ [ bd = record_binder; ntn = decl_notation -> bd,ntn ] ]
  ;
  record_binder_body:
    [ [ l = binders; oc = of_type_with_opt_coercion;
         t = lconstr -> fun id -> (oc,AssumExpr (id,mkCProdN loc l t))
      | l = binders; oc = of_type_with_opt_coercion;
         t = lconstr; ":="; b = lconstr -> fun id ->
	   (oc,DefExpr (id,mkCLambdaN loc l b,Some (mkCProdN loc l t)))
      | l = binders; ":="; b = lconstr -> fun id ->
         match b with
	 | CCast(_,b, Rawterm.CastConv (_, t)) ->
	     (false,DefExpr(id,mkCLambdaN loc l b,Some (mkCProdN loc l t)))
         | _ ->
	     (false,DefExpr(id,mkCLambdaN loc l b,None)) ] ]
  ;
  record_binder:
    [ [ id = name -> (false,AssumExpr(id,CHole (loc, None)))
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
        (oc,(idl,c)) ] ]
  ;

  constructor_type:
    [[ l = binders;
      t= [ coe = of_type_with_opt_coercion; c = lconstr ->
	            fun l id -> (coe,(id,mkCProdN loc l c))
            |  ->
		 fun l id -> (false,(id,mkCProdN loc l (CHole (loc, None)))) ]
	 -> t l
     ]]
;

  constructor:
    [ [ id = identref; c=constructor_type -> c id ] ]
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

      (* Requiring an already compiled module *)
      | IDENT "Require"; export = export_token; qidl = LIST1 global ->
          VernacRequire (export, None, qidl)
      | IDENT "Require"; export = export_token; filename = ne_string ->
	  VernacRequireFrom (export, None, filename)
      | IDENT "Import"; qidl = LIST1 global -> VernacImport (false,qidl)
      | IDENT "Export"; qidl = LIST1 global -> VernacImport (true,qidl)
      | IDENT "Include"; e = module_expr_inl; l = LIST0 ext_module_expr ->
	  VernacInclude(e::l)
      | IDENT "Include"; "Type"; e = module_type_inl; l = LIST0 ext_module_type ->
	  warning "Include Type is deprecated; use Include instead";
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
  module_expr_inl:
    [ [ "!"; me = module_expr -> (me,false)
      | me = module_expr -> (me,true) ] ]
  ;
  module_type_inl:
    [ [ "!"; me = module_type -> (me,false)
      | me = module_type -> (me,true) ] ]
  ;
  (* Module binder  *)
  module_binder:
    [ [ "("; export = export_token; idl = LIST1 identref; ":";
         mty = module_type_inl; ")" -> (export,idl,mty) ] ]
  ;
  (* Module expressions *)
  module_expr:
    [ [ me = module_expr_atom -> me
      | me1 = module_expr; me2 = module_expr_atom -> CMapply (me1,me2)
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
      | mty = module_type; me = module_expr_atom -> CMapply (mty,me)
      | mty = module_type; "with"; decl = with_declaration -> CMwith (mty,decl)
      ] ]
  ;
END

(* Extensions: implicits, coercions, etc. *)
GEXTEND Gram
  GLOBAL: gallina_ext instance_name;

  gallina_ext:
    [ [ (* Transparent and Opaque *)
        IDENT "Transparent"; l = LIST1 smart_global ->
          VernacSetOpacity (use_non_locality (),[Conv_oracle.transparent,l])
      | IDENT "Opaque"; l = LIST1 smart_global ->
          VernacSetOpacity (use_non_locality (),[Conv_oracle.Opaque, l])
      | IDENT "Strategy"; l =
          LIST1 [ lev=strategy_level; "["; q=LIST1 smart_global; "]" -> (lev,q)] ->
            VernacSetOpacity (use_locality (),l)
      (* Canonical structure *)
      | IDENT "Canonical"; IDENT "Structure"; qid = global ->
	  VernacCanonical (AN qid)
      | IDENT "Canonical"; IDENT "Structure"; ntn = by_notation ->
	  VernacCanonical (ByNotation ntn)
      | IDENT "Canonical"; IDENT "Structure"; qid = global;
          d = def_body ->
          let s = coerce_reference_to_id qid in
	  VernacDefinition
	    ((Global,false,CanonicalStructure),(dummy_loc,s),d,
	     (fun _ -> Recordops.declare_canonical_structure))

      (* Coercions *)
      | IDENT "Coercion"; qid = global; d = def_body ->
          let s = coerce_reference_to_id qid in
	  VernacDefinition ((use_locality_exp (),false,Coercion),(dummy_loc,s),d,Class.add_coercion_hook)
      | IDENT "Coercion"; IDENT "Local"; qid = global; d = def_body ->
           let s = coerce_reference_to_id qid in
	  VernacDefinition ((enforce_locality_exp true,false,Coercion),(dummy_loc,s),d,Class.add_coercion_hook)
      | IDENT "Identity"; IDENT "Coercion"; IDENT "Local"; f = identref;
         ":"; s = class_rawexpr; ">->"; t = class_rawexpr ->
	   VernacIdentityCoercion (enforce_locality_exp true, f, s, t)
      | IDENT "Identity"; IDENT "Coercion"; f = identref; ":";
         s = class_rawexpr; ">->"; t = class_rawexpr ->
	   VernacIdentityCoercion (use_locality_exp (), f, s, t)
      | IDENT "Coercion"; IDENT "Local"; qid = global; ":";
	 s = class_rawexpr; ">->"; t = class_rawexpr ->
	  VernacCoercion (enforce_locality_exp true, AN qid, s, t)
      | IDENT "Coercion"; IDENT "Local"; ntn = by_notation; ":";
	 s = class_rawexpr; ">->"; t = class_rawexpr ->
	  VernacCoercion (enforce_locality_exp true, ByNotation ntn, s, t)
      | IDENT "Coercion"; qid = global; ":"; s = class_rawexpr; ">->";
         t = class_rawexpr ->
	  VernacCoercion (use_locality_exp (), AN qid, s, t)
      | IDENT "Coercion"; ntn = by_notation; ":"; s = class_rawexpr; ">->";
         t = class_rawexpr ->
	  VernacCoercion (use_locality_exp (), ByNotation ntn, s, t)

      | IDENT "Context"; c = binders ->
	  VernacContext c

      | IDENT "Instance"; namesup = instance_name; ":";
	 expl = [ "!" -> Rawterm.Implicit | -> Rawterm.Explicit ] ; t = operconstr LEVEL "200";
	 pri = OPT [ "|"; i = natural -> i ] ;
	 props = [ ":="; "{"; r = record_declaration; "}" -> r |
	     ":="; c = lconstr -> c | -> CRecord (loc, None, []) ] ->
	   VernacInstance (false, not (use_non_locality ()),
			   snd namesup, (fst namesup, expl, t), props, pri)

      | IDENT "Existing"; IDENT "Instance"; is = global -> 
	  VernacDeclareInstance (not (use_section_locality ()), is)

      | IDENT "Existing"; IDENT "Class"; is = global -> VernacDeclareClass is

      (* Implicit *)
      | IDENT "Implicit"; IDENT "Arguments"; qid = smart_global;
	   pos = LIST0 [ "["; l = LIST0 implicit_name; "]" ->
	     List.map (fun (id,b,f) -> (ExplByName id,b,f)) l ] ->
	   VernacDeclareImplicits (use_section_locality (),qid,pos)

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
	     VernacGeneralizable (use_non_locality (), gen) ] ]
  ;
  implicit_name:
    [ [ "!"; id = ident -> (id, false, true)
    | id = ident -> (id,false,false)
    | "["; "!"; id = ident; "]" -> (id,true,true)
    | "["; id = ident; "]" -> (id,true, false) ] ]
  ;
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
      | -> (loc, Anonymous), []  ] ]
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
  GLOBAL: command check_command class_rawexpr;

  command:
    [ [ IDENT "Comments"; l = LIST0 comment -> VernacComments l

      (* Hack! Should be in grammar_ext, but camlp4 factorize badly *)
      | IDENT "Declare"; IDENT "Instance"; namesup = instance_name; ":";
	 expl = [ "!" -> Rawterm.Implicit | -> Rawterm.Explicit ] ; t = operconstr LEVEL "200";
	 pri = OPT [ "|"; i = natural -> i ] ->
	   VernacInstance (true, not (use_non_locality ()),
			   snd namesup, (fst namesup, expl, t),
			   CRecord (loc, None, []), pri)

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
	  VernacDeclareMLModule (use_locality (), l)

      | IDENT "Dump"; IDENT "Universes"; fopt = OPT ne_string ->
	  error "This command is deprecated, use Print Universes"

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
      | IDENT "Inspect"; n = natural -> VernacPrint (PrintInspect n)
      | IDENT "About"; qid = smart_global -> VernacPrint (PrintAbout qid)

      (* Searching the environment *)
      | IDENT "Search"; c = constr_pattern; l = in_or_out_modules ->
	  VernacSearch (SearchHead c, l)
      | IDENT "SearchPattern"; c = constr_pattern; l = in_or_out_modules ->
	  VernacSearch (SearchPattern c, l)
      | IDENT "SearchRewrite"; c = constr_pattern; l = in_or_out_modules ->
	  VernacSearch (SearchRewrite c, l)
      | IDENT "SearchAbout";
	  sl = [ "[";
	         l = LIST1 [
		   b = positive_search_mark; s = ne_string; sc = OPT scope
		   -> b, SearchString (s,sc)
		 | b = positive_search_mark; p = constr_pattern
		   -> b, SearchSubPattern p
		 ]; "]" -> l
   	       | p = constr_pattern -> [true,SearchSubPattern p]
   	       | s = ne_string; sc = OPT scope -> [true,SearchString (s,sc)] ];
	  l = in_or_out_modules ->
	  VernacSearch (SearchAbout sl, l)

      | IDENT "Add"; IDENT "ML"; IDENT "Path"; dir = ne_string ->
	  VernacAddMLPath (false, dir)
      | IDENT "Add"; IDENT "Rec"; IDENT "ML"; IDENT "Path"; dir = ne_string ->
	  VernacAddMLPath (true, dir)

      (* Pour intervenir sur les tables de param��tres *)
      | "Set"; table = option_table; v = option_value ->
  	  VernacSetOption (use_locality_full(),table,v)
      | "Set"; table = option_table ->
  	  VernacSetOption (use_locality_full(),table,BoolValue true)
      | IDENT "Unset"; table = option_table ->
  	  VernacUnsetOption (use_locality_full(),table)

      | IDENT "Print"; IDENT "Table"; table = option_table ->
	  VernacPrintOption table

      | IDENT "Add"; table = IDENT; field = IDENT; v = LIST1 option_ref_value
        -> VernacAddOption ([table;field], v)
      (* Un value global ci-dessous va ��tre cach�� par un field au dessus! *)
      (* En fait, on donne priorit�� aux tables secondaires *)
      (* Pas de syntaxe pour les tables tertiaires pour cause de conflit *)
      (* (mais de toutes fa��ons, pas utilis��es) *)
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
  check_command: (* TODO: rapprocher Eval et Check *)
    [ [ IDENT "Eval"; r = Tactic.red_expr; "in"; c = lconstr ->
          fun g -> VernacCheckMayEval (Some r, g, c)
      | IDENT "Compute"; c = lconstr ->
	  fun g -> VernacCheckMayEval (Some Rawterm.CbvVm, g, c)
      | IDENT "Check"; c = lconstr ->
	  fun g -> VernacCheckMayEval (None, g, c) ] ]
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
      | IDENT "Hint" -> PrintHintGoal
      | IDENT "Hint"; qid = smart_global -> PrintHint qid
      | IDENT "Hint"; "*" -> PrintHintDb
      | IDENT "HintDb"; s = IDENT -> PrintHintDbName s
      | "Rewrite"; IDENT "HintDb"; s = IDENT -> PrintRewriteHintDbName s
      | IDENT "Scopes" -> PrintScopes
      | IDENT "Scope"; s = IDENT -> PrintScope s
      | IDENT "Visibility"; s = OPT [x = IDENT -> x ] -> PrintVisibility s
      | IDENT "Implicit"; qid = smart_global -> PrintImplicit qid
      | IDENT "Universes"; fopt = OPT ne_string -> PrintUniverses fopt
      | IDENT "Assumptions"; qid = smart_global -> PrintAssumptions (false, qid)
      | IDENT "Opaque"; IDENT "Dependencies"; qid = smart_global -> PrintAssumptions (true, qid) ] ]
  ;
  class_rawexpr:
    [ [ IDENT "Funclass" -> FunClass
      | IDENT "Sortclass" -> SortClass
      | qid = smart_global -> RefClass qid ] ]
  ;
  locatable:
    [ [ qid = smart_global -> LocateTerm qid
      | IDENT "File"; f = ne_string -> LocateFile f
      | IDENT "Library"; qid = global -> LocateLibrary qid
      | IDENT "Module"; qid = global -> LocateModule qid
      | IDENT "Ltac"; qid = global -> LocateTactic qid ] ]
  ;
  option_value:
    [ [ n  = integer   -> IntValue n
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
  positive_search_mark:
    [ [ "-" -> false | -> true ] ]
  ;
  scope:
    [ [ "%"; key = IDENT -> key ] ]
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
      | IDENT "Reset"; id = identref -> VernacResetName id
      | IDENT "Delete"; id = identref -> VernacRemoveName id
      | IDENT "Reset"; IDENT "Initial" -> VernacResetInitial
      | IDENT "Back" -> VernacBack 1
      | IDENT "Back"; n = natural -> VernacBack n
      | IDENT "BackTo"; n = natural -> VernacBackTo n
      | IDENT "Backtrack"; n = natural ; m = natural ; p = natural ->
	  VernacBacktrack (n,m,p)

(* Tactic Debugger *)
      |	IDENT "Debug"; IDENT "On" ->
          VernacSetOption (None,["Ltac";"Debug"], BoolValue true)

      |	IDENT "Debug"; IDENT "Off" ->
          VernacSetOption (None,["Ltac";"Debug"], BoolValue false)

(* registration of a custom reduction *)

      | IDENT "Declare"; IDENT "Reduction"; s = IDENT; ":=";
         r = Tactic.red_expr ->
	   VernacDeclareReduction (use_locality(),s,r)

 ] ];
    END
;;

(* Grammar extensions *)

GEXTEND Gram
  GLOBAL: syntax;

  syntax:
   [ [ IDENT "Open"; local = obsolete_locality; IDENT "Scope"; sc = IDENT ->
         VernacOpenCloseScope (enforce_section_locality local,true,sc)

     | IDENT "Close"; local = obsolete_locality; IDENT "Scope"; sc = IDENT ->
         VernacOpenCloseScope (enforce_section_locality local,false,sc)

     | IDENT "Delimit"; IDENT "Scope"; sc = IDENT; "with"; key = IDENT ->
	 VernacDelimiters (sc,key)

     | IDENT "Bind"; IDENT "Scope"; sc = IDENT; "with";
       refl = LIST1 class_rawexpr -> VernacBindScope (sc,refl)

     | IDENT "Arguments"; IDENT "Scope"; qid = smart_global;
       "["; scl = LIST0 opt_scope; "]" ->
	 VernacArgumentsScope (use_section_locality (),qid,scl)

     | IDENT "Infix"; local = obsolete_locality;
	 op = ne_lstring; ":="; p = constr;
         modl = [ "("; l = LIST1 syntax_modifier SEP ","; ")" -> l | -> [] ];
	 sc = OPT [ ":"; sc = IDENT -> sc ] ->
         VernacInfix (enforce_module_locality local,(op,modl),p,sc)
     | IDENT "Notation"; local = obsolete_locality; id = identref;
	 idl = LIST0 ident; ":="; c = constr;
	 b = [ "("; IDENT "only"; IDENT "parsing"; ")" -> true | -> false ] ->
           VernacSyntacticDefinition
	     (id,(idl,c),enforce_module_locality local,b)
     | IDENT "Notation"; local = obsolete_locality; s = ne_lstring; ":=";
	 c = constr;
         modl = [ "("; l = LIST1 syntax_modifier SEP ","; ")" -> l | -> [] ];
	 sc = OPT [ ":"; sc = IDENT -> sc ] ->
           VernacNotation (enforce_module_locality local,c,(s,modl),sc)

     | IDENT "Tactic"; IDENT "Notation"; n = tactic_level;
	 pil = LIST1 production_item; ":="; t = Tactic.tactic
         -> VernacTacticNotation (n,pil,t)

     | IDENT "Reserved"; IDENT "Infix"; s = ne_lstring;
	 l = [ "("; l = LIST1 syntax_modifier SEP ","; ")" -> l | -> [] ] ->
	   Metasyntax.check_infix_modifiers l;
	   let (loc,s) = s in
	   VernacSyntaxExtension (use_module_locality(),((loc,"x '"^s^"' y"),l))

     | IDENT "Reserved"; IDENT "Notation"; local = obsolete_locality;
	 s = ne_lstring;
	 l = [ "("; l = LIST1 syntax_modifier SEP ","; ")" -> l | -> [] ]
	 -> VernacSyntaxExtension (enforce_module_locality local,(s,l))

     (* "Print" "Grammar" should be here but is in "command" entry in order
        to factorize with other "Print"-based vernac entries *)
  ] ]
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
      | IDENT "only"; IDENT "parsing" -> SetOnlyParsing
      | IDENT "format"; s = [s = STRING -> (loc,s)] -> SetFormat s
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
  opt_scope:
    [ [ "_" -> None | sc = IDENT -> Some sc ] ]
  ;
  production_item:
    [ [ s = ne_string -> TacTerm s
      | nt = IDENT;
        po = OPT [ "("; p = ident; sep = [ -> "" | ","; sep = STRING -> sep ];
                   ")" -> (p,sep) ] -> TacNonTerm (loc,nt,po) ] ]
  ;
END
