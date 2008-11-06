(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4deps: "parsing/grammar.cma" i*)
(*i camlp4use: "pa_extend.cmo" i*)

(* $Id$ *)


open Pp
open Util
open Names
open Topconstr
open Vernacexpr
open Pcoq
open Decl_mode
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

let vernac_kw = [ ";"; ","; ">->"; ":<"; "<:"; "where"; "at" ]
let _ = List.iter (fun s -> Lexer.add_token ("",s)) vernac_kw

(* Rem: do not join the different GEXTEND into one, it breaks native *)
(* compilation on PowerPC and Sun architectures *)

let check_command = Gram.Entry.create "vernac:check_command"

let tactic_mode = Gram.Entry.create "vernac:tactic_command"
let proof_mode = Gram.Entry.create "vernac:proof_command"
let noedit_mode = Gram.Entry.create "vernac:noedit_command"

let class_rawexpr = Gram.Entry.create "vernac:class_rawexpr"
let thm_token = Gram.Entry.create "vernac:thm_token"
let def_body = Gram.Entry.create "vernac:def_body"
let typeclass_context = Gram.Entry.create "vernac:typeclass_context"
let of_type_with_opt_coercion = Gram.Entry.create "vernac:of_type_with_opt_coercion"

let get_command_entry () =
  match Decl_mode.get_current_mode () with
      Mode_proof -> proof_mode
    | Mode_tactic -> tactic_mode
    | Mode_none -> noedit_mode

let default_command_entry =
  Gram.Entry.of_parser "command_entry" 
    (fun strm -> Gram.Entry.parse_token (get_command_entry ()) strm)

let no_hook _ _ = ()
GEXTEND Gram
  GLOBAL: vernac gallina_ext tactic_mode proof_mode noedit_mode;
  vernac:
    (* Better to parse "." here: in case of failure (e.g. in coerce_to_var), *)
    (* "." is still in the stream and discard_to_dot works correctly         *)
    [ [ g = gallina; "." -> g 
      | g = gallina_ext; "." -> g
      | c = command; "." -> c 
      | c = syntax; "." -> c
      | "["; l = LIST1 located_vernac; "]"; "." -> VernacList l
    ] ]
  ;
  vernac: FIRST
    [ [ IDENT "Time"; v = vernac  -> VernacTime v ] ]
  ;
  vernac: LAST  
    [ [ prfcom = default_command_entry -> prfcom ] ]
  ;
  noedit_mode:
    [ [ c = subgoal_command -> c None] ]
  ;
  tactic_mode:
  [ [ gln = OPT[n=natural; ":" -> n];
      tac = subgoal_command -> tac gln ] ]
  ;
  subgoal_command:
    [ [ c = check_command; "." -> c
      | tac = Tactic.tactic;
        use_dft_tac = [ "." -> false | "..." -> true ] ->
          (fun g ->
            let g = match g with Some gl -> gl | _ -> 1 in
            VernacSolve(g,tac,use_dft_tac)) ] ]
  ;
  proof_mode:
    [ [ instr = proof_instr; "." -> VernacProofInstr instr ] ] 
  ;
  proof_mode: LAST
    [ [ c=subgoal_command -> c (Some 1) ] ]
  ; 
  located_vernac:
    [ [ v = vernac -> loc, v ] ]
  ;
END

GEXTEND Gram
  GLOBAL: locality non_locality;
  locality:
    [ [ IDENT "Global" -> false | IDENT "Local" -> true | -> false ] ]
  ;
  non_locality:
    [ [ IDENT "Global" -> false | IDENT "Local" -> true | -> true ] ]
  ;
END

let test_plurial_form = function
  | [(_,([_],_))] ->
      Flags.if_verbose warning
   "Keywords Variables/Hypotheses/Parameters expect more than one assumption"
  | _ -> ()

let no_coercion loc (c,x) =
  if c then Util.user_err_loc
    (loc,"no_coercion",str"No coercion allowed here.");
  x

(* Gallina declarations *)
GEXTEND Gram
  GLOBAL: gallina gallina_ext thm_token def_body of_type_with_opt_coercion
    typeclass_context typeclass_constraint;

  gallina:
      (* Definition, Theorem, Variable, Axiom, ... *)
    [ [ thm = thm_token; id = identref; bl = binders_let; ":"; c = lconstr;
        l = LIST0 
          [ "with"; id = identref; bl = binders_let; ":"; c = lconstr ->
            (Some id,(bl,c)) ] ->
          VernacStartTheoremProof (thm,(Some id,(bl,c))::l, false, no_hook)
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
          VernacInductive (f,indl)
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
	l = LIST1 identref SEP "," -> VernacCombinedScheme (id, l) ] ]
  ;
  gallina_ext:
    [ [ b = record_token; oc = opt_coercion; name = identref;
        ps = binders_let; 
	s = [ ":"; s = lconstr -> s | -> CSort (loc,Rawterm.RType None) ];
	":="; cstr = OPT identref; "{";
        fs = LIST0 record_field SEP ";"; "}" ->
	  VernacRecord (b,(oc,name),ps,s,cstr,fs)
(* Non porté ?
      | f = finite_token; s = csort; id = identref;
        indpar = LIST0 simple_binder; ":="; lc = constructor_list -> 
          VernacInductive (f,[id,None,indpar,s,lc])
*)
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
      | IDENT "SubClass"  -> Class.add_subclass_hook, (Global, false, SubClass)
      | IDENT "Local"; IDENT "SubClass"  ->
          Class.add_subclass_hook, (Local, false, SubClass) ] ] 
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
  inline:
    [ ["Inline" -> true |  -> false] ]
  ;
  finite_token:
    [ [ "Inductive" -> true
      | "CoInductive" -> false ] ]
  ;
  record_token:
    [ [ IDENT "Record" -> (true,true) | IDENT "Structure" -> (false,true) ]]
  ;
  (* Simple definitions *)
  def_body:
    [ [ bl = binders_let; ":="; red = reduce; c = lconstr ->
      (match c with
          CCast(_,c, Rawterm.CastConv (k,t)) -> DefineBody (bl, red, c, Some t)
        | _ -> DefineBody (bl, red, c, None))
    | bl = binders_let; ":"; t = lconstr; ":="; red = reduce; c = lconstr ->
	DefineBody (bl, red, c, Some t)
    | bl = binders_let; ":"; t = lconstr ->
        ProveBody (bl, t) ] ]
  ;
  reduce:
    [ [ IDENT "Eval"; r = Tactic.red_expr; "in" -> Some r
      | -> None ] ]
  ;
  decl_notation:
    [ [ OPT [ "where"; ntn = ne_string; ":="; c = constr; 
         scopt = OPT [ ":"; sc = IDENT -> sc] -> (ntn,c,scopt) ] ] ]
    ;
  (* Inductives and records *)
  inductive_definition:
    [ [ id = identref; indpar = binders_let; 
        c = [ ":"; c = lconstr -> c | -> CSort (loc,Rawterm.RType None) ];
        ":="; lc = constructor_list_or_record_decl; ntn = decl_notation ->
	   ((id,indpar,c,lc),ntn) ] ]
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
	bl = binders_let_fixannot;
        ty = type_cstr; 
	":="; def = lconstr; ntn = decl_notation ->
	  let bl, annot = bl in
          let names = names_of_local_assums bl in
          let ni =
            match fst annot with
                Some (loc, id) ->
                  (if List.exists (fun (_, id') -> Name id = id') names then
		    Some (loc, id)
		    else Util.user_err_loc
                      (loc,"Fixpoint",
                       str "No argument named " ++ Nameops.pr_id id ++ str"."))
              | None -> 
		  (* If there is only one argument, it is the recursive one, 
		     otherwise, we search the recursive index later *)
		  match names with
		    | [(loc, Name na)] -> Some (loc, na)
		    | _ -> None	  
	  in 
	  ((id,(ni,snd annot),bl,ty,def),ntn) ] ]
  ;
  corec_definition:
    [ [ id = identref; bl = binders_let; ty = type_cstr; ":=";
        def = lconstr; ntn = decl_notation ->
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
    [ [ IDENT "Induction"; "for"; ind = global;
          IDENT "Sort"; s = sort-> InductionScheme(true,ind,s)
      | IDENT "Minimality"; "for"; ind = global;
          IDENT "Sort"; s = sort-> InductionScheme(false,ind,s)
      | IDENT "Equality"; "for" ; ind = global -> EqualityScheme(ind)  ] ]
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
    [ [ id = name -> (false,AssumExpr(id,CHole (loc, None)))
      | id = name; oc = of_type_with_opt_coercion; t = lconstr ->
         (oc,AssumExpr (id,t))
      | id = name; oc = of_type_with_opt_coercion;
             t = lconstr; ":="; b = lconstr -> (oc,DefExpr (id,b,Some t))
      | id = name; ":="; b = lconstr ->
         match b with
             CCast(_,b, Rawterm.CastConv (_, t)) -> (false,DefExpr(id,b,Some t))
           | _ -> (false,DefExpr(id,b,None)) ] ]
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
    [[ l = binders_let; 
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
	bl = LIST0 module_binder; mty_o = OPT of_module_type; 
	mexpr_o = OPT is_module_expr ->
	  VernacDefineModule (export, id, bl, mty_o, mexpr_o)
	  
      | IDENT "Module"; "Type"; id = identref; 
	bl = LIST0 module_binder; mty_o = OPT is_module_type ->
	  VernacDeclareModuleType (id, bl, mty_o)
	  
      | IDENT "Declare"; IDENT "Module"; export = export_token; id = identref; 
	bl = LIST0 module_binder; ":"; mty = module_type ->
	  VernacDeclareModule (export, id, bl, (mty,true))
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
      | IDENT "Include"; expr = module_expr -> VernacInclude(CIME(expr))
      | IDENT "Include"; "Type"; expr = module_type -> VernacInclude(CIMTE(expr)) ] ]
  ;
  export_token:
    [ [ IDENT "Import" -> Some false
      | IDENT "Export" -> Some true
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
    [ [ "("; export = export_token; idl = LIST1 identref; ":";
         mty = module_type; ")" -> (export,idl,mty) ] ]
  ;

  (* Module expressions *)
  module_expr:
    [ [ me = module_expr_atom -> me
      | me1 = module_expr; me2 = module_expr_atom -> CMEapply (me1,me2)
      ] ]
  ;
  module_expr_atom:
    [ [ qid = qualid -> CMEident qid | "("; me = module_expr; ")" -> me ] ]
  ;
  with_declaration:
    [ [ "Definition"; fqid = fullyqualid; ":="; c = Constr.lconstr ->
          CWith_Definition (fqid,c)
      | IDENT "Module"; fqid = fullyqualid; ":="; qid = qualid ->
	  CWith_Module (fqid,qid)
      ] ]
  ;
  module_type:
    [ [ qid = qualid -> CMTEident qid
(* ... *)
      | mty = module_type; me = module_expr_atom -> CMTEapply (mty,me) 
      | mty = module_type; "with"; decl = with_declaration -> CMTEwith (mty,decl)
      ] ]
  ;
END

(* Extensions: implicits, coercions, etc. *)   
GEXTEND Gram
  GLOBAL: gallina_ext;

  gallina_ext:
    [ [ (* Transparent and Opaque *)
        IDENT "Transparent"; b = non_locality; l = LIST1 global ->
          VernacSetOpacity (b,[Conv_oracle.transparent,l])
      | IDENT "Opaque"; b = non_locality; l = LIST1 global ->
          VernacSetOpacity (b,[Conv_oracle.Opaque, l])
      | IDENT "Strategy"; l =
          LIST1 [ lev=strategy_level; "["; q=LIST1 global; "]" -> (lev,q)] ->
            VernacSetOpacity (false,l)
      | IDENT "Local"; IDENT "Strategy"; l =
          LIST1 [ lev=strategy_level; "["; q=LIST1 global; "]" -> (lev,q)] ->
            VernacSetOpacity (true,l)
      (* Canonical structure *)
      | IDENT "Canonical"; IDENT "Structure"; qid = global ->
	  VernacCanonical qid
      | IDENT "Canonical"; IDENT "Structure"; qid = global; d = def_body ->
          let s = coerce_global_to_id qid in
	  VernacDefinition 
	    ((Global,false,CanonicalStructure),(dummy_loc,s),d,
	     (fun _ -> Recordops.declare_canonical_structure))

      (* Coercions *)
      | IDENT "Coercion"; qid = global; d = def_body ->
          let s = coerce_global_to_id qid in
	  VernacDefinition ((Global,false,Coercion),(dummy_loc,s),d,Class.add_coercion_hook)
      | IDENT "Coercion"; IDENT "Local"; qid = global; d = def_body ->
           let s = coerce_global_to_id qid in
	  VernacDefinition ((Local,false,Coercion),(dummy_loc,s),d,Class.add_coercion_hook)
      | IDENT "Identity"; IDENT "Coercion"; IDENT "Local"; f = identref;
         ":"; s = class_rawexpr; ">->"; t = class_rawexpr -> 
	   VernacIdentityCoercion (Local, f, s, t)
      | IDENT "Identity"; IDENT "Coercion"; f = identref; ":";
         s = class_rawexpr; ">->"; t = class_rawexpr -> 
	   VernacIdentityCoercion (Global, f, s, t)
      | IDENT "Coercion"; IDENT "Local"; qid = global; ":";
	 s = class_rawexpr; ">->"; t = class_rawexpr -> 
	  VernacCoercion (Local, qid, s, t)
      | IDENT "Coercion"; qid = global; ":"; s = class_rawexpr; ">->";
         t = class_rawexpr ->
	  VernacCoercion (Global, qid, s, t)

      (* Type classes, new syntax without artificial sup. *)
      | IDENT "Class"; qid = identref; pars = binders_let;
	 s = [ ":"; c = sort -> Some (loc, c) | -> None ];
	 props = typeclass_field_types ->
	   VernacClass (qid, pars, s, [], props)

      (* Type classes *)
      | IDENT "Class"; sup = OPT [ l = binders_let; "=>" -> l ];
	 qid = identref; pars = binders_let;
	 s = [ ":"; c = sort -> Some (loc, c) | -> None ];
	 props = typeclass_field_types ->
	   VernacClass (qid, pars, s, (match sup with None -> [] | Some l -> l), props)
	     
      | IDENT "Context"; c = binders_let -> 
	  VernacContext c
	    
      | IDENT "Instance"; local = non_locality; name = identref; 
	 sup = OPT binders_let; ":";
	 expl = [ "!" -> Rawterm.Implicit | -> Rawterm.Explicit ] ; t = operconstr LEVEL "200";
	 pri = OPT [ "|"; i = natural -> i ] ; props = typeclass_field_defs ->
	   let sup =
	     match sup with
		 None -> []
	       | Some l -> l
	   in
	   let n = 
	     let (loc, id) = name in 
	       (loc, Name id)
	   in
	     VernacInstance (not local, sup, (n, expl, t), props, pri)

      | IDENT "Existing"; IDENT "Instance"; is = identref -> VernacDeclareInstance is

      (* Implicit *)
      | IDENT "Implicit"; IDENT "Arguments"; 
	   local = [ IDENT "Global" -> false | IDENT "Local" -> true | -> Lib.sections_are_opened () ]; 
	   qid = global; 
	   pos = OPT [ "["; l = LIST0 implicit_name; "]" -> 
	     List.map (fun (id,b,f) -> (ExplByName id,b,f)) l ] ->
	   VernacDeclareImplicits (local,qid,pos)

      | IDENT "Implicit"; ["Type" | IDENT "Types"];
	   idl = LIST1 identref; ":"; c = lconstr -> VernacReserve (idl,c) ] ]
  ;
  implicit_name:
    [ [ "!"; id = ident -> (id, false, true)
    | id = ident -> (id,false,false)
    | "["; "!"; id = ident; "]" -> (id,true,true) 
    | "["; id = ident; "]" -> (id,true, false) ] ]
  ;
  typeclass_field_type:
    [ [ id = identref; oc = of_type_with_opt_coercion; t = lconstr -> id, oc, t ] ]
  ;
  typeclass_field_def:
    [ [ id = identref; params = LIST0 identref; ":="; t = lconstr -> id, params, t ] ]
  ;
  typeclass_field_types:
    [ [ ":="; l = LIST1 typeclass_field_type SEP ";" -> l
    | -> [] ] ]
  ;
  typeclass_field_defs:
    [ [ ":="; l = LIST1 typeclass_field_def SEP ";" -> l
    | -> [] ] ]
  ;
  strategy_level:
    [ [ IDENT "expand" -> Conv_oracle.Expand
      | IDENT "opaque" -> Conv_oracle.Opaque
      | n=INT -> Conv_oracle.Level (int_of_string n)
      | "-"; n=INT -> Conv_oracle.Level (- int_of_string n)
      | IDENT "transparent" -> Conv_oracle.transparent ] ]
  ;
END

GEXTEND Gram
  GLOBAL: command check_command class_rawexpr;

  command:
    [ [ IDENT "Comments"; l = LIST0 comment -> VernacComments l

      (* System directory *)
      | IDENT "Pwd" -> VernacChdir None
      | IDENT "Cd" -> VernacChdir None
      | IDENT "Cd"; dir = ne_string -> VernacChdir (Some dir)

      (* Toplevel control *)
      | IDENT "Drop" -> VernacToplevelControl Drop
      | IDENT "ProtectedLoop" -> VernacToplevelControl ProtectedLoop
      | IDENT "Quit" -> VernacToplevelControl Quit

      | IDENT "Load"; verbosely = [ IDENT "Verbose" -> true | -> false ];
	s = [ s = ne_string -> s | s = IDENT -> s ] ->
	  VernacLoad (verbosely, s)
      | IDENT "Declare"; IDENT "ML"; IDENT "Module"; l = LIST1 ne_string ->
	  VernacDeclareMLModule l

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
      | IDENT "Print"; qid = global -> VernacPrint (PrintName qid)
      | IDENT "Print"; IDENT "Module"; "Type"; qid = global -> 
	  VernacPrint (PrintModuleType qid)
      | IDENT "Print"; IDENT "Module"; qid = global -> 
	  VernacPrint (PrintModule qid)
      | IDENT "Inspect"; n = natural -> VernacPrint (PrintInspect n)
      | IDENT "About"; qid = global -> VernacPrint (PrintAbout qid)

      (* Searching the environment *)
      | IDENT "Search"; qid = global; l = in_or_out_modules -> 
	  VernacSearch (SearchHead qid, l)
      | IDENT "SearchPattern"; c = constr_pattern; l = in_or_out_modules ->
	  VernacSearch (SearchPattern c, l)
      | IDENT "SearchRewrite"; c = constr_pattern; l = in_or_out_modules ->
	  VernacSearch (SearchRewrite c, l)
      | IDENT "SearchAbout"; 
	  sl = [ "[";
	         l = LIST1 [ 
		   b = positive_search_mark; r = global -> b,SearchRef r
		 | b = positive_search_mark; s = ne_string; sc = OPT scope
		   -> b,SearchString (s,sc)
		 ]; "]" -> l
   	       | qid = global -> [true,SearchRef qid]
   	       | s = ne_string; sc = OPT scope -> [true,SearchString (s,sc)] ];
	  l = in_or_out_modules -> 
	  VernacSearch (SearchAbout sl, l)

      | IDENT "Add"; IDENT "ML"; IDENT "Path"; dir = ne_string ->
	  VernacAddMLPath (false, dir)
      | IDENT "Add"; IDENT "Rec"; IDENT "ML"; IDENT "Path"; dir = ne_string ->
	  VernacAddMLPath (true, dir)

      (* Pour intervenir sur les tables de paramètres *)
      | "Set"; table = option_table; v = option_value ->
  	  VernacSetOption (table,v)
      | "Set"; table = option_table ->
  	  VernacSetOption (table,BoolValue true)
      | IDENT "Unset"; table = option_table ->
  	  VernacUnsetOption table

      | IDENT "Print"; IDENT "Table"; table = option_table ->
	  VernacPrintOption table

      | IDENT "Add"; table = IDENT; field = IDENT; v = LIST1 option_ref_value
        -> VernacAddOption (SecondaryTable (table,field), v)
      (* Un value global ci-dessous va être caché par un field au dessus! *)
      (* En fait, on donne priorité aux tables secondaires *)
      (* Pas de syntaxe pour les tables tertiaires pour cause de conflit *)
      (* (mais de toutes façons, pas utilisées) *)
      | IDENT "Add"; table = IDENT; v = LIST1 option_ref_value ->
          VernacAddOption (PrimaryTable table, v)

      | IDENT "Test"; table = option_table; "for"; v = LIST1 option_ref_value
        -> VernacMemOption (table, v)
      | IDENT "Test"; table = option_table ->
          VernacPrintOption table

      | IDENT "Remove"; table = IDENT; field = IDENT; v= LIST1 option_ref_value
        -> VernacRemoveOption (SecondaryTable (table,field), v)
      | IDENT "Remove"; table = IDENT; v = LIST1 option_ref_value ->
	  VernacRemoveOption (PrimaryTable table, v) 

      | IDENT "proof" -> VernacDeclProof
      | "return" -> VernacReturn ]]
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
      | IDENT "Grammar"; ent = IDENT ->
          (* This should be in "syntax" section but is here for factorization*)
	  PrintGrammar ent
      | IDENT "LoadPath" -> PrintLoadPath
      | IDENT "Modules" -> 
          error "Print Modules is obsolete; use Print Libraries instead"
      | IDENT "Libraries" -> PrintModules

      | IDENT "ML"; IDENT "Path" -> PrintMLLoadPath
      | IDENT "ML"; IDENT "Modules" -> PrintMLModules
      | IDENT "Graph" -> PrintGraph
      | IDENT "Classes" ->  PrintClasses
      | IDENT "TypeClasses" -> PrintTypeClasses
      | IDENT "Instances"; qid = global -> PrintInstances qid
      | IDENT "Ltac"; qid = global -> PrintLtac qid
      | IDENT "Coercions" -> PrintCoercions
      | IDENT "Coercion"; IDENT "Paths"; s = class_rawexpr; t = class_rawexpr
         -> PrintCoercionPaths (s,t)
      | IDENT "Canonical"; IDENT "Projections" -> PrintCanonicalConversions
      | IDENT "Tables" -> PrintTables
(* Obsolete: was used for cooking V6.3 recipes ??
      | IDENT "Proof"; qid = global -> PrintOpaqueName qid
*)
      | IDENT "Hint" -> PrintHintGoal
      | IDENT "Hint"; qid = global -> PrintHint qid
      | IDENT "Hint"; "*" -> PrintHintDb
      | IDENT "HintDb"; s = IDENT -> PrintHintDbName s
      | "Rewrite"; IDENT "HintDb"; s = IDENT -> PrintRewriteHintDbName s
      | IDENT "Setoids" -> PrintSetoids
      | IDENT "Scopes" -> PrintScopes
      | IDENT "Scope"; s = IDENT -> PrintScope s
      | IDENT "Visibility"; s = OPT IDENT -> PrintVisibility s
      | IDENT "Implicit"; qid = global -> PrintImplicit qid
      | IDENT "Universes"; fopt = OPT ne_string -> PrintUniverses fopt
      | IDENT "Assumptions"; qid = global -> PrintAssumptions qid ] ]
  ;
  class_rawexpr:
    [ [ IDENT "Funclass" -> FunClass
      | IDENT "Sortclass" -> SortClass
      | qid = global -> RefClass qid ] ]
  ;
  locatable:
    [ [ qid = global -> LocateTerm qid
      | IDENT "File"; f = ne_string -> LocateFile f
      | IDENT "Library"; qid = global -> LocateLibrary qid
      | IDENT "Module"; qid = global -> LocateModule qid
      | s = ne_string -> LocateNotation s ] ]
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
    [ [ f1 = IDENT; f2 = IDENT; f3 = IDENT -> TertiaryTable (f1,f2,f3)
      | f1 = IDENT; f2 = IDENT -> SecondaryTable (f1,f2)
      | f1 = IDENT -> PrimaryTable f1 ] ]
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
          VernacSetOption (SecondaryTable ("Ltac","Debug"), BoolValue true)

      |	IDENT "Debug"; IDENT "Off" ->
          VernacSetOption (SecondaryTable ("Ltac","Debug"), BoolValue false)

 ] ];
    END
;;

(* Grammar extensions *)

GEXTEND Gram
  GLOBAL: syntax;

  syntax:
   [ [ IDENT "Open"; local = locality; IDENT "Scope"; sc = IDENT -> 
         VernacOpenCloseScope (local,true,sc)

     | IDENT "Close"; local = locality; IDENT "Scope"; sc = IDENT -> 
         VernacOpenCloseScope (local,false,sc)

     | IDENT "Delimit"; IDENT "Scope"; sc = IDENT; "with"; key = IDENT ->
	 VernacDelimiters (sc,key)

     | IDENT "Bind"; IDENT "Scope"; sc = IDENT; "with"; 
       refl = LIST1 class_rawexpr -> VernacBindScope (sc,refl)

     | IDENT "Arguments"; IDENT "Scope"; local = non_locality; qid = global;
       "["; scl = LIST0 opt_scope; "]" -> VernacArgumentsScope (local,qid,scl)

     | IDENT "Infix"; local = locality;
	 op = ne_string; ":="; p = global; 
         modl = [ "("; l = LIST1 syntax_modifier SEP ","; ")" -> l | -> [] ];
	 sc = OPT [ ":"; sc = IDENT -> sc ] ->
         VernacInfix (local,(op,modl),p,sc)
     | IDENT "Notation"; local = locality; id = identref; idl = LIST0 ident; 
	 ":="; c = constr;
	 b = [ "("; IDENT "only"; IDENT "parsing"; ")" -> true | -> false ] ->
           VernacSyntacticDefinition (id,(idl,c),local,b)
     | IDENT "Notation"; local = locality; s = ne_string; ":="; c = constr;
         modl = [ "("; l = LIST1 syntax_modifier SEP ","; ")" -> l | -> [] ];
	 sc = OPT [ ":"; sc = IDENT -> sc ] ->
           VernacNotation (local,c,(s,modl),sc)

     | IDENT "Tactic"; IDENT "Notation"; n = tactic_level; 
	 pil = LIST1 production_item; ":="; t = Tactic.tactic
         -> VernacTacticNotation (n,pil,t)

     | IDENT "Reserved"; IDENT "Notation"; local = locality; s = ne_string; 
	 l = [ "("; l = LIST1 syntax_modifier SEP ","; ")" -> l | -> [] ]
	 -> VernacSyntaxExtension (local,(s,l))

     (* "Print" "Grammar" should be here but is in "command" entry in order 
        to factorize with other "Print"-based vernac entries *)
  ] ]
  ;
  tactic_level:
    [ [ "("; "at"; IDENT "level"; n = natural; ")" -> n | -> 0 ] ]
  ;
  level:
    [ [ IDENT "level"; n = natural -> NumLevel n
      | IDENT "next"; IDENT "level" -> NextLevel ] ]
  ;
  syntax_modifier:
    [ [ x = IDENT; "at"; lev = level -> SetItemLevel ([x],lev)
      | x = IDENT; ","; l = LIST1 IDENT SEP ","; "at"; 
        lev = level -> SetItemLevel (x::l,lev)
      | "at"; IDENT "level"; n = natural -> SetLevel n
      | IDENT "left"; IDENT "associativity" -> SetAssoc Gramext.LeftA
      | IDENT "right"; IDENT "associativity" -> SetAssoc Gramext.RightA
      | IDENT "no"; IDENT "associativity" -> SetAssoc Gramext.NonA
      | x = IDENT; typ = syntax_extension_type -> SetEntryType (x,typ)
      | IDENT "only"; IDENT "parsing" -> SetOnlyParsing
      | IDENT "format"; s = [s = STRING -> (loc,s)] -> SetFormat s ] ]
  ;
  syntax_extension_type:
    [ [ IDENT "ident" -> ETIdent | IDENT "global" -> ETReference
      | IDENT "bigint" -> ETBigint
    ] ]
  ;
  opt_scope:
    [ [ "_" -> None | sc = IDENT -> Some sc ] ]
  ;
  production_item:
    [ [ s = ne_string -> VTerm s
      | nt = IDENT; po = OPT [ "("; p = ident; ")" -> p ] -> 
	  VNonTerm (loc,nt,po) ] ]
  ;
END
