(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Names
open Topconstr
open Vernacexpr
open Pcoq
open Pp
open Tactic
open Util
open Constr
open Vernac_
open Prim
open Symbol
open Decl_kinds

(* Dans join_binders, s'il y a un "?", on perd l'info qu'il est partag�� *)
let join_binders (idl,c) = List.map (fun id -> (id,c)) idl

open Genarg

let evar_constr loc = CHole loc

(* Rem: do not join the different GEXTEND into one, it breaks native *)
(* compilation on PowerPC and Sun architectures *)

GEXTEND Gram
  GLOBAL: vernac gallina_ext;
  vernac:
    (* Better to parse "." here: in case of failure (e.g. in coerce_to_var), *)
    (* "." is still in the stream and discard_to_dot works correctly         *)
    [ [ g = gallina; "." -> g 
      | g = gallina_ext; "." -> g
      | c = command; "." -> c 
      | c = syntax; "." -> c
      | n = natural; ":"; tac = Tactic.tactic; "." -> VernacSolve (n,tac,true) 
      | n = natural; ":"; tac = Tactic.tactic; "!!" -> VernacSolve (n,tac,false)
      | n = natural; ":"; v = check_command; "." -> v (Some n)
      | "["; l = vernac_list_tail -> VernacList l

      (* For translation from V7 to V8 *)
      | IDENT "V7only"; v = vernac -> VernacV7only v
      | IDENT "V8only"; v = vernac -> VernacV8only v

(*
      (* This is for "Grammar vernac" rules *)
      | id = METAIDENT -> VernacVar (Names.id_of_string id)
*)
    ] ]
  ;
    
  check_command:
    [ [ IDENT "Eval"; r = Tactic.red_expr; "in"; c = constr ->
          fun g -> VernacCheckMayEval (Some r, g, c)
      | IDENT "Check"; c = constr ->
	  fun g -> VernacCheckMayEval (None, g, c) ] ]
  ;
  vernac: FIRST
    [ [ IDENT "Time"; v = vernac  -> VernacTime v ] ]
  ;
  vernac: LAST
    [ [ tac = Tactic.tactic; "." -> VernacSolve (1,tac,true)
      | tac = Tactic.tactic; "!!" -> VernacSolve (1,tac,false)
      | IDENT "Existential"; n = natural; c = constr_body ->
	  VernacSolveExistential (n,c)
    ] ]
  ;
  constr_body:
    [ [ ":="; c = constr; ":"; t = constr -> CCast(loc,c,t)
      | ":"; t = constr; ":="; c = constr -> CCast(loc,c,t)
      | ":="; c = constr -> c ] ]
  ;
  vernac_list_tail:
    [ [ v = located_vernac; l = vernac_list_tail -> v :: l
      | "]"; "." -> [] ] ]
  ;
  located_vernac:
    [ [ v = vernac -> loc, v ] ]
  ;
END

let test_plurial_form = function
  | [_] ->
      Options.if_verbose warning
      "Keywords Variables/Hypotheses/Parameters expect more than one assumption"
  | _ -> ()

(* Gallina declarations *)
GEXTEND Gram
  GLOBAL: gallina gallina_ext thm_token;

  thm_token:
    [ [ "Theorem" -> Theorem
      | IDENT "Lemma" -> Lemma
      | IDENT "Fact" -> Fact
      | IDENT "Remark" -> Remark ] ]
  ;
  def_token:
    [ [ "Definition" -> (fun _ _ -> ()), Global, GDefinition
      | IDENT "Local" -> (fun _ _ -> ()), Local, LDefinition
      | IDENT "SubClass"  -> Class.add_subclass_hook, Global, GCoercion
      | IDENT "Local"; IDENT "SubClass"  -> Class.add_subclass_hook, Local, LCoercion ] ] 
  ;
  assumption_token:
    [ [ "Hypothesis" -> (Local, Logical)
      | "Variable" -> (Local, Definitional)
      | "Axiom" -> (Global, Logical)
      | "Parameter" -> (Global, Definitional) ] ]
  ;
  assumptions_token:
    [ [ IDENT "Hypotheses" -> (Local, Logical)
      | IDENT "Variables" -> (Local, Definitional)
      | IDENT "Parameters" -> (Global, Definitional) ] ]
  ;
  of_type_with_opt_coercion:
    [ [ ":>" -> true
      | ":"; ">" -> true
      | ":" -> false ] ]
  ;
  params:
    [ [ idl = LIST1 base_ident SEP ","; coe = of_type_with_opt_coercion; c = constr
      -> List.map (fun c -> (coe,c)) (join_binders (idl,c))
    ] ]
  ;
  ne_params_list:
    [ [ ll = LIST1 params SEP ";" -> List.flatten ll ] ]
  ;
  name_comma_list_tail:
    [ [ ","; nal = LIST1 name SEP "," -> nal | -> [] ] ]
  ;
  ident_comma_list_tail:
    [ [ ","; nal = LIST1 base_ident SEP "," -> nal | -> [] ] ]
  ;
  type_option:
    [ [ ":"; c = constr -> c 
      | -> evar_constr loc ] ]
  ;
  opt_casted_constr:
    [ [ c = constr;  ":"; t = constr -> CCast(loc,c,t)
      | c = constr -> c ] ]
  ;
  vardecls:
    [ [ na = name; nal = name_comma_list_tail; c = type_option
          -> LocalRawAssum (na::nal,c)
      | na = name; "="; c = opt_casted_constr ->
          LocalRawDef (na,c)
      | na = name; ":="; c = opt_casted_constr ->
          LocalRawDef (na,c)
    ] ]
  ;
  binders:
    [ [ "["; bl = LIST1 vardecls SEP ";"; "]" -> bl ] ]
  ;
  binders_list:
    [ [ bls = LIST0 binders -> List.flatten bls ] ]
  ;
  reduce:
    [ [ IDENT "Eval"; r = Tactic.red_expr; "in" -> Some r
      | -> None ] ]
  ;
  def_body:
    [ [ bl = binders_list; ":="; red = reduce; c = constr; ":"; t = constr ->
          DefineBody (bl, red, c, Some t)
      | bl = binders_list; ":"; t = constr; ":="; red = reduce; c = constr ->
          DefineBody (bl, red, c, Some t)
      | bl = binders_list; ":="; red = reduce; c = constr ->
          DefineBody (bl, red, c, None)
      | bl = binders_list; ":"; t = constr ->
          ProveBody (bl, t) ] ]
  ;
  gallina:
    (* Definition, Theorem, Variable, Axiom, ... *)
    [ [ thm = thm_token; id = base_ident; bl = binders_list; ":"; c = constr ->
         VernacStartTheoremProof (thm, id, (bl, c), false, (fun _ _ -> ()))
      | (f,d,e) = def_token; id = base_ident; b = def_body -> 
          VernacDefinition (d, id, b, f, e)
      | stre = assumption_token; bl = ne_params_list -> 
	  VernacAssumption (stre, bl)
      | stre = assumptions_token; bl = ne_params_list ->
	  test_plurial_form bl;
	  VernacAssumption (stre, bl)

      (* Symbols and rules *)
      | IDENT "Symbol"; (a,e) = symb_arity; s = symb_status; m = symb_mons;
	  am = symb_antimons; id = base_ident; ":"; t = constr ->
	    VernacSymbol (id,t,a,e,s,m,am)
      | IDENT "Rules"; ctx = rew_rules_ctx; subs = rew_rules_subs;
        "{"; rules = ne_rew_rules_list; "}" -> VernacRules (ctx,subs,rules)
      ] ]
  ;
  symb_arity:
    [ [ IDENT "C" -> 2,C
      | IDENT "AC" -> 2,AC
      | n = natural -> n,Free ] ]
  ;
  symb_status:
    [ [ IDENT "Lex" -> Lex
      | IDENT "Mul" -> Mul
      | IDENT "RLex" -> RevLex
      | IDENT "Lex"; "("; l = LIST1 mul_status SEP ","; ")" -> Comb l ] ]
  ;
  mul_status:
    [ [ n = natural -> [n]
      | IDENT "Mul"; n = natural; l = LIST1 natural -> n::l ] ]
  ;
  symb_mons:
    [ [ IDENT "Mon"; "("; l = LIST1 natural SEP ","; ")" -> l
      | -> [] ] ]
  ;
  symb_antimons:
    [ [ IDENT "Antimon"; "("; l = LIST1 natural SEP ","; ")" -> l
      | -> [] ] ]
  ;
  rew_rules_ctx:
    [ [ "["; l = LIST1 rew_rules_var_decl SEP ";"; "]" -> List.flatten l
      | -> [] ] ]
  ;
  rew_rules_var_decl:
    [ [ l = LIST1 base_ident SEP ","; ":"; c = constr -> join_binders (l,c) ] ]
  ;
  rew_rules_subs:
    [ [ IDENT "let"; l = LIST1 rew_rules_simple_subs SEP ","; IDENT "in" -> l
      | -> [] ] ]
  ;
  rew_rules_simple_subs:
    [ [ id = base_ident; ":="; c = constr -> (id,c) ] ]
  ;
  ne_rew_rules_list:
    [ [ rl = LIST1 rew_rule SEP ";" -> rl ] ]
  ;
  rew_rule:
    [ [ l = constr; "=>"; r = constr -> (l,r) ] ]
  ;

  (* Gallina inductive declarations *)
  finite_token:
    [ [ "Inductive" -> true
      | "CoInductive" -> false ] ]
  ;
  record_token:
    [ [ IDENT "Record" -> () | IDENT "Structure" -> () ] ]
  ;
  constructor:
    [ [ idl = LIST1 base_ident SEP ","; coe = of_type_with_opt_coercion;
        c = constr -> List.map (fun id -> (coe,(id,c))) idl ] ]
  ;
  constructor_list:
    [ [ "|"; l = LIST1 constructor SEP "|" -> List.flatten l
      | l = LIST1 constructor SEP "|" -> List.flatten l
      |  -> [] ] ]
  ;
  block_old_style:
    [ [ ind = oneind_old_style; "with"; indl = block_old_style -> ind :: indl
      | ind = oneind_old_style -> [ind] ] ]
  ;
  oneind_old_style:
    [ [ id = base_ident; ":"; c = constr; ":="; lc = constructor_list ->
          (id,c,lc) ] ]
  ;
  oneind:
    [ [ id = base_ident; indpar = simple_binders_list; ":"; c = constr; ":=";
	lc = constructor_list -> (id,indpar,c,lc) ] ]
  ;
  simple_binders_list:
    [ [ bl = ne_simple_binders_list -> bl
      |  -> [] ] ]
  ;
  opt_coercion:
    [ [ ">" -> true
      |  -> false ] ]
  ;
  onescheme:
    [ [ id = base_ident; ":="; dep = dep; ind = global; IDENT "Sort";
        s = sort -> (id,dep,ind,s) ] ]
  ;
  schemes:
    [ [ recl = LIST1 onescheme SEP "with" -> recl ] ]
  ;
  dep:
    [ [ IDENT "Induction"; IDENT "for" -> true
      | IDENT "Minimality"; IDENT "for" -> false ] ]
  ;
  onerec:
    [ [ id = base_ident; bl = ne_fix_binders; ":"; type_ = constr;
        ":="; def = constr ->
          let ni = List.length (List.flatten (List.map fst bl)) - 1 in
          let loc0 = fst (List.hd (fst (List.hd bl))) in
          let loc1 = join_loc loc0 (constr_loc type_) in
          let loc2 = join_loc loc0 (constr_loc def) in
	  (id, ni, CProdN (loc1,bl,type_), CLambdaN (loc2,bl,def)) ] ]
  ;
  specifrec:
    [ [ l = LIST1 onerec SEP "with" -> l ] ]
  ;
  onecorec:
    [ [ id = base_ident; ":"; c = constr; ":="; def = constr ->
          (id,c,def) ] ]
  ;
  specifcorec:
    [ [ l = LIST1 onecorec SEP "with" -> l ] ]
  ;
  record_field:
    [ [ id = base_ident; oc = of_type_with_opt_coercion; t = constr ->
          (oc,AssumExpr (id,t))
      | id = base_ident; oc = of_type_with_opt_coercion; t = constr;
	":="; b = constr ->
	  (oc,DefExpr (id,b,Some t))
      | id = base_ident; ":="; b = constr ->
	  (false,DefExpr (id,b,None)) ] ]
  ;
  fields:
    [ [ fs = LIST0 record_field SEP ";" -> fs ] ]
  ;
  simple_params:
    [ [ idl = LIST1 base_ident SEP ","; ":"; c = constr -> join_binders (idl, c)
      | idl = LIST1 base_ident SEP "," -> join_binders (idl, evar_constr dummy_loc)
    ] ]
  ;
  simple_binders:
    [ [ "["; bll = LIST1 simple_params SEP ";"; "]" -> List.flatten bll ] ]
  ;
  ne_simple_binders_list:
    [ [ bll = LIST1 simple_binders -> List.flatten bll ] ]
  ;
  fix_params:
    [ [ idl = LIST1 name SEP ","; ":"; c = constr -> (idl, c)
      | idl = LIST1 name SEP "," -> (idl, evar_constr dummy_loc)
    ] ]
  ;
  fix_binders:
    [ [ "["; bll = LIST1 fix_params SEP ";"; "]" -> bll ] ]
  ;
  ne_fix_binders:
    [ [ bll = LIST1 fix_binders -> List.flatten bll ] ]
  ;
  rec_constructor:
    [ [ c = base_ident -> Some c
      |  -> None ] ]
  ;
  gallina_ext:
    [ [ IDENT "Mutual"; bl = ne_simple_binders_list ; f = finite_token;
        indl = block_old_style ->
	  let indl' = List.map (fun (id,ar,c) -> (id,bl,ar,c)) indl in
	  VernacInductive (f,indl')
      | record_token; oc = opt_coercion; name = base_ident;
	ps = simple_binders_list; ":";
	s = constr; ":="; c = rec_constructor; "{"; fs = fields; "}" ->
	  VernacRecord ((oc,name),ps,s,c,fs)
    ] ]
  ;
  gallina:
    [ [ IDENT "Mutual"; f = finite_token; indl = LIST1 oneind SEP "with" ->
          VernacInductive (f,indl)
      | f = finite_token; indl = LIST1 oneind SEP "with" ->
          VernacInductive (f,indl)
      | "Fixpoint"; recs = specifrec -> VernacFixpoint recs
      | "CoFixpoint"; corecs = specifcorec -> VernacCoFixpoint corecs
      | IDENT "Scheme"; l = schemes -> VernacScheme l
      | f = finite_token; s = csort; id = base_ident;
	indpar = simple_binders_list; ":="; lc = constructor_list -> 
          VernacInductive (f,[id,indpar,s,lc]) ] ]
  ;
  csort:
    [ [ s = sort -> CSort (loc,s) ] ]
  ;
  gallina_ext:
    [ [ 
(* Sections *)
	IDENT "Section"; id = base_ident -> VernacBeginSection id
      | IDENT "Chapter"; id = base_ident -> VernacBeginSection id ] ]
  ;

  module_vardecls: (* This is interpreted by Pcoq.abstract_binder *)
    [ [ id = base_ident; idl = ident_comma_list_tail; ":"; mty = Module.module_type
        -> (id::idl,mty) ] ]
  ;
  module_binders:
    [ [ "["; bl = LIST1 module_vardecls SEP ";"; "]" -> bl ] ]
  ;
  module_binders_list:
    [ [ bls = LIST0 module_binders -> List.flatten bls ] ]
  ;
  of_module_type:
    [ [ ":"; mty = Module.module_type -> (mty, true) 
      | "<:"; mty = Module.module_type -> (mty, false) ] ]
  ;
  is_module_type:
    [ [ ":="; mty = Module.module_type -> mty ] ]
  ;
  is_module_expr:
    [ [ ":="; mexpr = Module.module_expr -> mexpr ] ]
  ;
  gallina_ext:
    [ [ 
	  (* Interactive module declaration *)
	IDENT "Module"; id = base_ident; 
	bl = module_binders_list; mty_o = OPT of_module_type; 
	mexpr_o = OPT is_module_expr ->
	  VernacDefineModule (id, bl, mty_o, mexpr_o)
	  
      | IDENT "Module"; "Type"; id = base_ident; 
	bl = module_binders_list; mty_o = OPT is_module_type ->
	  VernacDeclareModuleType (id, bl, mty_o)
	  
      | IDENT "Declare"; IDENT "Module"; id = base_ident; 
	bl = module_binders_list; mty_o = OPT of_module_type; 
	mexpr_o = OPT is_module_expr ->
	  VernacDeclareModule (id, bl, mty_o, mexpr_o)

	  (* This end a Section a Module or a Module Type *)

      | IDENT "End"; id = base_ident -> VernacEndSegment id


(* Transparent and Opaque *)
      | IDENT "Transparent"; l = LIST1 global -> VernacSetOpacity (false, l)
      | IDENT "Opaque"; l = LIST1 global -> VernacSetOpacity (true, l)

(* Canonical structure *)
      | IDENT "Canonical"; IDENT "Structure"; qid = global ->
	  VernacCanonical qid
      | IDENT "Canonical"; IDENT "Structure"; qid = global; d = def_body ->
          let s = Ast.coerce_global_to_id qid in
	  VernacDefinition (Global,s,d,Recordobj.add_object_hook,SCanonical)
      (* Rem: LOBJECT, OBJCOERCION, LOBJCOERCION have been removed
         (they were unused and undocumented) *)

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
      | IDENT "Class"; IDENT "Local"; c = global ->
	  Pp.warning "Class is obsolete"; VernacNop
      | IDENT "Class"; c = global ->
	  Pp.warning "Class is obsolete"; VernacNop

(* Implicit *)
(*
      | IDENT "Syntactic"; "Definition"; id = base_ident; ":="; c = constr;
         n = OPT [ "|"; n = natural -> n ] ->
	   VernacSyntacticDefinition (id,c,n)
*)
      | IDENT "Syntactic"; "Definition"; id = IDENT; ":="; c = constr;
         n = OPT [ "|"; n = natural -> n ] ->
	   let c = match n with
	     | Some n ->
		 let l = list_tabulate (fun _ -> (CHole (loc),None)) n in
		 CApp (loc,c,l)
	     | None -> c in
	   VernacNotation ("'"^id^"'",c,[],None)
      | IDENT "Implicits"; qid = global; "["; l = LIST0 natural; "]" ->
	  VernacDeclareImplicits (qid,Some l)
      | IDENT "Implicits"; qid = global -> VernacDeclareImplicits (qid,None)

      (* For compatibility *)
      | IDENT "Implicit"; IDENT "Arguments"; IDENT "On" ->
	  VernacSetOption
	    (Goptions.SecondaryTable ("Implicit","Arguments"), BoolValue true)
      | IDENT "Implicit"; IDENT "Arguments"; IDENT "Off" ->
	  VernacSetOption
	    (Goptions.SecondaryTable ("Implicit","Arguments"), BoolValue false)
  ] ]
  ;
END

(* Modules management *)   
GEXTEND Gram
  GLOBAL: command;

  export_token:
    [ [ IDENT "Import" -> false
      | IDENT "Export" -> true
      |  -> false ] ]
  ;
  specif_token:
    [ [ IDENT "Implementation" -> Some false
      | IDENT "Specification" -> Some true
      |  -> None ] ]
  ;
  command:
    [ [ "Load"; verbosely = [ IDENT "Verbose" -> true | -> false ];
	s = [ s = STRING -> s | s = IDENT -> s ] ->
	  VernacLoad (verbosely, s)
(*      | "Compile";
	verbosely =
          [ IDENT "Verbose" -> "Verbose"
          | -> "" ];
	IDENT "Module";
	only_spec =
          [ IDENT "Specification" -> "Specification"
          | -> "" ];
	mname = [ s = STRING -> s | s = IDENT -> s ];
	fname = OPT [ s = STRING -> s | s = IDENT -> s ] -> ExtraVernac
          let fname = match fname with Some s -> s | None -> mname in
            <:ast< (CompileFile ($STR $verbosely) ($STR $only_spec)
                      ($STR $mname) ($STR $fname))>>
*)
      | IDENT "Read"; IDENT "Module"; qidl = LIST1 global ->
	  VernacRequire (None, None, qidl)
      | IDENT "Require"; export = export_token; specif = specif_token;
        qidl = LIST1 global -> VernacRequire (Some export, specif, qidl)
(*      | IDENT "Require"; export = export_token; specif = specif_token;
        id = base_ident; filename = STRING -> 
	  VernacRequireFrom (export, specif, id, filename) *)
      | IDENT "Require"; export = export_token; specif = specif_token;
        filename = STRING -> 
	  VernacRequireFrom (export, specif, filename)
      | IDENT "Declare"; IDENT "ML"; IDENT "Module"; l = LIST1 STRING ->
	  VernacDeclareMLModule l
      | IDENT "Import"; qidl = LIST1 global -> VernacImport (false,qidl)
      | IDENT "Export"; qidl = LIST1 global -> VernacImport (true,qidl)
  ] 
]
  ;
END

GEXTEND Gram
  GLOBAL: command;

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
