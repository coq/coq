(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i camlp4deps: "parsing/grammar.cma" i*)

(* $Id$ *)

open Coqast
open Vernacexpr
open Pcoq
open Pp
open Tactic
open Util
open Constr
open Vernac_
open Prim

(* Dans join_binders, s'il y a un "?", on perd l'info qu'il est partagé *)
let join_binders (idl,c) = List.map (fun id -> (id,c)) idl

open Genarg

let evar_constr loc = <:ast< (ISEVAR) >>

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
      | n = Prim.natural; ":"; tac = Tactic.tactic; "." -> VernacSolve (n,tac)
      | "["; l = vernac_list_tail -> VernacList l
      (* This is for "Grammar vernac" rules *)
      | id = Prim.metaident -> VernacVar (Ast.nvar_of_ast id) ] ]
  ;
  vernac: FIRST
    [ [ IDENT "Time"; v = vernac  -> VernacTime v ] ]
  ;
  vernac: LAST
    [ [ tac = Tactic.tactic; "." ->
        (match tac with
(* Horrible hack pour LETTOP !
	| VernacSolve (Coqast.Node(_,kind,_))
          when kind = "StartProof" || kind = "TheoremProof" -> ??
*)
	| _ -> VernacSolve (1,tac))
      | IDENT "Existential"; n = natural; c = constr_body ->
	  VernacSolveExistential (n,c)
    ] ]
  ;
  constr_body:
    [ [ ":="; c = constr; ":"; t = constr -> <:ast< (CAST $c $t) >>
      | ":"; t = constr; ":="; c = constr -> <:ast< (CAST $c $t) >>
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
      | IDENT "Remark" -> Remark
      | IDENT "Decl" -> Decl ] ]
  ;
  def_token:
    [ [ "Definition" -> (fun _ _ -> ()), Definition
      | IDENT "Local" -> (fun _ _ -> ()), LocalDefinition
      | IDENT "SubClass"  -> Class.add_subclass_hook, Definition
      | IDENT "Local"; IDENT "SubClass"  ->
	  Class.add_subclass_hook, LocalDefinition ] ]  
  ;
  assumption_token:
    [ [ "Hypothesis" -> AssumptionHypothesis
      | "Variable" -> AssumptionVariable
      | "Axiom" -> AssumptionAxiom
      | "Parameter" -> AssumptionParameter ] ]
  ;
  assumptions_token:
    [ [ IDENT "Hypotheses" -> AssumptionHypothesis
      | IDENT "Variables" -> AssumptionVariable
      | IDENT "Parameters" -> AssumptionParameter ] ]
  ;
  of_type_with_opt_coercion:
    [ [ ":>" -> true
      | ":"; ">" -> true
      | ":" -> false ] ]
  ;
  params:
    [ [ idl = LIST1 ident SEP ","; coe = of_type_with_opt_coercion; c = constr
      -> List.map (fun c -> (coe,c)) (join_binders (idl,c))
    ] ]
  ;
  ne_params_list:
    [ [ ll = LIST1 params SEP ";" -> List.flatten ll ] ]
  ;
ident_comma_list_tail:
    [ [ ","; idl = LIST1 ident SEP "," -> idl | -> [] ] ]
  ;
  type_option:
    [ [ ":"; c = constr -> c 
      | -> evar_constr loc ] ]
  ;
  opt_casted_constr:
    [ [ c = constr;  ":"; t = constr -> <:ast< (CAST $c $t) >>
      | c = constr -> c ] ]
  ;
  vardecls:
    [ [ id = ident; idl = ident_comma_list_tail; c = type_option ->
          LocalRawAssum (id::idl,c)
      | id = ident; [ "=" | ":=" ]; c = opt_casted_constr ->
          LocalRawDef (id,c)
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
    [ [ thm = thm_token; id = ident; ":"; c = constr -> 
         VernacStartTheoremProof (thm, id, c, false, (fun _ _ -> ()))
      | (f,d) = def_token; id = ident; b = def_body -> 
          VernacDefinition (d, id, b, f)
      | stre = assumption_token; bl = ne_params_list -> 
	  VernacAssumption (stre, bl)
      | stre = assumptions_token; bl = ne_params_list ->
	  test_plurial_form bl;
	  VernacAssumption (stre, bl)
      ] ]
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
    [ [ id = ident; coe = of_type_with_opt_coercion; c = constr ->
        (coe,(id,c)) ] ]
  ;
  ne_constructor_list:
    [ [ idc = constructor; "|"; l = ne_constructor_list -> idc :: l
      | idc = constructor -> [idc] ] ]
  ;
  constructor_list:
    [ [ "|"; l = ne_constructor_list -> l
      | l = ne_constructor_list -> l
      |  -> [] ] ]
  ;
  block_old_style:
    [ [ ind = oneind_old_style; "with"; indl = block_old_style -> ind :: indl
      | ind = oneind_old_style -> [ind] ] ]
  ;
  oneind_old_style:
    [ [ id = ident; ":"; c = constr; ":="; lc = constructor_list ->
          (id,c,lc) ] ]
  ;
  block:
    [ [ ind = oneind; "with"; indl = block -> ind :: indl
      | ind = oneind -> [ind] ] ]
  ;
  oneind:
    [ [ id = ident; indpar = indpar; ":"; c = constr; ":=";
	lc = constructor_list -> (id,indpar,c,lc) ] ]
  ;
  indpar:
    [ [ bl = ne_simple_binders_list -> bl
      |  -> [] ] ]
  ;
  opt_coercion:
    [ [ ">" -> true
      |  -> false ] ]
  ;
  onescheme:
    [ [ id = ident; ":="; dep = dep; ind = qualid; IDENT "Sort";
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
    [ [ id = ident; idl = ne_simple_binders_list; ":"; c = constr;
        ":="; def = constr -> (id,idl,c,def) ] ]
  ;
  specifrec:
    [ [ l = LIST1 onerec SEP "with" -> l ] ]
  ;
  onecorec:
    [ [ id = ident; ":"; c = constr; ":="; def = constr ->
          (id,c,def) ] ]
  ;
  specifcorec:
    [ [ l = LIST1 onecorec SEP "with" -> l ] ]
  ;
  record_field:
    [ [ id = ident; oc = of_type_with_opt_coercion; t = constr ->
          (oc,AssumExpr (id,t))
      | id = ident; oc = of_type_with_opt_coercion; t = constr;
	":="; b = constr ->
	  (oc,DefExpr (id,b,Some t))
      | id = ident; ":="; b = constr ->
	  (false,DefExpr (id,b,None)) ] ]
  ;
  fields:
    [ [ fs = LIST0 record_field SEP ";" -> fs ] ]
  ;
  simple_params:
    [ [ idl = LIST1 ident SEP ","; ":"; c = constr -> join_binders (idl, c)
      | idl = LIST1 ident SEP "," -> join_binders (idl, evar_constr dummy_loc)
    ] ]
  ;
  simple_binders:
    [ [ "["; bll = LIST1 simple_params SEP ";"; "]" -> List.flatten bll ] ]
  ;
  ne_simple_binders_list:
    [ [ bll = LIST1 simple_binders -> List.flatten bll ] ]
  ;
  rec_constructor:
    [ [ c = ident -> Some c
      |  -> None ] ]
  ;
  gallina_ext:
    [ [ IDENT "Mutual"; bl = ne_simple_binders_list ; f = finite_token;
        indl = block_old_style ->
	  let indl' = List.map (fun (id,ar,c) -> (id,bl,ar,c)) indl in
	  VernacInductive (f,indl')
      | record_token; oc = opt_coercion; name = ident; ps = indpar; ":";
	s = sort; ":="; c = rec_constructor; "{"; fs = fields; "}" ->
	  VernacRecord ((oc,name),ps,s,c,fs)
    ] ]
  ;
  gallina:
    [ [ IDENT "Mutual"; f = finite_token; indl = block ->
          VernacInductive (f,indl)
      | "Fixpoint"; recs = specifrec -> VernacFixpoint recs
      | "CoFixpoint"; corecs = specifcorec -> VernacCoFixpoint corecs
      | IDENT "Scheme"; l = schemes -> VernacScheme l
      | f = finite_token; s = sort; id = ident; indpar = indpar; ":=";
        lc = constructor_list -> 
          VernacInductive (f,[id,indpar,s,lc])
      | f = finite_token; indl = block ->
          VernacInductive (f,indl) ] ]
  ;
  gallina_ext:
    [ [ 
(* Sections *)
	IDENT "Section"; id = ident -> VernacBeginSection id
      | IDENT "Chapter"; id = ident -> VernacBeginSection id ] ]
(*      | IDENT "Module"; id = ident  -> 
	  warning "Module is currently unsupported"; VernacNop *)
  ;

  module_vardecls: (* This is interpreted by Pcoq.abstract_binder *)
    [ [ id = ident; idl = ident_comma_list_tail; 
	":"; mty = Module.module_type ->
          (id::idl,mty) ] ]
  ;
  module_binders:
    [ [ "["; bl = LIST1 module_vardecls SEP ";"; "]" -> bl ] ]
  ;
  module_binders_list:
    [ [ bls = LIST0 module_binders -> List.flatten bls ] ]
  ;
  of_module_type:
    [ [ ":"; mty = Module.module_type -> mty ] ]
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
	IDENT "Module"; id = ident; bl = module_binders_list;
	mty_o = OPT of_module_type; mexpr_o = OPT is_module_expr ->
	  VernacDeclareModule id bl mty_o mexpr_o
	  
      | IDENT "Module"; "Type"; id = ident; 
	bl = module_binders_list; mty_o = OPT is_module_type ->
	  VernacDeclareModuleType id bl mty_o

	  (* This end a Section a Module or a Module Type *)

      | IDENT "End"; id = ident -> VernacEndSegment id


(* Transparent and Opaque *)
      | IDENT "Transparent"; l = LIST1 qualid -> VernacSetOpacity (false, l)
      | IDENT "Opaque"; l = LIST1 qualid -> VernacSetOpacity (true, l)

(* Canonical structure *)
      | IDENT "Canonical"; IDENT "Structure"; qid = qualid ->
	  VernacCanonical qid
      | IDENT "Canonical"; IDENT "Structure"; qid = qualid; d = def_body ->
          let s = Ast.coerce_qualid_to_id qid in
	  VernacDefinition (Definition,s,d,Recordobj.add_object_hook)
(*
	  VernacDefinition (Definition,s,None,c,t,Recordobj.add_object_hook)
*)
      (* Rem: LOBJECT, OBJCOERCION, LOBJCOERCION have been removed
         (they were unused and undocumented) *)

(* Coercions *)
      | IDENT "Coercion"; qid = qualid; d = def_body ->
          let s = Ast.coerce_qualid_to_id qid in
(*
	  VernacDefinition (Definition,s,None,c,t,Class.add_coercion_hook)
*)
	  VernacDefinition (Definition,s,d,Class.add_coercion_hook)
      | IDENT "Coercion"; IDENT "Local"; qid = qualid; d = def_body ->
           let s = Ast.coerce_qualid_to_id qid in
	  VernacDefinition (LocalDefinition,s,d,Class.add_coercion_hook)
      | IDENT "Identity"; IDENT "Coercion"; IDENT "Local"; f = Prim.ident;
         ":"; s = class_rawexpr; ">->"; t = class_rawexpr -> 
	   VernacIdentityCoercion (Declare.make_strength_0 (), f, s, t)
      | IDENT "Identity"; IDENT "Coercion"; f = Prim.ident; ":";
         s = class_rawexpr; ">->"; t = class_rawexpr -> 
	   VernacIdentityCoercion (Libnames.NeverDischarge, f, s, t)
      | IDENT "Coercion"; IDENT "Local"; qid = qualid; ":";
	 s = class_rawexpr; ">->"; t = class_rawexpr -> 
	  VernacCoercion (Declare.make_strength_0 (), qid, s, t)
      | IDENT "Coercion"; qid = qualid; ":"; s = class_rawexpr; ">->";
         t = class_rawexpr ->
	  VernacCoercion (Libnames.NeverDischarge, qid, s, t)
      | IDENT "Class"; IDENT "Local"; c = qualid ->
	  Pp.warning "Class is obsolete"; VernacNop
      | IDENT "Class"; c = qualid ->
	  Pp.warning "Class is obsolete"; VernacNop

(* Implicit *)
      | IDENT "Syntactic"; "Definition"; id = ident; ":="; c = constr;
         n = OPT [ "|"; n = natural -> n ] ->
	   VernacSyntacticDefinition (id,c,n)

      | IDENT "Implicits"; qid = qualid; "["; l = LIST0 natural; "]" ->
	  VernacDeclareImplicits (qid,Some l)
      | IDENT "Implicits"; qid = qualid -> VernacDeclareImplicits (qid,None)

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
      | IDENT "Read"; IDENT "Module"; qidl = LIST1 qualid ->
	  VernacRequire (None, None, qidl)
      | IDENT "Require"; export = export_token; specif = specif_token;
        qidl = LIST1 qualid -> VernacRequire (Some export, specif, qidl)
      | IDENT "Require"; export = export_token; specif = specif_token;
        id = Prim.ident; filename = STRING -> 
	  VernacRequireFrom (export, specif, id, filename)
(*
      | IDENT "Write"; IDENT "Module"; id = identarg -> ExtraVernac 
	  <:ast< (WriteModule $id) >>
      | IDENT "Write"; IDENT "Module"; id = identarg; s = stringarg -> ExtraVernac 
	  <:ast< (WriteModule $id $s) >>
*)
      | IDENT "Declare"; IDENT "ML"; IDENT "Module"; l = LIST1 STRING ->
	  VernacDeclareMLModule l
      | IDENT "Import"; qidl = LIST1 qualid -> VernacImport (false,qidl)
      | IDENT "Export"; qidl = LIST1 qualid -> VernacImport (true,qidl)
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
      | IDENT "Reset"; id = Prim.ident -> VernacResetName id
      | IDENT "Reset"; IDENT "Initial" -> VernacResetInitial
      | IDENT "Back" -> VernacBack 1
      | IDENT "Back"; n = Prim.natural -> VernacBack n

(* Tactic Debugger *)
      |	IDENT "Debug"; IDENT "On" -> VernacDebug true
      |	IDENT "Debug"; IDENT "Off" -> VernacDebug false

 ] ];
    END
;;
