(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i camlp4deps: "parsing/grammar.cma" i*)

(* $Id$ *)

open Pcoq
open Pp
open Tactic
open Util
open Vernac_

(* Rem: do not join the different GEXTEND into one, it breaks native *)
(* compilation on PowerPC and Sun architectures *)

GEXTEND Gram
  GLOBAL: vernac;
  vernac:
    (* Better to parse "." here: in case of failure (e.g. in coerce_to_var), *)
    (* "." is still in the stream and discard_to_dot works correctly         *)
    [ [ g = gallina; "." -> g 
      | g = gallina_ext; "." -> g
      | c = command; "." -> c 
      | c = syntax; "." -> c
      | "["; l = vernac_list_tail -> <:ast< (VernacList ($LIST $l)) >>

      (* This is for "Grammar vernac" rules *)
      | id = Prim.metaident -> id ] ]
  ;
  vernac: FIRST
    [ [ IDENT "Time"; v = vernac  -> <:ast< (Time $v)>> ] ]
  ;
  vernac: LAST
    [ [ tac = tacarg; "." ->
        (match tac with
	| Coqast.Node(_,kind,_)
          when kind = "StartProof" || kind = "TheoremProof" -> tac
	| _ -> <:ast< (SOLVE 1 (TACTIC $tac)) >>) ] ]
  ;
  vernac_list_tail:
    [ [ v = vernac; l = vernac_list_tail -> v :: l
      | "]"; "." -> [] ] ]
  ;
END

(* Gallina declarations *)
GEXTEND Gram
  GLOBAL: gallina gallina_ext reduce thm_tok theorem_body;

  theorem_body_line:
    [ [ n = numarg; ":"; tac = tacarg; "." ->
          <:ast< (VERNACCALL "SOLVE" $n (TACTIC $tac)) >>
      | tac = tacarg; "." -> <:ast< (VERNACCALL "SOLVE" 1 (TACTIC $tac)) >>
      ] ]
  ;
  theorem_body_line_list:
    [ [ t = theorem_body_line -> [t]
      | t = theorem_body_line; l = theorem_body_line_list -> t :: l ] ]
  ;
  theorem_body:
    [ [ l = theorem_body_line_list ->
          <:ast< (VERNACARGLIST ($LIST $l)) >> ] ]
  ;
  thm_tok:
    [ [ "Theorem" -> <:ast< "THEOREM" >>
      | IDENT "Lemma" -> <:ast< "LEMMA" >>
      | IDENT "Fact" -> <:ast< "FACT" >>
      | IDENT "Remark" -> <:ast< "REMARK" >>
      | IDENT "Decl" -> <:ast< "DECL" >> ] ]
  ;
  def_tok:
    [ [ "Definition" -> <:ast< "DEFINITION" >>
      | IDENT "Local" -> <:ast< "LOCAL" >> 
      | IDENT "SubClass"  -> <:ast< "SUBCLASS" >>
      | IDENT "Local"; IDENT "SubClass"  -> <:ast< "LSUBCLASS" >> ] ]  
  ;
  hyp_tok:
    [ [ "Hypothesis" -> <:ast< "HYPOTHESIS" >>
      | "Variable" -> <:ast< "VARIABLE" >> ] ]
  ;
  hyps_tok:
    [ [ IDENT "Hypotheses" -> <:ast< "HYPOTHESES" >>
      | IDENT "Variables" -> <:ast< "VARIABLES" >> ] ]
  ;
  param_tok:
    [ [ "Axiom" -> <:ast< "AXIOM" >>
      | "Parameter" -> <:ast< "PARAMETER" >> ] ]
  ;
  params_tok:
    [ [ IDENT "Parameters" -> <:ast< "PARAMETERS" >> ] ]
  ;
  params:
    [ [ idl = Constr.ne_ident_comma_list; ":"; c = Constr.constr ->
          <:ast< (BINDER $c ($LIST $idl)) >> ] ]
  ;
  ne_params_list:
    [ [ id = params; ";"; idl = ne_params_list -> id :: idl
      | id = params -> [id] ] ]
  ;
  reduce:
    [ [ IDENT "Eval"; r = Tactic.red_tactic; "in" ->
        [ <:ast< (TACTIC_ARG (REDEXP $r)) >> ]
      | -> [] ] ]
  ;
  binders_list:
    [ [ idl = Constr.ne_binders_list -> <:ast< (BINDERS ($LIST $idl)) >>
      | -> <:ast< (BINDERS) >> ] ]
  ;
  gallina:
    (* Definition, Goal *)
    [ [ thm = thm_tok; id = identarg; ":"; c = constrarg ->
          <:ast< (StartProof $thm $id $c) >>
      | thm = thm_tok; id = identarg; ":"; c = constrarg; ":="; "Proof";
        tb = theorem_body; "Qed" ->
          <:ast< (TheoremProof $thm $id $c $tb) >>
      | def = def_tok; s = identarg; bl = binders_list;
	":"; t = Constr.constr ->
          <:ast< (StartProof $def $s (CONSTR ($ABSTRACT "PRODLIST" $bl $t))) >>
      | def = def_tok; s = identarg; bl = binders_list;
	":="; red = reduce; c = Constr.constr ->
          <:ast< (DEFINITION $def $s (CONSTR ($ABSTRACT "LAMBDALIST" $bl $c))
		    ($LIST $red)) >>
      | def = def_tok; s = identarg; bl = binders_list;
	":="; red = reduce; c = Constr.constr; ":"; t = Constr.constr ->
          <:ast< (DEFINITION $def $s (CONSTR ($ABSTRACT "LAMBDALIST" $bl $c)) 
		    (CONSTR ($ABSTRACT "PRODLIST" $bl $t)) ($LIST $red)) >>
      | def = def_tok; s = identarg; bl = binders_list;
	":"; t = Constr.constr; ":="; red = reduce; c = Constr.constr ->
          <:ast< (DEFINITION $def $s (CONSTR ($ABSTRACT "LAMBDALIST" $bl $c))
		    (CONSTR ($ABSTRACT "PRODLIST" $bl $t)) ($LIST $red)) >>

      | hyp = hyp_tok; bl = ne_params_list ->
          <:ast< (VARIABLE $hyp  (BINDERLIST ($LIST $bl))) >>
      | hyp = hyps_tok; bl = ne_params_list ->
          <:ast< (VARIABLE $hyp  (BINDERLIST ($LIST $bl))) >>
      | hyp = param_tok; bl = ne_params_list ->
          <:ast< (PARAMETER $hyp (BINDERLIST ($LIST $bl))) >>
      | hyp = params_tok; bl = ne_params_list ->
          <:ast< (PARAMETER $hyp (BINDERLIST ($LIST $bl))) >>
      ] ]
  ;
  END

(* Gallina inductive declarations *)
GEXTEND Gram
  GLOBAL: gallina gallina_ext;

  finite_tok:
    [ [ "Inductive" -> <:ast< "Inductive" >>
      | "CoInductive" -> <:ast< "CoInductive" >> ] ]
  ;
  record_tok:
    [ [ IDENT "Record" -> <:ast< "Record" >>
      | IDENT "Structure" -> <:ast< "Structure" >> ] ]
  ;
  constructor:
    [ [ id = identarg; ":"; c = Constr.constr ->
          <:ast< (BINDER $c $id) >> ] ]
  ;
  ne_constructor_list:
    [ [ idc = constructor; "|"; l = ne_constructor_list -> idc :: l
      | idc = constructor -> [idc] ] ]
  ;
  constructor_list:
    [ [ "|"; l = ne_constructor_list -> <:ast< (BINDERLIST ($LIST $l)) >>
      | l = ne_constructor_list -> <:ast< (BINDERLIST ($LIST $l)) >>
      |  -> <:ast< (BINDERLIST) >> ] ]
  ;
  block_old_style:
    [ [ ind = oneind_old_style; "with"; indl = block_old_style -> ind :: indl
      | ind = oneind_old_style -> [ind] ] ]
  ;
  oneind_old_style:
    [ [ id = identarg; ":"; c = constrarg; ":="; lc = constructor_list ->
          <:ast< (VERNACARGLIST $id $c $lc) >> ] ]
  ;
  block:
    [ [ ind = oneind; "with"; indl = block -> ind :: indl
      | ind = oneind -> [ind] ] ]
  ;
  oneind:
    [ [ id = identarg; indpar = indpar; ":"; c = constrarg; ":=";
	lc = constructor_list
      -> <:ast< (VERNACARGLIST $id $c $indpar $lc) >> ] ]
  ;
  indpar:
    [ [ bl = ne_simple_binders_list ->
          <:ast< (BINDERLIST ($LIST $bl)) >>
      |  -> <:ast< (BINDERLIST) >> ] ]
  ;
  opt_coercion:
    [ [ ">" -> "COERCION"
      |  -> "" ] ]
  ;
  of_type_with_opt_coercion:
    [ [ ":>" -> "COERCION"
      | ":"; ">" -> "COERCION"
      | ":" -> "" ] ]
  ;
  onescheme:
    [ [ id = identarg; ":="; dep = dep; indid = qualidarg; IDENT "Sort";
        s = sortarg ->
          <:ast< (VERNACARGLIST $id $dep $indid $s) >> ] ]
  ;
  specifscheme:
    [ [ rec_ = onescheme; "with"; recl = specifscheme -> rec_ :: recl
      | rec_ = onescheme -> [rec_] ] ]
  ;
  dep:
    [ [ IDENT "Induction"; IDENT "for" -> <:ast< "DEP" >>
      | IDENT "Minimality"; IDENT "for" -> <:ast< "NODEP" >> ] ]
  ;
  onerec:
    [ [ id = identarg; idl = ne_simple_binders_list; ":"; c = constrarg;
        ":="; def = constrarg ->
          <:ast< (VERNACARGLIST $id (BINDERLIST ($LIST $idl)) $c $def) >> ] ]
  ;
  specifrec:
    [ [ rec_ = onerec; "with"; recl = specifrec -> rec_ :: recl
      | rec_ = onerec -> [rec_] ] ]
  ;
  onecorec:
    [ [ id = identarg; ":"; c = constrarg; ":="; def = constrarg ->
          <:ast< (VERNACARGLIST $id $c $def) >> ] ]
  ;
  specifcorec:
    [ [ corec = onecorec; "with"; corecl = specifcorec -> corec :: corecl
      | corec = onecorec -> [corec] ] ]
  ;
  field:
    [ [ id = identarg; oc = of_type_with_opt_coercion; c = constrarg ->
          <:ast< (VERNACARGLIST ($STR $oc) "ASSUM" $id $c) >>
      | id = identarg; oc = of_type_with_opt_coercion; t = Constr.constr;
	":="; b = Constr.constr -> 
          <:ast< (VERNACARGLIST "" "DEF" $id $b (COMMAND (CAST $b $t))) >>
      | id = identarg; ":="; b = constrarg ->
          <:ast< (VERNACARGLIST "" "DEF" $id $b) >>
(*      | id = identarg; ":>"; c = constrarg ->
          <:ast< (VERNACARGLIST "COERCION" $id $c) >> *)] ]
  ;
  nefields:
    [ [ idc = field; ";"; fs = nefields -> idc :: fs
      | idc = field -> [idc] ] ]
  ;
  fields:
    [ [ fs = nefields -> <:ast< (VERNACARGLIST ($LIST $fs)) >>
      |  -> <:ast< (VERNACARGLIST) >> ] ]
  ;
  simple_params:
    [ [ idl = Constr.ne_ident_comma_list; ":"; c = Constr.constr ->
          <:ast< (BINDER $c ($LIST $idl)) >>
      | idl = Constr.ne_ident_comma_list ->
          <:ast< (BINDER (ISEVAR) ($LIST $idl)) >> ] ]
  ;
  ne_simple_params_list:
    [ [ id = simple_params; ";"; idl = ne_simple_params_list -> id :: idl
      | id = simple_params -> [id] ] ]
  ;
  simple_binders:
    [ [ "["; bl = ne_simple_params_list; "]" -> bl ] ]
  ;
  ne_simple_binders_list:
    [ [ bl = simple_binders; bll = ne_simple_binders_list -> bl @ bll
      | bl = simple_binders -> bl ] ]
  ;
  rec_constr:
    [ [ c = Vernac_.identarg -> <:ast< (VERNACARGLIST $c) >>
      |  -> <:ast< (VERNACARGLIST) >> ] ]
  ;
  gallina_ext:
    [ [ IDENT "Mutual"; bl = ne_simple_binders_list ; f = finite_tok;
        indl = block_old_style ->
          <:ast< (OLDMUTUALINDUCTIVE (BINDERLIST ($LIST $bl)) $f
                                     (VERNACARGLIST ($LIST $indl))) >>
      | record_tok; oc = opt_coercion; name = identarg; ps = indpar; ":";
	s = sortarg; ":="; c = rec_constr; "{"; fs = fields; "}" ->
          <:ast< (RECORD ($STR $oc) $name $ps $s $c $fs) >>
(*      | record_tok; ">"; name = identarg; ps = indpar; ":";
	s = sortarg; ":="; c = rec_constr; "{"; fs = fields; "}" ->
          <:ast< (RECORD "COERCION" $name $ps $s $c $fs) >>
*)      ] ]
  ;
  gallina:
    [ [ IDENT "Mutual"; f = finite_tok; indl = block ->
          <:ast< (MUTUALINDUCTIVE $f (VERNACARGLIST ($LIST $indl))) >>
      | "Fixpoint"; recs = specifrec ->
          <:ast< (MUTUALRECURSIVE (VERNACARGLIST ($LIST $recs))) >>
      | "CoFixpoint"; corecs = specifcorec ->
          <:ast< (MUTUALCORECURSIVE (VERNACARGLIST ($LIST $corecs))) >>
      | IDENT "Scheme"; schemes = specifscheme ->
          <:ast< (INDUCTIONSCHEME (VERNACARGLIST ($LIST $schemes))) >>
      | f = finite_tok; s = sortarg; id = identarg; indpar = indpar; ":=";
        lc = constructor_list ->
          <:ast< (ONEINDUCTIVE $f $id $s $indpar $lc) >>
      | f = finite_tok; indl = block ->
          <:ast< (MUTUALINDUCTIVE $f (VERNACARGLIST ($LIST $indl))) >>

      | record_tok; oc = opt_coercion; name = identarg; ps = indpar; ":";
	s = sortarg; ":="; c = rec_constr; "{"; fs = fields; "}" ->
          <:ast< (RECORD ($STR $oc) $name $ps $s $c $fs) >>
(*      | record_tok; ">"; name = identarg; ps = indpar; ":";
	s = sortarg; ":="; c = rec_constr; "{"; fs = fields; "}" ->
          <:ast< (RECORD "COERCION" $name $ps $s $c $fs) >>
*)      ] ];

  END

GEXTEND Gram
  GLOBAL: gallina_ext;

  def_body:
    [ [
	c1 = Constr.constr; ":"; c2 = Constr.constr ->
          <:ast< (CONSTR (CAST $c1 $c2)) >>
      | c = Constr.constr -> <:ast< (CONSTR $c) >>
  ] ];

  gallina_ext:
    [ [ 
(* Sections *)
	IDENT "Section"; id = identarg -> <:ast< (BeginSection $id) >>
      | IDENT "Chapter"; id = identarg -> <:ast< (BeginSection $id) >>
      | IDENT "Module"; id = identarg -> <:ast< (BeginModule $id) >>
      | IDENT "End"; id = identarg -> <:ast< (EndSection $id) >>

(* Transparent and Opaque *)
      | IDENT "Transparent"; l = ne_qualidarg_list ->
          <:ast< (TRANSPARENT ($LIST $l)) >>
      | IDENT "Opaque"; l = ne_qualidarg_list -> 
	  <:ast< (OPAQUE ($LIST $l)) >>

(* Canonical structure *)
      | IDENT "Canonical"; IDENT "Structure"; qid = qualidarg ->
          <:ast< (CANONICAL $qid) >>
      | IDENT "Canonical"; IDENT "Structure"; qid = qualidarg; ":"; 
	t = Constr.constr; ":="; c = Constr.constr ->
          let s = Ast.coerce_to_var qid in
          <:ast< (DEFINITION "OBJECT" $s (CONSTR $c) (CONSTR $t)) >>
      | IDENT "Canonical"; IDENT "Structure"; qid = qualidarg; ":="; 
	c = Constr.constr; ":"; t = Constr.constr ->
          let s = Ast.coerce_to_var qid in
          <:ast< (DEFINITION "OBJECT" $s (CONSTR $c) (CONSTR $t)) >>
      | IDENT "Canonical"; IDENT "Structure"; qid = qualidarg; ":="; 
	c = Constr.constr ->
          let s = Ast.coerce_to_var qid in
          <:ast< (DEFINITION "OBJECT" $s (CONSTR $c)) >>
      (* Rem: LOBJECT, OBJCOERCION, LOBJCOERCION have been removed
         (they were unused and undocumented *)

(* Coercions *)
      | IDENT "Coercion"; qid = qualidarg; ":="; c = def_body ->
          let s = Ast.coerce_to_var qid in
          <:ast< (DEFINITION "COERCION" $s $c) >>
      | IDENT "Coercion"; IDENT "Local"; qid = qualidarg; ":="; 
	 c = constrarg ->
           let s = Ast.coerce_to_var qid in
	    <:ast< (DEFINITION "LCOERCION" $s $c) >>
      | IDENT "Coercion"; IDENT "Local"; qid = qualidarg; ":="; 
	 c1 = Constr.constr; ":"; c2 = Constr.constr ->
          let s = Ast.coerce_to_var qid in
          <:ast< (DEFINITION "LCOERCION" $s (CONSTR (CAST $c1 $c2))) >>
      | IDENT "Identity"; IDENT "Coercion"; IDENT "Local"; f = qualidarg;
         ":"; c = qualidarg; ">->"; d = qualidarg ->
          <:ast< (COERCION "LOCAL" "IDENTITY" $f $c $d) >>
      | IDENT "Identity"; IDENT "Coercion"; f = qualidarg; ":";
         c = qualidarg; ">->"; d = qualidarg ->
          <:ast< (COERCION "" "IDENTITY" $f $c $d) >>
      | IDENT "Coercion"; IDENT "Local"; qid = qualidarg; ":"; c = qualidarg;
        ">->"; d = qualidarg ->
          <:ast< (COERCION "LOCAL" "" $qid $c $d) >>
      | IDENT "Coercion"; qid = qualidarg; ":"; c = qualidarg; ">->";
         d = qualidarg -> <:ast< (COERCION "" "" $qid $c $d) >>
      | IDENT "Class"; IDENT "Local"; c = qualidarg ->
          <:ast< (CLASS "LOCAL" $c) >>
      | IDENT "Class"; c = qualidarg -> <:ast< (CLASS "" $c) >>

(* Implicit *)
      | IDENT "Syntactic"; "Definition"; id = identarg; ":="; com = constrarg
         -> <:ast< (SyntaxMacro $id $com) >>
      | IDENT "Syntactic"; "Definition"; id = identarg; ":="; com = constrarg;
         "|"; n = numarg -> <:ast< (SyntaxMacro $id $com $n) >>
      | IDENT "Implicit"; IDENT "Arguments"; IDENT "On" ->
          <:ast< (IMPLICIT_ARGS_ON) >>
      | IDENT "Implicit"; IDENT "Arguments"; IDENT "Off" ->
          <:ast< (IMPLICIT_ARGS_OFF) >>
      | IDENT "Implicits"; qid = qualidarg; "["; l = numarg_list; "]" ->
          <:ast< (IMPLICITS "" $qid ($LIST $l)) >>
      | IDENT "Implicits"; qid = qualidarg ->
          <:ast< (IMPLICITS "Auto" $qid) >> 
  ] ]
  ;
END

(* Modules management *)   
GEXTEND Gram
  GLOBAL: command;

  import_tok:
    [ [ IDENT "Import" -> <:ast< "IMPORT" >>
      | IDENT "Export" -> <:ast< "EXPORT" >>
      |  -> <:ast< "IMPORT" >> ] ]
  ;
  specif_tok:
    [ [ IDENT "Implementation" -> <:ast< "IMPLEMENTATION" >>
      | IDENT "Specification" -> <:ast< "SPECIFICATION" >>
      |  -> <:ast< "UNSPECIFIED" >> ] ]
  ;
  command:
    [ [ "Load"; verbosely = [ IDENT "Verbose" -> "Verbose" | -> "" ];
	s = [ s = STRING -> s | s = IDENT -> s ] ->
          <:ast< (LoadFile ($STR $verbosely) ($STR $s)) >>
(*      | "Compile";
	verbosely =
          [ IDENT "Verbose" -> "Verbose"
          | -> "" ];
	IDENT "Module";
	only_spec =
          [ IDENT "Specification" -> "Specification"
          | -> "" ];
	mname = [ s = STRING -> s | s = IDENT -> s ];
	fname = OPT [ s = STRING -> s | s = IDENT -> s ] ->
          let fname = match fname with Some s -> s | None -> mname in
            <:ast< (CompileFile ($STR $verbosely) ($STR $only_spec)
                      ($STR $mname) ($STR $fname))>>
*)
      | IDENT "Read"; IDENT "Module"; qidl = LIST1 qualidarg ->
          <:ast< (ReadModule ($LIST $qidl)) >>
      | IDENT "Require"; import = import_tok; specif = specif_tok;
        qidl = LIST1 qualidarg ->
          <:ast< (Require $import $specif ($LIST $qidl)) >>
      | IDENT "Require"; import = import_tok; specif = specif_tok;
        qid = qualidarg; filename = stringarg ->
          <:ast< (RequireFrom $import $specif $qid $filename) >>
      | IDENT "Write"; IDENT "Module"; id = identarg -> 
	  <:ast< (WriteModule $id) >>
      | IDENT "Write"; IDENT "Module"; id = identarg; s = stringarg -> 
	  <:ast< (WriteModule $id $s) >>
      | IDENT "Declare"; IDENT "ML"; IDENT "Module";
        l = ne_stringarg_list -> <:ast< (DeclareMLModule ($LIST $l)) >>
      | IDENT "Import"; qidl = ne_qualidarg_list ->
          <:ast< (ImportModule ($LIST $qidl)) >>
      | IDENT "Export"; qidl = ne_qualidarg_list ->
          <:ast< (ExportModule ($LIST $qidl)) >>
  ] 
]
  ;
END

GEXTEND Gram
  GLOBAL: command;

  command:
    [ [ 

(* State management *)
        IDENT "Write"; IDENT "State"; id = identarg ->
          <:ast< (WriteState $id) >>
      | IDENT "Write"; IDENT "State"; s = stringarg ->
          <:ast< (WriteState $s) >>
      | IDENT "Restore";  IDENT "State"; id = identarg ->
          <:ast< (RestoreState $id) >>
      | IDENT "Restore";  IDENT "State"; s = stringarg ->
          <:ast< (RestoreState $s) >>
      | IDENT "Reset"; id = identarg -> <:ast< (ResetName $id) >>
      | IDENT "Reset"; IDENT "Initial" -> <:ast< (ResetInitial) >>
      | IDENT "Reset"; IDENT "Section"; id = identarg ->
          <:ast< (ResetSection $id) >>
      | IDENT "Back" -> <:ast<(Back)>>
      | IDENT "Back"; n = numarg -> <:ast<(Back $n)>>

(* Tactic Debugger *)
      | IDENT "Debug"; IDENT "On" -> <:ast< (DebugOn) >>
      |	IDENT "Debug"; IDENT "Off" -> <:ast< (DebugOff) >>

 ] ];
    END
;;
