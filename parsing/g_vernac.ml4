
(*i camlp4deps: "parsing/grammar.cma" i*)

(* $Id$ *)

open Pcoq
open Pp
open Tactic
open Util
open Vernac

GEXTEND Gram
  GLOBAL: vernac;
  vernac:
    [ [ g = gallina -> g 
      | g = gallina_ext -> g
      | c = command -> c 
      | c = syntax -> c
      | "["; l = vernac_list_tail -> <:ast< (VernacList ($LIST $l)) >> ] ]
  ;
  vernac: LAST
    [ [ tac = tacarg; "." -> <:ast< (SOLVE 1 (TACTIC $tac)) >> ] ]
  ;
  vernac_list_tail:
    [ [ v = vernac; l = vernac_list_tail -> v :: l
      | "]"; "." -> [] ] ]
  ;
END

(* Gallina declarations *)
GEXTEND Gram
  GLOBAL: gallina gallina_ext;

  theorem_body_line:
    [ [ n = numarg; ":"; tac = tacarg; "." ->
          <:ast< (VERNACCALL {SOLVE} $n (TACTIC $tac)) >>
      | tac = tacarg; "." -> <:ast< (VERNACCALL {SOLVE} 1 (TACTIC $tac)) >>
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
      | IDENT "Remark" -> <:ast< "REMARK" >> ] ]
  ;
  def_tok:
    [ [ "Definition" -> <:ast< "DEFINITION" >>
      | IDENT "Local" -> <:ast< "LOCAL" >> 
      | "@"; "Definition"  -> <:ast< "OBJECT" >>
      | "@"; IDENT "Local"  -> <:ast< "LOBJECT" >>
      | "@"; IDENT "Coercion"  -> <:ast< "OBJCOERCION" >>
      | "@"; IDENT "Local"; IDENT "Coercion"  -> <:ast< "LOBJCOERCION" >>
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
    [ [ idl = Constr.ne_binders_list -> idl
      | -> [] ] ]
  ;
  gallina:
    (* Definition, Goal *)
    [ [ thm = thm_tok; id = identarg; ":"; c = constrarg; "." ->
          <:ast< (StartProof $thm $id $c) >>
      | thm = thm_tok; id = identarg; ":"; c = constrarg; ":="; "Proof";
        tb = theorem_body; "Qed"; "." ->
          <:ast< (TheoremProof $thm $id $c $tb) >>

      | def = def_tok; s = identarg; bl = binders_list;
	":"; t = Constr.constr; "." ->
          <:ast< (StartProof $def $s (CONSTR ($ABSTRACT "PRODLIST" $bl $t))) >>
      | def = def_tok; s = identarg; bl = binders_list;
	":="; red = reduce; c = Constr.constr; "." ->
          <:ast< (DEFINITION $def $s (CONSTR ($ABSTRACT "LAMBDALIST" $bl $c))
		    ($LIST $red)) >>
      | def = def_tok; s = identarg; bl = binders_list;
	":="; red = reduce; c = Constr.constr; ":"; t = Constr.constr; "." ->
          <:ast< (DEFINITION $def $s (CONSTR ($ABSTRACT "LAMBDALIST" $bl $c)) 
		    (CONSTR ($ABSTRACT "PRODLIST" $bl $t)) ($LIST $red)) >>
      | def = def_tok; s = identarg; bl = binders_list;
	":"; t = Constr.constr; ":="; red = reduce; c = Constr.constr; "." ->
          <:ast< (DEFINITION $def $s (CONSTR ($ABSTRACT "LAMBDALIST" $bl $c))
		    (CONSTR ($ABSTRACT "PRODLIST" $bl $t)) ($LIST $red)) >>

      | hyp = hyp_tok; bl = ne_params_list; "." ->
          <:ast< (VARIABLE $hyp  (BINDERLIST ($LIST $bl))) >>
      | hyp = hyps_tok; bl = ne_params_list; "." ->
          <:ast< (VARIABLE $hyp  (BINDERLIST ($LIST $bl))) >>
      | hyp = param_tok; bl = ne_params_list; "." ->
          <:ast< (PARAMETER $hyp (BINDERLIST ($LIST $bl))) >>
      | hyp = params_tok; bl = ne_params_list; "." ->
          <:ast< (PARAMETER $hyp (BINDERLIST ($LIST $bl))) >>
      ] ]
  ;
  gallina_ext:
      [ [ IDENT "Abstraction"; id = identarg; "["; l = ne_numarg_list; "]";
        ":="; c = constrarg; "." ->
          <:ast< (ABSTRACTION $id $c ($LIST $l)) >>
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
    [ [ id = IDENT; ":"; c = Constr.constr ->
          <:ast< (BINDER $c ($VAR $id)) >> ] ]
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
    [ [ id = identarg; ":="; dep = dep; indid = identarg; IDENT "Sort";
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
          <:ast< (VERNACARGLIST ($STR $oc) $id $c) >>
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
    [ [ c = Vernac.identarg -> <:ast< (VERNACARGLIST $c) >>
      |  -> <:ast< (VERNACARGLIST) >> ] ]
  ;
  gallina_ext:
    [ [ IDENT "Mutual"; bl = ne_simple_binders_list ; f = finite_tok;
        indl = block_old_style; "." ->
          <:ast< (OLDMUTUALINDUCTIVE (BINDERLIST ($LIST $bl)) $f
                                     (VERNACARGLIST ($LIST $indl))) >>
      | record_tok; oc = opt_coercion; name = identarg; ps = indpar; ":";
	s = sortarg; ":="; c = rec_constr; "{"; fs = fields; "}"; "." ->
          <:ast< (RECORD ($STR $oc) $name $ps $s $c $fs) >>
(*      | record_tok; ">"; name = identarg; ps = indpar; ":";
	s = sortarg; ":="; c = rec_constr; "{"; fs = fields; "}"; "." ->
          <:ast< (RECORD "COERCION" $name $ps $s $c $fs) >>
*)      ] ]
  ;
  gallina:
    [ [ IDENT "Mutual"; f = finite_tok; indl = block; "." ->
          <:ast< (MUTUALINDUCTIVE $f (VERNACARGLIST ($LIST $indl))) >>
      | "Fixpoint"; recs = specifrec; "." ->
          <:ast< (MUTUALRECURSIVE (VERNACARGLIST ($LIST $recs))) >>
      | "CoFixpoint"; corecs = specifcorec; "." ->
          <:ast< (MUTUALCORECURSIVE (VERNACARGLIST ($LIST $corecs))) >>
      | IDENT "Scheme"; schemes = specifscheme; "." ->
          <:ast< (INDUCTIONSCHEME (VERNACARGLIST ($LIST $schemes))) >>
      | f = finite_tok; s = sortarg; id = identarg; indpar = indpar; ":=";
        lc = constructor_list; "." ->
          <:ast< (ONEINDUCTIVE $f $id $s $indpar $lc) >>
      | f = finite_tok; indl = block; "." ->
          <:ast< (MUTUALINDUCTIVE $f (VERNACARGLIST ($LIST $indl))) >>

      | record_tok; oc = opt_coercion; name = identarg; ps = indpar; ":";
	s = sortarg; ":="; c = rec_constr; "{"; fs = fields; "}"; "." ->
          <:ast< (RECORD ($STR $oc) $name $ps $s $c $fs) >>
(*      | record_tok; ">"; name = identarg; ps = indpar; ":";
	s = sortarg; ":="; c = rec_constr; "{"; fs = fields; "}"; "." ->
          <:ast< (RECORD "COERCION" $name $ps $s $c $fs) >>
*)      ] ];

  END

GEXTEND Gram
  GLOBAL: gallina_ext;

  gallina_ext:
    [ [ 

(* Sections *)
	IDENT "Section"; id = identarg; "." -> <:ast< (BeginSection $id) >>
      | IDENT "Chapter"; id = identarg; "." -> <:ast< (BeginSection $id) >>
      | IDENT "Module"; id = identarg; "." -> <:ast< (BeginModule $id) >>
      | IDENT "End"; id = identarg; "." -> <:ast< (EndSection $id) >>

(* Transparent and Opaque *)
      | IDENT "Transparent"; l = ne_identarg_list; "." ->
          <:ast< (TRANSPARENT ($LIST $l)) >>
      | IDENT "Opaque"; l = ne_identarg_list; "." -> 
	  <:ast< (OPAQUE ($LIST $l)) >>

(* Coercions *)
      | IDENT "Coercion"; s = identarg; ":="; c = Constr.constr; "." ->
          <:ast< (DEFINITION "COERCION" $s (CONSTR $c)) >>
      | IDENT "Coercion"; s = identarg; ":="; c1 = Constr.constr; ":";
         c2 = Constr.constr; "." ->
          <:ast< (DEFINITION "COERCION" $s (CONSTR (CAST $c1 $c2))) >>
      | IDENT "Coercion"; IDENT "Local"; s = identarg; ":="; 
	 c = constrarg; "." ->
          <:ast< (DEFINITION "LCOERCION" $s $c) >>
      | IDENT "Coercion"; IDENT "Local"; s = identarg; ":="; 
	 c1 = Constr.constr; ":"; c2 = Constr.constr; "." ->
          <:ast< (DEFINITION "LCOERCION" $s (CONSTR (CAST $c1 $c2))) >>
      | IDENT "Identity"; IDENT "Coercion"; IDENT "Local"; f = identarg;
         ":"; c = identarg; ">->"; d = identarg; "." ->
          <:ast< (COERCION "LOCAL" "IDENTITY" $f $c $d) >>
      | IDENT "Identity"; IDENT "Coercion"; f = identarg; ":";
         c = identarg; ">->"; d = identarg; "." ->
          <:ast< (COERCION "" "IDENTITY" $f $c $d) >>
      | IDENT "Coercion"; IDENT "Local"; f = identarg; ":"; c = identarg;
        ">->"; d = identarg; "." ->
          <:ast< (COERCION "LOCAL" "" $f $c $d) >>
      | IDENT "Coercion"; f = identarg; ":"; c = identarg; ">->";
         d = identarg; "." -> <:ast< (COERCION "" "" $f $c $d) >>
      | IDENT "Class"; IDENT "Local"; c = identarg; "." ->
          <:ast< (CLASS "LOCAL" $c) >>
      | IDENT "Class"; c = identarg; "." -> <:ast< (CLASS "" $c) >>

(* Implicit *)
      | IDENT "Syntactic"; "Definition"; id = identarg; ":="; com = constrarg;
         "." -> <:ast< (SyntaxMacro $id $com) >>
      | IDENT "Syntactic"; "Definition"; id = identarg; ":="; com = constrarg;
         "|"; n = numarg; "." -> <:ast< (SyntaxMacro $id $com $n) >>
      | IDENT "Implicit"; IDENT "Arguments"; IDENT "On"; "." ->
          <:ast< (IMPLICIT_ARGS_ON) >>
      | IDENT "Implicit"; IDENT "Arguments"; IDENT "Off"; "." ->
          <:ast< (IMPLICIT_ARGS_OFF) >>
      | IDENT "Implicits"; id = identarg; "["; l = numarg_list; "]"; "." ->
          <:ast< (IMPLICITS "" $id ($LIST $l)) >>
      | IDENT "Implicits"; id = identarg; "." ->
          <:ast< (IMPLICITS "Auto" $id) >> 
  ] ]
  ;
END

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
    [ [ 

(* State management *)
        IDENT "Write"; IDENT "State"; id = identarg; "." ->
          <:ast< (WriteState $id) >>
      | IDENT "Write"; IDENT "State"; s = stringarg; "." ->
          <:ast< (WriteState $s) >>
      | IDENT "Restore";  IDENT "State"; id = identarg; "." ->
          <:ast< (RestoreState $id) >>
      | IDENT "Restore";  IDENT "State"; s = stringarg; "." ->
          <:ast< (RestoreState $s) >>
      | IDENT "Reset"; id = identarg; "." -> <:ast< (ResetName $id) >>
      | IDENT "Reset"; IDENT "Initial"; "." -> <:ast< (ResetInitial) >>
      | IDENT "Reset"; IDENT "Section"; id = identarg; "." ->
          <:ast< (ResetSection $id) >>

(* Modules management *)   
      | "Load"; verbosely = [ IDENT "Verbose" -> "Verbose" | -> "" ];
	s = [ s = STRING -> s | s = IDENT -> s ]; "." ->
          <:ast< (LoadFile ($STR $verbosely) ($STR $s)) >>
      | "Compile";
	verbosely =
          [ IDENT "Verbose" -> "Verbose"
          | -> "" ];
	IDENT "Module";
	only_spec =
          [ IDENT "Specification" -> "Specification"
          | -> "" ];
	mname = [ s = STRING -> s | s = IDENT -> s ];
	fname = OPT [ s = STRING -> s | s = IDENT -> s ]; "." ->
          let fname = match fname with Some s -> s | None -> mname in
            <:ast< (CompileFile ($STR $verbosely) ($STR $only_spec)
                      ($STR $mname) ($STR $fname))>>
      | IDENT "Read"; IDENT "Module"; id = identarg; "." ->
          <:ast< (ReadModule $id) >>
      | IDENT "Require"; import = import_tok; specif = specif_tok;
        id = identarg; "." -> <:ast< (Require $import $specif $id) >>
      | IDENT "Require"; import = import_tok; specif = specif_tok;
        id = identarg; filename = stringarg; "." ->
          <:ast< (RequireFrom $import $specif $id $filename) >>
      | IDENT "Write"; IDENT "Module"; id = identarg; "." -> 
	  <:ast< (WriteModule $id) >>
      | IDENT "Write"; IDENT "Module"; id = identarg; s = stringarg; "." -> 
	  <:ast< (WriteModule $id $s) >>
      | IDENT "Begin"; IDENT "Silent"; "." -> <:ast< (BeginSilent) >>
      | IDENT "End"; IDENT "Silent"; "." -> <:ast< (EndSilent) >>
      | IDENT "Declare"; IDENT "ML"; IDENT "Module";
        l = ne_stringarg_list; "." -> <:ast< (DeclareMLModule ($LIST $l)) >>
      | IDENT "Import"; id = identarg; "." -> <:ast< (ImportModule $id) >>
      
(* Extraction *)
      | IDENT "Extraction"; id = identarg; "." ->
          <:ast< (PrintExtractId $id) >>
      | IDENT "Extraction"; "." -> <:ast< (PrintExtract) >>

(* Tactic Debugger *)
      |	IDENT "Debug"; IDENT "On"; "." -> <:ast< (DebugOn) >>
      |	IDENT "Debug"; IDENT "Off"; "." -> <:ast< (DebugOff) >>

 ] ];
    END

(* Proof commands *)
GEXTEND Gram
  GLOBAL: command ne_constrarg_list;

  destruct_location :
  [ [ IDENT "Conclusion"  -> <:ast< (CONCL)>>
    | IDENT "Discardable"; "Hypothesis"  -> <:ast< (DiscardableHYP)>>
    | "Hypothesis"   -> <:ast< (PreciousHYP)>> ]]
  ;
  ne_constrarg_list:
  [ [ l = LIST1 constrarg -> l ] ]
  ;
  opt_identarg_list:
  [ [ -> []
    | ":"; l = LIST1 identarg -> l ] ]
  ;
  vrec_clause:
    [ [ name=identarg; it=LIST1 input_fun; ":="; body=tactic_expr ->
          <:ast<(RECCLAUSE $name (FUNVAR ($LIST $it)) $body)>> ] ]
  ;
  command:
    [ [ IDENT "Goal"; c = constrarg; "." -> <:ast< (GOAL $c) >>
      | IDENT "Goal"; "." -> <:ast< (GOAL) >>
      | "Proof"; "." -> <:ast< (GOAL) >>
      | IDENT "Abort"; "." -> <:ast< (ABORT) >>
      | "Qed"; "." -> <:ast< (SaveNamed) >>
      | IDENT "Save"; "." -> <:ast< (SaveNamed) >>
      | IDENT "Defined"; "." -> <:ast< (DefinedNamed) >>
      | IDENT "Save"; IDENT "Remark"; id = identarg; "." ->
          <:ast< (SaveAnonymousRmk $id) >>
      | IDENT "Save"; IDENT "Theorem"; id = identarg; "." ->
          <:ast< (SaveAnonymousThm $id) >>
      | IDENT "Save"; id = identarg; "." -> <:ast< (SaveAnonymousThm $id) >>
      | IDENT "Suspend"; "." -> <:ast< (SUSPEND) >>
      | IDENT "Resume"; "." -> <:ast< (RESUME) >>
      | IDENT "Resume"; id = identarg; "." -> <:ast< (RESUME $id) >>
      | IDENT "Abort"; IDENT "All"; "." -> <:ast< (ABORTALL) >>
      | IDENT "Abort"; id = identarg; "." -> <:ast< (ABORT $id) >>
      | IDENT "Restart"; "." -> <:ast< (RESTART) >>
      | "Proof"; c = constrarg; "." -> <:ast< (PROOF $c) >>
      | IDENT "Undo"; "." -> <:ast< (UNDO 1) >>
      | IDENT "Undo"; n = numarg; "." -> <:ast< (UNDO $n) >>
      | IDENT "Show"; n = numarg; "." -> <:ast< (SHOW $n) >>
      | IDENT "Show"; IDENT "Implicits"; n = numarg; "." ->
          <:ast< (SHOWIMPL $n) >>
      | IDENT "Focus"; "." -> <:ast< (FOCUS) >>
      | IDENT "Focus"; n = numarg; "." -> <:ast< (FOCUS $n) >>
      | IDENT "Unfocus"; "." -> <:ast< (UNFOCUS) >>
      | IDENT "Show"; "." -> <:ast< (SHOW) >>
      | IDENT "Show"; IDENT "Implicits"; "." -> <:ast< (SHOWIMPL) >>
      | IDENT "Show"; IDENT "Node"; "." -> <:ast< (ShowNode) >>
      | IDENT "Show"; IDENT "Script"; "." -> <:ast< (ShowScript) >>
      | IDENT "Show"; IDENT "Existentials"; "." -> <:ast< (ShowEx) >>
      | IDENT "Existential"; n = numarg; ":="; c = constrarg; "." ->
          <:ast< (EXISTENTIAL $n $c) >>
      | IDENT "Existential"; n = numarg; ":="; c1 = Constr.constr; ":";
        c2 = Constr.constr; "." ->
          <:ast< (EXISTENTIAL $n (CONSTR (CAST $c1 $c2))) >>
      | IDENT "Existential"; n = numarg; ":"; c2 = Constr.constr; ":=";
        c1 = Constr.constr; "." ->
          <:ast< (EXISTENTIAL $n (CONSTR (CAST $c1 $c2))) >>
      | IDENT "Explain"; "Proof"; l = numarg_list; "." ->
          <:ast< (ExplainProof ($LIST $l)) >>
      | IDENT "Explain"; "Proof"; IDENT "Tree"; l = numarg_list; "." ->
          <:ast< (ExplainProofTree ($LIST $l)) >>
      | IDENT "Go"; n = numarg; "." -> <:ast< (Go $n) >>
      | IDENT "Go"; IDENT "top"; "." -> <:ast< (Go "top") >>
      | IDENT "Go"; IDENT "prev"; "." -> <:ast< (Go "prev") >>
      | IDENT "Go"; IDENT "next"; "." -> <:ast< (Go "next") >>
      | IDENT "Show"; "Proof"; "." -> <:ast< (ShowProof) >>
      | IDENT "Guarded"; "." -> <:ast< (CheckGuard) >>
      | IDENT "Show"; IDENT "Tree"; "." -> <:ast< (ShowTree) >>
      | IDENT "Show"; IDENT "Conjectures"; "." -> <:ast< (ShowProofs) >>

(* Tactic Definition *)

      |IDENT "Tactic"; "Definition"; name=identarg; ":="; body=Tactic.tactic;
        "." -> <:ast<(TACDEF $name (AST $body))>>
      |IDENT "Tactic"; "Definition"; name=identarg; largs=LIST1 input_fun;
        ":="; body=Tactic.tactic; "." ->
        <:ast<(TACDEF $name (AST (FUN (FUNVAR ($LIST $largs)) $body)))>>
      |IDENT "Recursive"; IDENT "Tactic"; "Definition"; vc=vrec_clause ; "." ->
        (match vc with
            Coqast.Node(_,"RECCLAUSE",nme::tl) ->
              <:ast<(TACDEF $nme (AST (REC $vc)))>>
           |_ ->
             anomalylabstrm "Gram.vernac" [<'sTR "Not a correct RECCLAUSE">])
      |IDENT "Recursive"; IDENT "Tactic"; "Definition"; vc=vrec_clause;
        IDENT "And"; vcl=LIST1 vrec_clause SEP IDENT "And"; "." ->
        let nvcl=
          List.fold_right
            (fun e b -> match e with
                Coqast.Node(_,"RECCLAUSE",nme::_) ->
                  nme::<:ast<(AST (REC $e))>>::b
               |_ ->
                 anomalylabstrm "Gram.vernac" [<'sTR
                   "Not a correct RECCLAUSE">]) (vc::vcl) []
        in
          <:ast<(TACDEF ($LIST $nvcl))>>

(* Hints for Auto and EAuto *)

      | IDENT "Hint"; hintname = identarg; dbname = opt_identarg_list; ":=";
	IDENT "Resolve"; c = constrarg; "." ->
	  <:ast<(HintResolve $hintname (VERNACARGLIST ($LIST $dbname)) $c)>>
	  
      | IDENT "Hint"; hintname = identarg; dbnames = opt_identarg_list; ":=";
	IDENT "Immediate"; c = constrarg; "." ->
	  <:ast<(HintImmediate $hintname (VERNACARGLIST ($LIST $dbnames)) $c)>>
	  
      | IDENT "Hint"; hintname = identarg; dbnames = opt_identarg_list; ":=";
	IDENT "Unfold"; c = identarg; "." ->
	  <:ast<(HintUnfold $hintname (VERNACARGLIST ($LIST $dbnames)) $c)>>
	  
      | IDENT "Hint"; hintname = identarg; dbnames = opt_identarg_list; ":=";
	IDENT "Constructors"; c = identarg;  "." ->
	  <:ast<(HintConstructors $hintname (VERNACARGLIST ($LIST $dbnames)) $c)>>
	  
      | IDENT "Hint"; hintname = identarg; dbnames = opt_identarg_list; ":=";
	IDENT "Extern"; n = numarg; c = constrarg ; tac = tacarg; "." ->
	  <:ast<(HintExtern $hintname (VERNACARGLIST ($LIST $dbnames)) 
		   $n $c (TACTIC $tac))>>
	  
      | IDENT "Hints"; IDENT "Resolve"; l = ne_identarg_list; 
	dbnames = opt_identarg_list; "." ->
          <:ast< (HintsResolve (VERNACARGLIST ($LIST $dbnames)) ($LIST $l)) >>
	  
      | IDENT "Hints"; IDENT "Immediate"; l = ne_identarg_list; 
	dbnames = opt_identarg_list; "." ->
          <:ast< (HintsImmediate (VERNACARGLIST ($LIST $dbnames)) ($LIST $l)) >>
	  
      | IDENT "Hints"; IDENT "Unfold"; l = ne_identarg_list;
	dbnames = opt_identarg_list; "." ->
          <:ast< (HintsUnfold (VERNACARGLIST ($LIST $dbnames)) ($LIST $l)) >>
	  
      | IDENT "HintDestruct"; 
                dloc = destruct_location;
                na  = identarg;
                hyptyp = constrarg;
                pri = numarg;
                tac = Prim.astact; "." -> 
          <:ast< (HintDestruct $na (AST $dloc) $hyptyp $pri (AST $tac))>>

      | n = numarg; ":"; tac = tacarg; "." ->
          <:ast< (SOLVE $n (TACTIC $tac)) >> 

(*This entry is not commented, only for debug*)
      | IDENT "PrintConstr"; com = constrarg; "." ->
          <:ast< (PrintConstr $com)>>
      ] ];
  END
