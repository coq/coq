
(* $Id$ *)

open Util
open Gramext
open Pp
open Pcoq
open Coqast
open Ast

open Vernac

GEXTEND Gram
  vernac:
    [ RIGHTA
     [ "Drop"; "." -> <:ast< (DROP) >>
     | "ProtectedLoop"; "." -> <:ast< (PROTECTEDLOOP)>>
     | "Load"; verbosely = [ IDENT "Verbose" -> "Verbose" | -> "" ];
       s = [ s = STRING -> s | s = IDENT -> s ]; "." ->
         <:ast< (LoadFile ($STR $verbosely) ($STR $s)) >>

     (* TODO: deplacer vers g_vernac & Vernac.v *)
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
                   ($STR $mname) ($STR $fname))>> ]]
  ;
END

(* These are the entries without which MakeBare cannot be compiled *)
GEXTEND Gram
  GLOBAL: vernac Prim.syntax_entry Prim.grammar_entry;

  vernac:
    [[ "Token"; s = STRING; "." -> <:ast< (TOKEN ($STR $s)) >>

     | "Grammar"; univ=IDENT; tl=LIST1 Prim.grammar_entry SEP "with"; "." ->
         <:ast< (GRAMMAR ($VAR univ) (ASTLIST ($LIST tl))) >>

     | "Syntax"; whatfor=IDENT; el=LIST1 Prim.syntax_entry SEP ";"; "." ->
         <:ast< (SYNTAX ($VAR whatfor) (ASTLIST ($LIST el))) >>
     | IDENT "Infix"; as_ = entry_prec; n = numarg; op = Prim.string;
       p = identarg; "." -> <:ast< (INFIX (AST $as_) $n $op $p) >>
     | IDENT "Distfix"; as_ = entry_prec; n = numarg; s = Prim.string;
       p = identarg; "." -> <:ast< (DISTFIX (AST $as_) $n $s $p) >> ]]
  ;

  (* Syntax entries for Grammar. Only grammar_entry is exported *)
  Prim.grammar_entry:
    [[ nont = Prim.ident; etyp = Prim.entry_type; ":=";
       ep = entry_prec; rl = LIST0 grammar_rule SEP "|" ->
         <:ast< (ENTRY $nont $etyp $ep ($LIST rl)) >> ]]
  ;
  entry_prec:
    [[ IDENT "LEFTA" -> <:ast< {LEFTA} >>
     | IDENT "RIGHTA" -> <:ast< {RIGHTA} >>
     | IDENT "NONA" -> <:ast< {NONA} >>
     | ->  <:ast< {NONE} >> ] ]
  ;
  grammar_rule:
    [[ name = rule_name; "["; pil = LIST0 production_item; "]"; "->";
       a = Prim.astact ->
        <:ast< (RULE ($ID name) $a ($LIST pil)) >> ]]
  ;
  rule_name:
    [[ name = IDENT -> name ]]
  ;
  production_item:
    [[ s = STRING -> <:ast< ($STR $s) >>
     | nt = non_terminal; po = OPT [ "("; p = Prim.ident; ")" -> p ] ->
         match po with
           | Some p -> <:ast< (NT $nt $p) >>
           | _ -> <:ast< (NT $nt) >> ]]
  ;
  non_terminal:
    [[ u = Prim.ident; ":"; nt = Prim.ident -> <:ast< (QUAL $u $nt) >>
     | nt = Prim.ident -> <:ast< $nt >> ]]
  ;


  (* Syntax entries for Syntax. Only syntax_entry is exported *)
  Prim.syntax_entry:
    [ [ IDENT "level"; p = precedence; ":"; rl = LIST1 syntax_rule SEP "|" ->
          <:ast< (SYNTAXENTRY $p ($LIST $rl)) >> ] ]
  ;
  syntax_rule:
    [ [ nm = IDENT; "["; s = Prim.astpat; "]"; "->"; u = unparsing ->
          <:ast< (RULE ($ID $nm) $s $u) >> ] ]
  ;
  precedence:
    [ [ a = Prim.number ->  <:ast< (PREC $a 0 0) >>
      | "["; a1 = Prim.number; a2 = Prim.number; a3 = Prim.number; "]" ->
          <:ast< (PREC $a1 $a2 $a3) >> ] ]
  ;
  unparsing:
    [ [ "["; ll = LIST0 next_hunks; "]" -> <:ast< (UNPARSING ($LIST $ll))>> ] ]
  ;
  next_hunks:
    [ [ IDENT "FNL" -> <:ast< (UNP_FNL) >>
      | IDENT "TAB" -> <:ast< (UNP_TAB) >>
      | c = STRING -> <:ast< (RO ($STR $c)) >>
      | "[";
        x =
          [ b = box; ll = LIST0 next_hunks -> <:ast<(UNP_BOX $b ($LIST $ll))>>
          | n = Prim.number; m = Prim.number -> <:ast< (UNP_BRK $n $m) >>
          | IDENT "TBRK";
            n = Prim.number; m = Prim.number -> <:ast< (UNP_TBRK $n $m) >> ];
        "]" -> x
      | e = Prim.ast; oprec = OPT [ ":"; pr = paren_reln -> pr ] ->
            match oprec with
	      | Some pr -> <:ast< (PH $e $pr) >>
              | None -> <:ast< (PH $e {Any}) >> ]]
  ;
  box:
    [ [ "<"; bk = box_kind; ">" -> bk ] ]
  ;
  box_kind:
    [ [ IDENT "h"; n = Prim.number -> <:ast< (PpHB $n) >>
      | IDENT "v"; n = Prim.number -> <:ast< (PpVB $n) >>
      | IDENT "hv"; n = Prim.number -> <:ast< (PpHVB $n) >>
      | IDENT "hov"; n = Prim.number -> <:ast< (PpHOVB $n) >>
      | IDENT "t" -> <:ast< (PpTB) >> ] ]
  ;
  paren_reln:
    [ [ IDENT "L" -> <:ast< {L} >>
      | IDENT "E" -> <:ast< {E} >>
      | pprim = STRING -> <:ast< ($STR $pprim) >> ] ]
  ;
END



(* Converting and checking grammar command *)

type nonterm =
  | NtShort of string
  | NtQual of string * string

type prod_item =
  | Term of Token.pattern
  | NonTerm of nonterm * entry_type * string option

type grammar_rule = {
  gr_name : string; 
  gr_production : prod_item list; 
  gr_action : Ast.act }

type grammar_entry = { 
  ge_name : string;
  ge_type : entry_type;
  gl_assoc : g_assoc option;
  gl_rules : grammar_rule list }

type grammar_command = { 
  gc_univ : string; 
  gc_entries : grammar_entry list }

let is_ident_not_keyword s =
  match s.[0] with
    | 'a'..'z' | 'A'..'Z' | '_' -> not (Lexer.is_keyword s)
    | _ -> false

let is_number s =
  match s.[0] with
    | '0'..'9' -> true
    | _ -> false

let strip s =
  let len =
    let rec loop i len =
      if i = String.length s then len
      else if s.[i] == ' ' then loop (i + 1) len
      else loop (i + 1) (len + 1)
    in
    loop 0 0
  in
  if len == String.length s then s
  else
    let s' = String.create len in
    let rec loop i i' =
      if i == String.length s then s'
      else if s.[i] == ' ' then loop (i + 1) i'
      else begin s'.[i'] <- s.[i]; loop (i + 1) (i' + 1) end
    in
    loop 0 0

let terminal s =
  let s = strip s in
  if s = "" then failwith "empty token";
  if is_ident_not_keyword s then ("IDENT", s)
  else if is_number s then ("INT", s)
  else ("", s)



let qualified_nterm current_univ ntrm =
  match ntrm with
      NtQual (univ, en) -> (get_univ univ, en)
    | NtShort en -> (current_univ, en)


let nterm univ ast =
  let nont =
    match ast with
      | Node (_, "QUAL", [Id (_, u); Id (_, nt)]) -> NtQual (u, nt)
      | Id (_, nt) -> NtShort nt
      | _ -> invalid_arg_loc (Ast.loc ast, "Extend.nterm") 
  in
  let (u,n) = qualified_nterm univ nont in
  let e =
    try 
      get_entry u n
    with UserError _ -> 
      user_err_loc(loc ast,"Externd.nterm", [< 'sTR"unknown grammar entry" >])
  in
  (nont, type_of_entry e)

let prod_item univ env ast =
  match ast with
    | Str (_, s) -> env, Term (terminal s)
    | Node (_, "NT", [nt; Id (locp, p)]) ->
	let (nont, etyp) = nterm univ nt in
        if isMeta p then 
	  ((p, etyp) :: env, NonTerm (nont, etyp, Some p))
        else 
	  user_err_loc
            (locp,"Extend.prod_item",
             [< 'sTR"This ident is not a metavariable." >])
    | Node (_, "NT", [nt]) ->
	let (nont, etyp) = nterm univ nt in 
	env, NonTerm (nont, etyp, None)
    | _ -> invalid_arg_loc (Ast.loc ast, "Extend.prod_item")

let rec prod_item_list univ penv pil =
  match pil with
    | [] -> [], penv
    | pi :: pitl ->
	let (env, pic) = prod_item univ penv pi in
	let (pictl, act_env) = prod_item_list univ env pitl in
        (pic :: pictl, act_env)

let gram_rule univ etyp ast =
  match ast with
    | Node (_, "RULE", (Id (_, name) :: act :: pil)) ->
	let (pilc, act_env) = prod_item_list univ [] pil in
	let a = Ast.to_act_check_vars act_env etyp act in
        { gr_name=name; gr_production=pilc; gr_action=a }
    | _ -> invalid_arg_loc (Ast.loc ast, "Extend.gram_rule")

let gram_entry univ (nt, etyp, ass, rl) =
  { ge_name = nt;
    ge_type = etyp;
    gl_assoc = ass;
    gl_rules = List.map (gram_rule univ etyp) rl }

let gram_assoc = function
  | Id (_, "LEFTA") -> Some LeftA
  | Id (_, "RIGHTA") -> Some RightA
  | Id (_, "NONA") -> Some NonA
  | Id (_, "NONE") -> None
  | ast -> invalid_arg_loc (Ast.loc ast, "Egrammar.assoc")

let gram_define_entry univ = function
  | Node (_, "ENTRY", (Id (ntl, nt) :: et :: ass :: rl)) ->
      let etyp = entry_type et in
      let assoc = gram_assoc ass in
      let _ =
        try 
	  create_entry univ nt etyp
        with Failure s ->
          user_err_loc (ntl,"Extend.gram_define_entry",[< 'sTR s >])
      in 
      (nt, etyp, assoc, rl)
  | ast -> invalid_arg_loc (Ast.loc ast, "Egrammar.gram_define_entry")

let gram_of_ast univ astl =
  let u = get_univ univ in
  let entryl = List.map (gram_define_entry u) astl in
  { gc_univ = univ;
    gc_entries = List.map (gram_entry u) entryl }


(* Converting and checking pretty-printing command *)

type parenRelation = L | E | Any
type precedence = int * int * int

let compare_prec (a1,b1,c1) (a2,b2,c2) =
  match (a1=a2),(b1=b2),(c1=c2) with
    | true,true,true -> 0
    | true,true,false -> c1-c2
    | true,false,_ -> b1-b2
    | false,_,_ -> a1-a2

let tolerable_prec oparent_prec_reln (_,child_prec) =
  match oparent_prec_reln with
    | Some ((_,pprec), L) -> (compare_prec child_prec pprec) < 0
    | Some ((_,pprec), E) -> (compare_prec child_prec pprec) <= 0
    | _ -> true

type ppbox =
  | PpHB of int
  | PpHOVB of int
  | PpHVB of int
  | PpVB of int
  | PpTB

type unparsing_hunk = 
  | PH of Ast.pat * string option * parenRelation
  | RO of string
  | UNP_BOX of ppbox * unparsing_hunk list
  | UNP_BRK of int * int
  | UNP_TBRK of int * int
  | UNP_TAB
  | UNP_FNL

let ppcmd_of_box = function
  | PpHB n -> h n
  | PpHOVB n -> hOV n
  | PpHVB n -> hV n
  | PpVB n -> v n
  | PpTB   -> t

(* Parsing the unparsing specifications *)

let box_of_ast = function
  | Node (_, "PpHB", [Num (_, n)]) -> (PpHB n)
  | Node (_, "PpHOVB", [Num (_, n)]) -> (PpHOVB n)
  | Node (_, "PpHVB", [Num (_, n)]) -> (PpHVB n)
  | Node (_, "PpVB", [Num (_, n)]) -> (PpVB n)
  | Node (_, "PpTB", [])           -> PpTB
  | p -> invalid_arg_loc (Ast.loc p,"Syntaxext.box_of_ast")

let rec unparsing_hunk_of_ast vars = function
  | Node(_, "PH", [e; Str(_,pprim)]) ->
      PH (Ast.val_of_ast vars e, Some pprim, Any)
  | Node(loc, "PH", [e; Id(_,pr)]) ->
      let reln =
        (match pr with
           | "L" -> L
           | "E" -> E
           | "Any" -> Any 
           | _ -> invalid_arg_loc (loc,"Syntaxext.paren_reln_of_ast")) in
      PH (Ast.val_of_ast vars e, None, reln)
  | Node (_, "RO", [Str(_,s)]) -> RO s
  | Node (_, "UNP_FNL", []) -> UNP_FNL
  | Node (_, "UNP_TAB", []) -> UNP_TAB
  | Node (_, "UNP_BRK", [Num(_, n1); Num(_, n2)]) -> UNP_BRK(n1,n2)
  | Node (_, "UNP_TBRK", [Num(_, n1); Num(_, n2)]) -> UNP_TBRK(n1,n2)
  | Node (_, "UNP_BOX", (box::sub)) ->
      UNP_BOX(box_of_ast box,
              List.map (unparsing_hunk_of_ast vars) sub)
  | h -> invalid_arg_loc (Ast.loc h,"Syntaxext.unparsing_hunk_of_ast")

let unparsing_of_ast vars = function
  | Node(_,"UNPARSING",ll) ->
      List.map (unparsing_hunk_of_ast vars) ll
  | u -> invalid_arg_loc (Ast.loc u,"Syntaxext.unp_of_ast")

let prec_of_ast = function
  | Node(_,"PREC",[Num(_,a1); Num(_,a2); Num(_,a3)]) -> (a1,a2,a3)
  | ast -> invalid_arg_loc (Ast.loc ast,"Syntaxext.prec_of_ast")


type syntax_entry = {
  syn_id : string;
  syn_prec: precedence;
  syn_astpat : Ast.pat;
  syn_hunks : unparsing_hunk list }

let rule_of_ast whatfor prec = function
  | Node(_,"RULE",[Id(_,s); spat; unp]) ->
      let (astpat,meta_env) = Ast.to_pat [] spat in
      let hunks = unparsing_of_ast meta_env unp in
      { syn_id = s;
	syn_prec = prec;
        syn_astpat = astpat;
        syn_hunks = hunks }
  | ast -> invalid_arg_loc (Ast.loc ast,"Metasyntax.rule_of_ast")

let level_of_ast whatfor = function
  | Node(_,"SYNTAXENTRY",(pr::rl)) ->
      let prec = prec_of_ast pr in
      List.map (rule_of_ast whatfor prec) rl
  | ast -> invalid_arg_loc (Ast.loc ast,"Metasyntax.level_of_ast")
