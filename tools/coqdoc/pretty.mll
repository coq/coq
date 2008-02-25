(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*s Utility functions for the scanners *)

{

  open Cdglobals
  open Printf
  open Index
  open Lexing 
  open Output

  (* count the number of spaces at the beginning of a string *)
  let count_spaces s =
    let n = String.length s in
    let rec count c i = 
      if i == n then c,i else match s.[i] with
	| '\t' -> count (c + (8 - (c mod 8))) (i + 1)
	| ' ' -> count (c + 1) (i + 1)
	| _ -> c,i
    in
      count 0 0

  let count_dashes s =
    let c = ref 0 in
    for i = 0 to String.length s - 1 do if s.[i] = '-' then incr c done;
    !c

  let cut_head_tail_spaces s =
    let n = String.length s in
    let rec look_up i = if i == n || s.[i] <> ' ' then i else look_up (i+1) in
    let rec look_dn i = if i == -1 || s.[i] <> ' ' then i else look_dn (i-1) in
    let l = look_up 0 in
    let r = look_dn (n-1) in
    if l <= r then String.sub s l (r-l+1) else s

  let sec_title s =
    let rec count lev i = 
      if s.[i] = '*' then 
	count (succ lev) (succ i) 
      else 
	let t = String.sub s i (String.length s - i) in
	lev, cut_head_tail_spaces t
    in
    count 0 (String.index s '*')

  let strip_eol s =
    let eol = s.[String.length s - 1] = '\n' in
    (eol, if eol then String.sub s 1 (String.length s - 1) else s)


  let formatted = ref false
  let brackets = ref 0

  let backtrack lexbuf = lexbuf.lex_curr_pos <- lexbuf.lex_start_pos

  let is_space = function ' ' | '\t' | '\n' | '\r' -> true | _ -> false

  (* saving/restoring the PP state *)

  type state = {
    st_gallina : bool;
    st_light : bool
  }

  let state_stack = Stack.create ()

  let save_state () = 
    Stack.push { st_gallina = !gallina; st_light = !light } state_stack

  let restore_state () =
    let s = Stack.pop state_stack in
    gallina := s.st_gallina;
    light := s.st_light
      
  let without_ref r f x = save_state (); r := false; f x; restore_state ()

  let without_gallina = without_ref gallina

  let without_light = without_ref light

  let show_all f = without_gallina (without_light f)

  let begin_show () = save_state (); gallina := false; light := false
  let end_show () = restore_state ()

  (* Reset the globals *)

  let reset () =
    formatted := false;
    brackets := 0

  (* erasing of Section/End *)

  let section_re = Str.regexp "[ \t]*Section"
  let end_re = Str.regexp "[ \t]*End"
  let is_section s = Str.string_match section_re s 0
  let is_end s = Str.string_match end_re s 0

  let sections_to_close = ref 0

  let section_or_end s =
    if is_section s then begin
      incr sections_to_close; true
    end else if is_end s then begin
      if !sections_to_close > 0 then begin 
	decr sections_to_close; true 
      end else 
	false
    end else
      true

  (* tokens pretty-print *)

  let token_buffer = Buffer.create 1024

  let token_re = 
    Str.regexp "[ \t]*(\\*\\*[ \t]+printing[ \t]+\\([^ \t]+\\)"
  let printing_token_re =
    Str.regexp
      "[ \t]*\\(\\(%\\([^%]*\\)%\\)\\|\\(\\$[^$]*\\$\\)\\)?[ \t]*\\(#\\(\\([^#]\\|&#\\)*\\)#\\)?"

  let add_printing_token toks pps =
    try
      if Str.string_match token_re toks 0 then
	let tok = Str.matched_group 1 toks in
	if Str.string_match printing_token_re pps 0 then
	  let pp = 
	    (try Some (Str.matched_group 3 pps) with _ -> 
             try Some (Str.matched_group 4 pps) with _ -> None),
	    (try Some (Str.matched_group 6 pps) with _ -> None)
	  in
	  Output.add_printing_token tok pp
    with _ ->
      ()

  let remove_token_re = 
    Str.regexp 
      "[ \t]*(\\*\\*[ \t]+remove[ \t]+printing[ \t]+\\([^ \t]+\\)[ \t]*\\*)"

  let remove_printing_token toks =
    try
      if Str.string_match remove_token_re toks 0 then
	let tok = Str.matched_group 1 toks in
	Output.remove_printing_token tok
    with _ ->
      ()

  let extract_ident_re = Str.regexp "([ \t]*\\([^ \t]+\\)[ \t]*:="
  let extract_ident s =
    assert (String.length s >= 3);
    if Str.string_match extract_ident_re s 0 then
      Str.matched_group 1 s
    else
      String.sub s 1 (String.length s - 3)

}

(*s Regular expressions *)

let space = [' ' '\t']
let space_nl = [' ' '\t' '\n' '\r']
let nl = "\r\n" | '\n'

let firstchar = 
  ['A'-'Z' 'a'-'z' '_' 
  (* iso 8859-1 accents *) 
  '\192'-'\214' '\216'-'\246' '\248'-'\255' ] |
  (* utf-8 latin 1 supplement *) 
  '\195' ['\128'-'\191'] |
  (* utf-8 letterlike symbols *) 
  '\226' ('\132' ['\128'-'\191'] | '\133' ['\128'-'\143'])
let identchar = 
  firstchar | ['\'' '0'-'9' '@' ]
let id = firstchar identchar*
let pfx_id = (id '.')*
let identifier = 
  id | pfx_id id

let symbolchar_no_brackets =
  ['!' '$' '%' '&' '*' '+' ',' '@' '^' '#'
   '\\' '/' '-' '<' '>' '|' ':' '?' '=' '~'
   '{' '}' '(' ')'] |
  (* utf-8 symbols *) 
  '\226' ['\134'-'\143' '\152'-'\155' '\164'-'\165' '\168'-'\171'] _
let symbolchar = symbolchar_no_brackets | '[' | ']'
let token = symbolchar+ | '[' [^ '[' ']' ':']* ']'


let thm_token = 
  "Theorem" 
  | "Lemma" 
  | "Fact" 
  | "Remark" 
  | "Corollary" 
  | "Proposition" 
  | "Property"
  | "Goal"

let def_token = 
  "Definition" 
  | "Let" 
  | "Class"
  | "SubClass" 
  | "Example"
  | "Local" 
  | "Fixpoint" 
  | "CoFixpoint" 
  | "Record" 
  | "Structure" 
  | "Instance"
  | "Scheme"
  | "Inductive"
  | "CoInductive"

let decl_token = 
  "Hypothesis" 
  | "Hypotheses" 
  | "Parameter" 
  | "Axiom" 's'? 
  | "Conjecture"

let gallina_ext =
  "Module" 
  | "Include" space+ "Type"
  | "Include"
  | "Declare" space+ "Module"
  | "Transparent"
  | "Opaque"
  | "Canonical"
  | "Coercion"
  | "Identity"
  | "Implicit"
  | "Notation"
  | "Infix"
  | "Tactic" space+ "Notation"
  | "Reserved" space+ "Notation"
  | "Section"
  | "Variable" 's'?
  | ("Hypothesis" | "Hypotheses")
  | "End"

let commands = 
  "Pwd"
  | "Cd"
  | "Drop"
  | "ProtectedLoop"
  | "Quit"
  | "Load"
  | "Add"
  | "Remove" space+ "Loadpath"
  | "Print"
  | "Inspect"
  | "About"
  | "Search"
  | "Eval"
  | "Reset"
  | "Check"
  | "Type"

  | "Section"
  | "Chapter"
  | "Variable" 's'?
  | ("Hypothesis" | "Hypotheses")
  | "End"

let extraction = 
  "Extraction"
  | "Recursive" space+ "Extraction" 
  | "Extract"

let gallina_kw = thm_token | def_token | decl_token | gallina_ext | commands | extraction

let prog_kw =
  "Program" space+ gallina_kw
  | "Obligation"
  | "Obligations"
  | "Solve"

let gallina_kw_to_hide =
  "Implicit"
  | "Ltac"
  | "Require"
  | "Import"
  | "Export"
  | "Load" 
  | "Hint"
  | "Open"
  | "Close"
  | "Delimit"
  | "Transparent"
  | "Opaque"
  | ("Declare" space+ ("Morphism" | "Step") )
  | ("Set" | "Unset") space+ "Printing" space+ "Coercions"
  | "Declare" space+ ("Left" | "Right") space+ "Step" 


(* tokens with balanced brackets *)
let token_brackets =
  ( symbolchar_no_brackets+ ('[' symbolchar_no_brackets* ']')* 
  | symbolchar_no_brackets* ('[' symbolchar_no_brackets* ']')+ )
  symbolchar_no_brackets*

let section = "*" | "**" | "***" | "****"

let item_space = "    "

let begin_hide = "(*" space* "begin" space+ "hide" space* "*)" space* nl
let end_hide = "(*" space* "end" space+ "hide" space* "*)" space* nl
let begin_show = "(*" space* "begin" space+ "show" space* "*)" space* nl
let end_show = "(*" space* "end" space+ "show" space* "*)" space* nl
(*
let begin_verb = "(*" space* "begin" space+ "verb" space* "*)"
let end_verb = "(*" space* "end" space+ "verb" space* "*)"
*)



(*s Scanning Coq, at beginning of line *)

rule coq_bol = parse
  | space* nl+
      { empty_line_of_code (); coq_bol lexbuf }
  | space* "(**" space_nl
      { end_coq (); start_doc (); 
	let eol = doc_bol lexbuf in
	  end_doc (); start_coq (); 
	  if eol then coq_bol lexbuf else coq lexbuf }
  | space* "Comments" space_nl
      { end_coq (); start_doc (); comments lexbuf; end_doc (); 
	start_coq (); coq lexbuf }
  | space* begin_hide
      { skip_hide lexbuf; coq_bol lexbuf }
  | space* begin_show
      { begin_show (); coq_bol lexbuf }
  | space* end_show
      { end_show (); coq_bol lexbuf }
  | space* gallina_kw_to_hide
      { let s = lexeme lexbuf in
	  if !light && section_or_end s then 
	    let eol = skip_to_dot lexbuf in
	      if eol then (line_break (); coq_bol lexbuf) else coq lexbuf
	  else 
	    begin
	      let nbsp,isp = count_spaces s in
		indentation nbsp; 
		let s = String.sub s isp (String.length s - isp) in
		  ident s (lexeme_start lexbuf + isp); 
		  let eol = body lexbuf in 
		    if eol then coq_bol lexbuf else coq lexbuf
	    end }
  | space* gallina_kw
      { let s = lexeme lexbuf in 
	let nbsp,isp = count_spaces s in
	let s = String.sub s isp (String.length s - isp)  in
	  indentation nbsp;
	  ident s (lexeme_start lexbuf + isp); 
	  let eol= body lexbuf in
	    if eol then coq_bol lexbuf else coq lexbuf }
  | space* prog_kw
      { let s = lexeme lexbuf in 
	let nbsp,isp = count_spaces s in
	  indentation nbsp;
	  let s = String.sub s isp (String.length s - isp)  in
	    ident s (lexeme_start lexbuf + isp); 
	    let eol= body lexbuf in
	      if eol then coq_bol lexbuf else coq lexbuf }

  | space* "(**" space+ "printing" space+ (identifier | token) space+
      { let tok = lexeme lexbuf in
	let s = printing_token lexbuf in
	  add_printing_token tok s;
	  coq_bol lexbuf }
  | space* "(**" space+ "printing" space+
      { eprintf "warning: bad 'printing' command at character %d\n" 
	  (lexeme_start lexbuf); flush stderr;
	ignore (comment lexbuf);
	coq_bol lexbuf }
  | space* "(**" space+ "remove" space+ "printing" space+ 
      (identifier | token) space* "*)"
      { remove_printing_token (lexeme lexbuf);
	coq_bol lexbuf }
  | space* "(**" space+ "remove" space+ "printing" space+
      { eprintf "warning: bad 'remove printing' command at character %d\n" 
	  (lexeme_start lexbuf); flush stderr;
	ignore (comment lexbuf);
	coq_bol lexbuf }
  | space* "(*"
      { let eol = comment lexbuf in
	  if eol then coq_bol lexbuf else coq lexbuf }
  | eof 
      { () }
  | _
      { let eol = 
	  if not !gallina then 
	    begin backtrack lexbuf; indentation 0; body_bol lexbuf end 
	  else 
	    skip_to_dot lexbuf 
	in
	  if eol then coq_bol lexbuf else coq lexbuf }

(*s Scanning Coq elsewhere *)

and coq = parse
  | nl 
      { line_break(); coq_bol lexbuf }
  | "(**" space_nl
      { end_coq (); start_doc (); 
	let eol = doc_bol lexbuf in
	  end_doc (); start_coq (); 
	  if eol then coq_bol lexbuf else coq lexbuf }
  | "(*"
      { let eol = comment lexbuf in
	  if eol then begin line_break(); coq_bol lexbuf end 
          else coq lexbuf
      }
  | nl+ space* "]]"
      { if not !formatted then begin symbol (lexeme lexbuf); coq lexbuf end }
  | eof 
      { () }
  | gallina_kw_to_hide
      { let s = lexeme lexbuf in
	  if !light && section_or_end s then 
	    begin 
	      let eol = skip_to_dot lexbuf in
		if eol then coq_bol lexbuf else coq lexbuf 
	    end 
	  else 
	    begin
	      ident s (lexeme_start lexbuf); 
	      let eol=body lexbuf in 
		if eol then coq_bol lexbuf else coq lexbuf
	    end }
  | gallina_kw
      { let s = lexeme lexbuf in 
	  ident s (lexeme_start lexbuf); 
	let eol = body lexbuf in
	  if eol then coq_bol lexbuf else coq lexbuf }
  | prog_kw
      { let s = lexeme lexbuf in 
	  ident s (lexeme_start lexbuf); 
	let eol = body lexbuf in
	  if eol then coq_bol lexbuf else coq lexbuf }
  | space+ { char ' '; coq lexbuf }
  | eof 
      { () }
  | _ {	let eol = 
	  if not !gallina then 
	    begin backtrack lexbuf; indentation 0; body lexbuf end 
	  else 
	    let eol = skip_to_dot lexbuf in
	      if eol then line_break (); eol
	in 
	  if eol then coq_bol lexbuf else coq lexbuf}
      
(*s Scanning documentation, at beginning of line *)

and doc_bol = parse
  | space* nl+
      { paragraph (); doc_bol lexbuf }
  | space* section space+ ([^'\n' '*'] | '*'+ [^'\n' ')' '*'])* ('*'+ '\n')?
      { let eol, lex = strip_eol (lexeme lexbuf) in
        let lev, s = sec_title lex in
          section lev (fun () -> ignore (doc (from_string s)));
	  if eol then doc_bol lexbuf else doc lexbuf }
  | space* '-'+
      { let n = count_dashes (lexeme lexbuf) in
	if n >= 4 then rule () else item n;
        doc lexbuf }
  | "<<" space*
      { start_verbatim (); verbatim lexbuf; doc_bol lexbuf }
  | eof 
      { true }
  | _ 
      { backtrack lexbuf; doc lexbuf }

(*s Scanning documentation elsewhere *)

and doc = parse
  | nl
      { char '\n'; doc_bol lexbuf }
  | "["
      { brackets := 1; 
	start_inline_coq (); escaped_coq lexbuf; end_inline_coq ();
	doc lexbuf }
  | "[[" nl space*
      { formatted := true; line_break (); start_inline_coq ();
	indentation (fst (count_spaces (lexeme lexbuf))); 
	let eol = body_bol lexbuf in 
	  end_inline_coq (); formatted := false;
	  if eol then doc_bol lexbuf else doc lexbuf}
  | '*'* "*)" space* nl
      { true }
  | '*'* "*)"
      { false }
  | "$"
      { start_latex_math (); escaped_math_latex lexbuf; doc lexbuf }
  | "$$"
      { char '$'; doc lexbuf }
  | "%"
      { escaped_latex lexbuf; doc lexbuf }
  | "%%"
      { char '%'; doc lexbuf }
  | "#"
      { escaped_html lexbuf; doc lexbuf }
  | "##"
      { char '#'; doc lexbuf }
  | eof 
      { false }
  | _ 
      { char (lexeme_char lexbuf 0); doc lexbuf }

(*s Various escapings *)

and escaped_math_latex = parse
  | "$" { stop_latex_math () }
  | eof { stop_latex_math () }
  | _   { latex_char (lexeme_char lexbuf 0); escaped_math_latex lexbuf }

and escaped_latex = parse
  | "%" { () }
  | eof { () }
  | _   { latex_char (lexeme_char lexbuf 0); escaped_latex lexbuf }

and escaped_html = parse
  | "#" { () }
  | "&#"
        { html_char '&'; html_char '#'; escaped_html lexbuf }
  | "##"
        { html_char '#'; escaped_html lexbuf }
  | eof { () }
  | _   { html_char (lexeme_char lexbuf 0); escaped_html lexbuf }

and verbatim = parse
  | "nl>>" { verbatim_char '\n'; stop_verbatim () }
  | eof { stop_verbatim () }
  | _ { verbatim_char (lexeme_char lexbuf 0); verbatim lexbuf }

(*s Coq, inside quotations *)

and escaped_coq = parse
  | "]"
      { decr brackets; 
	if !brackets > 0 then begin char ']'; escaped_coq lexbuf end }
  | "["
      { incr brackets; char '['; escaped_coq lexbuf }
  | "(*"
      { ignore (comment lexbuf); escaped_coq lexbuf }
  | "*)"
      { (* likely to be a syntax error: we escape *) backtrack lexbuf }
  | eof
      { () }
  | token_brackets
      { let s = lexeme lexbuf in
	symbol s;
	escaped_coq lexbuf }
  | (identifier '.')* identifier
      { ident (lexeme lexbuf) (lexeme_start lexbuf); escaped_coq lexbuf }
  | _ 
      { char (lexeme_char lexbuf 0); escaped_coq lexbuf }

(*s Coq "Comments" command. *)

and comments = parse
  | space_nl+ 
      { char ' '; comments lexbuf }
  | '"' [^ '"']* '"' 
      { let s = lexeme lexbuf in
	let s = String.sub s 1 (String.length s - 2) in
	ignore (doc (from_string s)); comments lexbuf }
  | ([^ '.' '"'] | '.' [^ ' ' '\t' '\n'])+
      { escaped_coq (from_string (lexeme lexbuf)); comments lexbuf }
  | "." (space_nl | eof)
      { () }
  | eof 
      { () }
  | _   
      { char (lexeme_char lexbuf 0); comments lexbuf }

(*s Skip comments *)

and comment = parse
  | "(*" { comment lexbuf }
  | "*)" space* nl+ { true }
  | "*)" { false }
  | eof  { false }
  | _    { comment lexbuf }

and skip_to_dot = parse
  | '.' space* nl { true }
  | eof | '.' space+ { false}
  | "(*" { ignore (comment lexbuf); skip_to_dot lexbuf }
  | _ { skip_to_dot lexbuf }

and body_bol = parse
  | space+
      { indentation (fst (count_spaces (lexeme lexbuf))); body lexbuf }
  | _ { backtrack lexbuf; body lexbuf }

and body = parse
  | nl {line_break(); body_bol lexbuf}
  | nl+ space* "]]"
      { if not !formatted then begin symbol (lexeme lexbuf); body lexbuf end else true }
  | eof { false }
  | '.' space* nl | '.' space* eof { char '.'; line_break(); true }      
  | '.' space+ { char '.'; char ' '; false }
  | '"' { char '"'; notation lexbuf; body lexbuf }
  | "(*" { let eol = comment lexbuf in 
	     if eol 
	     then begin line_break(); body_bol lexbuf end
	     else body lexbuf }
  | identifier 
      { let s = lexeme lexbuf in 
	  ident s (lexeme_start lexbuf); 
	  body lexbuf }
  | token
      { let s = lexeme lexbuf in
	  symbol s; body lexbuf }
  | _ { let c = lexeme_char lexbuf 0 in 
	  char c; 
          body lexbuf }

and notation_bol = parse
  | space+
      { indentation (fst (count_spaces (lexeme lexbuf))); notation lexbuf }
  | _ { backtrack lexbuf; notation lexbuf }

and notation = parse
  | nl { line_break(); notation_bol lexbuf }
  | '"' { char '"'; false }
  | token
      { let s = lexeme lexbuf in
	  symbol s; notation lexbuf }
  | _ { let c = lexeme_char lexbuf 0 in 
	  char c; 
          notation lexbuf }

and skip_hide = parse
  | eof | end_hide { () }
  | _ { skip_hide lexbuf }

(*s Reading token pretty-print *)

and printing_token = parse
  | "*)" | eof 
	{ let s = Buffer.contents token_buffer in 
	  Buffer.clear token_buffer;
	  s }
  | _   { Buffer.add_string token_buffer (lexeme lexbuf); 
	  printing_token lexbuf }

(*s Applying the scanners to files *)

{

  let coq_file f m =
    reset ();
    Index.scan_file f m;
    start_module ();
    let c = open_in f in
    let lb = from_channel c in
    start_coq (); coq_bol lb; end_coq ();
    close_in c

}

