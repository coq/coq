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

  open Printf
  open Index
  open Lexing 
  open Output

  (* count the number of spaces at the beginning of a string *)
  let count_spaces s =
    let n = String.length s in
    let rec count c i = 
      if i == n then c else match s.[i] with
	| '\t' -> count (c + (8 - (c mod 8))) (i + 1)
	| ' ' -> count (c + 1) (i + 1)
	| _ -> c
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

  let formatted = ref false
  let brackets = ref 0

  let backtrack lexbuf = lexbuf.lex_curr_pos <- lexbuf.lex_start_pos

  (* Gallina (skipping proofs). This is a three states automaton. *)   

  let gallina = ref false

  type gallina_state = Nothing | AfterDot | Proof

  let gstate = ref AfterDot

  let is_proof = 
    let t = Hashtbl.create 13 in
    List.iter (fun s -> Hashtbl.add t s true)
      [ "Theorem"; "Lemma"; "Fact"; "Remark"; "Goal"; "Let";
	"Correctness"; "Definition"; "Morphism" ];
    fun s -> try Hashtbl.find t s with Not_found -> false

  let gallina_id id = 
    if !gstate = AfterDot then
      if is_proof id then gstate := Proof else 
	if id <> "Add" then gstate := Nothing

  let gallina_symbol s = 
    if !gstate = AfterDot || (!gstate = Proof && s = ":=") then 
      gstate := Nothing

  let is_space = function ' ' | '\t' | '\n' | '\r' -> true | _ -> false

  let gallina_char c = 
    if c = '.' then
      (let skip = !gstate = Proof in gstate := AfterDot; skip)
    else
      (if !gstate = AfterDot && not (is_space c) then gstate := Nothing;
       false)

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
    brackets := 0;
    gstate := AfterDot

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

let firstchar = 
  ['A'-'Z' 'a'-'z' '_' 
  (* iso 8859-1 accents *) 
  '\192'-'\214' '\216'-'\246' '\248'-'\255' ] |
  (* utf-8 latin 1 supplement *) 
  '\195' ['\128'-'\191'] |
  (* utf-8 letterlike symbols *) 
  '\226' ('\132' ['\128'-'\191'] | '\133' ['\128'-'\143'])
let identchar = 
  firstchar | ['\'' '0'-'9' '@']
let identifier = firstchar identchar*

let symbolchar_no_brackets =
  ['!' '$' '%' '&' '*' '+' ',' '@' '^' '#'
   '\\' '/' '-' '<' '>' '|' ':' '?' '=' '~'
   '{' '}' '(' ')'] |
  (* utf-8 symbols *) 
  '\226' ['\134'-'\143' '\152'-'\155' '\164'-'\165' '\168'-'\171'] _
let symbolchar = symbolchar_no_brackets | '[' | ']'
let token = symbolchar+ | '[' [^ '[' ']' ':']* ']'

(* tokens with balanced brackets *)
let token_brackets =
  ( symbolchar_no_brackets+ ('[' symbolchar_no_brackets* ']')* 
  | symbolchar_no_brackets* ('[' symbolchar_no_brackets* ']')+ )
  symbolchar_no_brackets*

let section = "*" | "**" | "***" | "****"

let item_space = "    "

let begin_hide = "(*" space* "begin" space+ "hide" space* "*)" space* '\n'
let end_hide = "(*" space* "end" space+ "hide" space* "*)" space* '\n'
let begin_show = "(*" space* "begin" space+ "show" space* "*)" space* '\n'
let end_show = "(*" space* "end" space+ "show" space* "*)" space* '\n'
(*
let begin_verb = "(*" space* "begin" space+ "verb" space* "*)"
let end_verb = "(*" space* "end" space+ "verb" space* "*)"
*)

let coq_command_to_hide =
  "Implicit" space |
  "Ltac" space | 
  "Require" space | 
  "Load" space |
  "Hint" space |
  "Transparent" space |
  "Opaque" space |
  ("Declare" space+ ("Morphism" | "Step") space) |
  "Section" space | 
  "Variable" 's'? space | 
  ("Hypothesis" | "Hypotheses") space | 
  "End" space |
  ("Set" | "Unset") space+ "Printing" space+ "Coercions" space |
  "Declare" space+ ("Left" | "Right") space+ "Step" space

(*s Scanning Coq, at beginning of line *)

rule coq_bol = parse
  | '\n'+
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
  | space* coq_command_to_hide
      { let s = lexeme lexbuf in
	if !light && section_or_end s then begin 
	  skip_to_dot lexbuf; 
	  coq_bol lexbuf 
	end else begin
	  indentation (count_spaces s); 
	  backtrack lexbuf; 
	  coq lexbuf 
	end }
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
  | space+
      { indentation (count_spaces (lexeme lexbuf)); coq lexbuf }
  | eof 
      { () }
  | _ 
      { backtrack lexbuf; indentation 0; coq lexbuf }

(*s Scanning Coq elsewhere *)

and coq = parse
  | "\n" 
      { line_break (); coq_bol lexbuf }
  | "(**" space_nl
      { end_coq (); start_doc (); 
	let eol = doc_bol lexbuf in
	end_doc (); start_coq (); 
	if eol then coq_bol lexbuf else coq lexbuf }
  | "(*"
      { let eol = comment lexbuf in
	if eol then coq_bol lexbuf else coq lexbuf }
  | '\n'+ space* "]]"
      { if not !formatted then begin symbol (lexeme lexbuf); coq lexbuf end }
  | eof 
      { () }
  | token
      { let s = lexeme lexbuf in
	if !gallina then gallina_symbol s;
	symbol s;
	coq lexbuf }
  | "with" space+ "Module" | "Module" space+ "Type" | "Declare" space+ "Module"
    (* hack to avoid making Type a keyword *)
      { let s = lexeme lexbuf in
	if !gallina then gallina_id s;
        ident s (lexeme_start lexbuf); coq lexbuf }
  | "(" space* identifier space* ":=" 
      { let id = extract_ident (lexeme lexbuf) in
	symbol "("; ident id (lexeme_start lexbuf); symbol ":="; coq lexbuf }
  | (identifier '.')* identifier
      { let id = lexeme lexbuf in
	if !gallina then gallina_id id;
	ident id (lexeme_start lexbuf); coq lexbuf }
  | _ 
      { let c = lexeme_char lexbuf 0 in 
	char c;
	if !gallina && gallina_char c then skip_proof lexbuf;
	coq lexbuf }

(*s Scanning documentation, at beginning of line *)

and doc_bol = parse
  | space* "\n" '\n'*
      { paragraph (); doc_bol lexbuf }
  | space* section [^')'] ([^'\n' '*'] | '*' [^'\n'')'])*
      { let lev, s = sec_title (lexeme lexbuf) in 
	section lev (fun () -> ignore (doc (from_string s))); 
	doc lexbuf }
  | space* '-'+
      { let n = count_dashes (lexeme lexbuf) in
	if n >= 4 then rule () else item n;
	doc lexbuf }
  | "<<" space*
      { start_verbatim (); verbatim lexbuf; doc_bol lexbuf }
  | eof 
      { false }
  | _ 
      { backtrack lexbuf; doc lexbuf }

(*s Scanning documentation elsewhere *)

and doc = parse
  | "\n"
      { char '\n'; doc_bol lexbuf }
  | "["
      { brackets := 1; 
	start_inline_coq (); escaped_coq lexbuf; end_inline_coq ();
	doc lexbuf }
  | "[[" '\n' space*
      { formatted := true; start_code ();
	indentation (count_spaces (lexeme lexbuf)); 
	without_gallina coq lexbuf; 
	end_code (); formatted := false;
	doc lexbuf }
  | '*'* "*)" space* '\n'
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
  | "\n>>" { verbatim_char '\n'; stop_verbatim () }
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
  | "(*" { ignore (comment lexbuf); comment lexbuf }
  | "*)" space* '\n'+ { true }
  | "*)" { false }
  | eof  { false }
  | _    { comment lexbuf }

(*s Skip proofs *)

and skip_proof = parse
  | "(*" { ignore (comment lexbuf); skip_proof lexbuf }
  | "Save" | "Qed" | "Defined"
  | "Abort" | "Proof" | "Admitted" { skip_to_dot lexbuf }
  | "Proof" space* '.' { skip_proof lexbuf }
  | identifier { skip_proof lexbuf } (* to avoid keywords within idents *)
  | eof { () }
  | _ { skip_proof lexbuf }

and skip_to_dot = parse
  | eof | '.' { if !gallina then gstate := AfterDot }
  | "(*" { ignore (comment lexbuf); skip_to_dot lexbuf }
  | _ { skip_to_dot lexbuf }

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

  type file =
    | Vernac_file of string * coq_module
    | Latex_file of string

  let coq_file f m =
    reset ();
    Index.scan_file f m;
    start_module ();
    let c = open_in f in
    let lb = from_channel c in
    start_coq (); coq_bol lb; end_coq ();
    close_in c

  (* LaTeX document *)

  let latex_document l = 
    let file = function
      | Vernac_file (f,m) -> set_module m; coq_file f m
      | Latex_file f -> dump_file f
    in
    header ();
    if !toc then make_toc ();
    List.iter file l;
    trailer ();
    close ()

  (* HTML document *)      

  let html_document l =
    let file = function
      | Vernac_file (f,m) -> 
	  set_module m;
	  let hf = m ^ ".html" in
	  set_out_file hf;
	  header ();
	  coq_file f m;
	  trailer ();
	  close ()
      | Latex_file _ -> ()
    in
    List.iter file l;
    make_index ();
    if !toc then make_toc ()

  (* TeXmacs document *)

  let texmacs_document l = 
    let file = function
      | Vernac_file (f,m) -> set_module m; coq_file f m
      | Latex_file f -> dump_file f
    in
    header ();
    List.iter file l;
    trailer ();
    close ()

  let index_module = function
    | Vernac_file (_,m) -> Index.add_module m
    | Latex_file _ -> ()

  let produce_document l =
    List.iter index_module l;
    (match !target_language with
       | LaTeX -> latex_document 
       | HTML -> html_document
       | TeXmacs -> texmacs_document) l

}

