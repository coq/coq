(* -*- compile-command: "make -C ../.. bin/coqdoc" -*- *)
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
  open Lexing

  (* A list function we need *)
  let rec take n ls = 
    if n = 0 then [] else
      match ls with
        | [] -> []
        | (l :: ls) -> l :: (take (n-1) ls)

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
  let comment_level = ref 0
  let in_proof = ref None

  let backtrack lexbuf = lexbuf.lex_curr_pos <- lexbuf.lex_start_pos
  let backtrack_past_newline lexbuf =
    let buf = lexeme lexbuf in
    let splits = Str.bounded_split_delim (Str.regexp "['\n']") buf 2 in
      match splits with
        | [] -> ()
        | (_ :: []) -> ()
        | (s1 :: rest :: _) ->
            let length_skip = 1 + String.length s1 in
              lexbuf.lex_curr_pos <- lexbuf.lex_start_pos + length_skip

  let is_space = function ' ' | '\t' | '\n' | '\r' -> true | _ -> false

  (* saving/restoring the PP state *)

  type state = {
    st_gallina : bool;
    st_light : bool
  }

  let state_stack = Stack.create ()

  let save_state () = 
    Stack.push { st_gallina = !Cdglobals.gallina; st_light = !Cdglobals.light } state_stack

  let restore_state () =
    let s = Stack.pop state_stack in
    Cdglobals.gallina := s.st_gallina;
    Cdglobals.light := s.st_light
      
  let without_ref r f x = save_state (); r := false; f x; restore_state ()

  let without_gallina = without_ref Cdglobals.gallina

  let without_light = without_ref Cdglobals.light

  let show_all f = without_gallina (without_light f)

  let begin_show () = save_state (); Cdglobals.gallina := false; Cdglobals.light := false
  let end_show () = restore_state ()

  (* Reset the globals *)

  let reset () =
    formatted := false;
    brackets := 0;
    comment_level := 0

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

  (* for item lists *)
  type list_compare = 
      | Before 
      | StartLevel of int
      | InLevel of int * bool

  (* Before : we're before any levels
     StartLevel : at the same column as the dash in a level
     InLevel : after the dash of this level, but before any deeper dashes.
               bool is true if this is the last level *)
  let find_level levels cur_indent =
    match levels with
    | [] -> Before
    | (l::ls) -> 
        if cur_indent < l then Before
        else 
          (* cur_indent will never be less than the head of the list *)
          let rec findind ls n = 
            match ls with
            | [] -> InLevel (n,true)
            | (l :: []) -> if cur_indent = l then StartLevel n
                           else InLevel (n,true)
            | (l1 :: l2 :: ls) -> 
                if cur_indent = l1 then StartLevel n
                else if cur_indent < l2 then InLevel (n,false)
                     else findind (l2 :: ls) (n+1)
          in
            findind (l::ls) 1

  type is_start_list =
    | Rule
    | List of int
    | Neither

  let check_start_list str =
    let n_dashes = count_dashes str in
    let (n_spaces,_) = count_spaces str in
      if n_dashes >= 4 then 
        Rule
      else 
        if n_dashes = 1 then
          List n_spaces
        else
          Neither

   (* examine a string for subtitleness *)
  let subtitle m s = 
    match Str.split_delim (Str.regexp ":") s with
    | [] -> false
    | (name::_) ->
        if (cut_head_tail_spaces name) = m then
          true
        else
          false


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

  let symbol lexbuf s = Output.symbol s 

}

(*s Regular expressions *)

let space = [' ' '\t']
let space_nl = [' ' '\t' '\n' '\r']
let nl = "\r\n" | '\n'

let firstchar = 
  ['A'-'Z' 'a'-'z' '_' 
  (* iso 8859-1 accents *) 
  '\192'-'\214' '\216'-'\246' '\248'-'\255' ] |
  (* *)
  '\194' '\185' |
  (* utf-8 latin 1 supplement *) 
  '\195' ['\128'-'\191'] |
  (* utf-8 letterlike symbols *) 
  '\206' ('\160' | [ '\177'-'\183'] | '\187') |
  '\226' ('\130' [ '\128'-'\137' ] (* subscripts *)
    | '\129' [ '\176'-'\187' ] (* superscripts *)
    | '\132' ['\128'-'\191'] | '\133' ['\128'-'\143'])
let identchar = 
  firstchar | ['\'' '0'-'9' '@' ]
let id = firstchar identchar*
let pfx_id = (id '.')*
let identifier = 
  id | pfx_id id

(* This misses unicode stuff, and it adds "[" and "]".  It's only an
   approximation of idents - used for detecting whether an underscore
   is part of an identifier or meant to indicate emphasis *)
let nonidentchar = 
  [^ 'A'-'Z' 'a'-'z' '_' '[' ']'
      (* iso 8859-1 accents *) 
    '\192'-'\214' '\216'-'\246' '\248'-'\255'
    '\'' '0'-'9' '@' ]

let symbolchar_symbol_no_brackets =
  ['!' '$' '%' '&' '*' '+' ',' '^' '#'
      '\\' '/' '-' '<' '>' '|' ':' '?' '=' '~' ] |
  (* utf-8 symbols *) 
  '\226' ['\134'-'\143' '\152'-'\155' '\164'-'\165' '\168'-'\171'] _
let symbolchar_no_brackets = symbolchar_symbol_no_brackets | 
    [ '@' '{' '}' '(' ')' 'A'-'Z' 'a'-'z' '_']
let symbolchar = symbolchar_no_brackets | '[' | ']'
let token_no_brackets = symbolchar_symbol_no_brackets symbolchar_no_brackets*
let token = symbolchar_symbol_no_brackets symbolchar* | '[' [^ '[' ']' ':']* ']'
let printing_token = (token | id)+

(* tokens with balanced brackets *)
let token_brackets =
  ( token_no_brackets ('[' token_no_brackets? ']')* 
  | token_no_brackets? ('[' token_no_brackets? ']')+ )
  token_no_brackets?

let thm_token = 
  "Theorem" 
  | "Lemma" 
  | "Fact" 
  | "Remark" 
  | "Corollary" 
  | "Proposition" 
  | "Property"
  | "Goal"

let prf_token =
  "Next" space+ "Obligation"
  | "Proof" (space* "." | space+ "with")

let def_token = 
  "Definition" 
  | "Let" 
  | "Class"
  | "SubClass"
  | "Example"
  | "Local" 
  | "Fixpoint" 
  | "Boxed" 
  | "CoFixpoint" 
  | "Record" 
  | "Structure" 
  | "Scheme"
  | "Inductive"
  | "CoInductive"
  | "Equations"
  | "Instance"
  | "Global" space+ "Instance"

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
  | "Context"
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

let end_kw = "Qed" | "Defined" | "Save" | "Admitted" | "Abort"

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
    "Implicit" space+ "Arguments"
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
      { if not (!in_proof <> None && (!Cdglobals.gallina || !Cdglobals.light)) then Output.empty_line_of_code (); coq_bol lexbuf }
  | space* "(**" space_nl
      { Output.end_coq (); Output.start_doc (); 
	let eol = doc_bol lexbuf in
	  Output.end_doc (); Output.start_coq (); 
	  if eol then coq_bol lexbuf else coq lexbuf }
  | space* "Comments" space_nl
      { Output.end_coq (); Output.start_doc (); comments lexbuf; Output.end_doc (); 
	Output.start_coq (); coq lexbuf }
  | space* begin_hide
      { skip_hide lexbuf; coq_bol lexbuf }
  | space* begin_show
      { begin_show (); coq_bol lexbuf }
  | space* end_show
      { end_show (); coq_bol lexbuf }
  | space* gallina_kw_to_hide
      { let s = lexeme lexbuf in
	  if !Cdglobals.light && section_or_end s then 
	    let eol = skip_to_dot lexbuf in
	      if eol then (coq_bol lexbuf) else coq lexbuf
	  else 
	    begin
	      let nbsp,isp = count_spaces s in
		Output.indentation nbsp; 
		let s = String.sub s isp (String.length s - isp) in
		  Output.ident s (lexeme_start lexbuf + isp); 
		  let eol = body lexbuf in 
		    if eol then coq_bol lexbuf else coq lexbuf
	    end }
  | space* thm_token
      { let s = lexeme lexbuf in 
	let nbsp,isp = count_spaces s in
	let s = String.sub s isp (String.length s - isp)  in
	  Output.indentation nbsp;
	  Output.ident s (lexeme_start lexbuf + isp); 
	  let eol = body lexbuf in
	    in_proof := Some eol;
	    if eol then coq_bol lexbuf else coq lexbuf }
  | space* prf_token
      { in_proof := Some true;
	let eol = 
	  if not !Cdglobals.gallina then 
	    begin backtrack lexbuf; body_bol lexbuf end 
	  else 
	    let s = lexeme lexbuf in
	      if s.[String.length s - 1] = '.' then false
	      else skip_to_dot lexbuf
	in if eol then coq_bol lexbuf else coq lexbuf }
  | space* end_kw { 
      let eol = 
	if not (!in_proof <> None && !Cdglobals.gallina) then 
	  begin backtrack lexbuf; body_bol lexbuf end 
	else skip_to_dot lexbuf
      in
	in_proof := None;
	if eol then coq_bol lexbuf else coq lexbuf }
  | space* gallina_kw
      { 
	in_proof := None;
	let s = lexeme lexbuf in 
	let nbsp,isp = count_spaces s in
	let s = String.sub s isp (String.length s - isp)  in
	  Output.indentation nbsp;
	  Output.ident s (lexeme_start lexbuf + isp); 
	  let eol= body lexbuf in
	    if eol then coq_bol lexbuf else coq lexbuf }
  | space* prog_kw
      { 
	in_proof := None;
	let s = lexeme lexbuf in 
	let nbsp,isp = count_spaces s in
	  Output.indentation nbsp;
	  let s = String.sub s isp (String.length s - isp)  in
	    Output.ident s (lexeme_start lexbuf + isp); 
	    let eol= body lexbuf in
	      if eol then coq_bol lexbuf else coq lexbuf }

  | space* "(**" space+ "printing" space+ printing_token space+
      { let tok = lexeme lexbuf in
	let s = printing_token_body lexbuf in
	  add_printing_token tok s;
	  coq_bol lexbuf }
  | space* "(**" space+ "printing" space+
      { eprintf "warning: bad 'printing' command at character %d\n" 
	  (lexeme_start lexbuf); flush stderr;
	comment_level := 1;
	ignore (comment lexbuf);
	coq_bol lexbuf }
  | space* "(**" space+ "remove" space+ "printing" space+ 
      (identifier | token) space* "*)"
      { remove_printing_token (lexeme lexbuf);
	coq_bol lexbuf }
  | space* "(**" space+ "remove" space+ "printing" space+
      { eprintf "warning: bad 'remove printing' command at character %d\n" 
	  (lexeme_start lexbuf); flush stderr;
	comment_level := 1;
	ignore (comment lexbuf);
	coq_bol lexbuf }
  | space* "(*"
      { comment_level := 1; 
	if !Cdglobals.parse_comments then begin
	  let s = lexeme lexbuf in 
	  let nbsp,isp = count_spaces s in
	    Output.indentation nbsp;
	    Output.start_comment ();
	end;
	let eol = comment lexbuf in
	  if eol then coq_bol lexbuf else coq lexbuf }
  | eof 
      { () }
  | _
      { let eol = 
	  if not !Cdglobals.gallina then 
	    begin backtrack lexbuf; body_bol lexbuf end 
	  else 
	    skip_to_dot lexbuf 
	in
	  if eol then coq_bol lexbuf else coq lexbuf }

(*s Scanning Coq elsewhere *)

and coq = parse
  | nl 
      { if not (!in_proof <> None && !Cdglobals.gallina) then Output.line_break(); coq_bol lexbuf }
  | "(**" space_nl
      { Output.end_coq (); Output.start_doc (); 
	let eol = doc_bol lexbuf in
	  Output.end_doc (); Output.start_coq (); 
	  if eol then coq_bol lexbuf else coq lexbuf }
  | "(*"
      { comment_level := 1;
	if !Cdglobals.parse_comments then begin
	  let s = lexeme lexbuf in 
	  let nbsp,isp = count_spaces s in
	    Output.indentation nbsp;
	    Output.start_comment ();
	end;
	let eol = comment lexbuf in
	  if eol then coq_bol lexbuf
          else coq lexbuf
      }
  | nl+ space* "]]"
      { if not !formatted then begin symbol lexbuf (lexeme lexbuf); coq lexbuf end }
  | eof 
      { () }
  | gallina_kw_to_hide
      { let s = lexeme lexbuf in
	  if !Cdglobals.light && section_or_end s then 
	    begin 
	      let eol = skip_to_dot lexbuf in
		if eol then coq_bol lexbuf else coq lexbuf 
	    end 
	  else 
	    begin
	      Output.ident s (lexeme_start lexbuf); 
	      let eol=body lexbuf in 
		if eol then coq_bol lexbuf else coq lexbuf
	    end }
  | prf_token
      { let eol = 
	  if not !Cdglobals.gallina then 
	    begin backtrack lexbuf; body_bol lexbuf end 
	  else 
	    let s = lexeme lexbuf in
	    let eol = 
	      if s.[String.length s - 1] = '.' then false
	      else skip_to_dot lexbuf
	    in
	      eol
	in if eol then coq_bol lexbuf else coq lexbuf }
  | end_kw { 
      let eol = 
	if not !Cdglobals.gallina then 
	  begin backtrack lexbuf; body lexbuf end 
	else 
	  let eol = skip_to_dot lexbuf in
	    if !in_proof <> Some true && eol then 
	      Output.line_break ();
	    eol
      in
	in_proof := None;
	if eol then coq_bol lexbuf else coq lexbuf }
  | gallina_kw
      { let s = lexeme lexbuf in 
	  Output.ident s (lexeme_start lexbuf); 
	let eol = body lexbuf in
	  if eol then coq_bol lexbuf else coq lexbuf }
  | prog_kw
      { let s = lexeme lexbuf in 
	  Output.ident s (lexeme_start lexbuf); 
	let eol = body lexbuf in
	  if eol then coq_bol lexbuf else coq lexbuf }
  | space+ { Output.char ' '; coq lexbuf }
  | eof 
      { () }
  | _ {	let eol = 
	  if not !Cdglobals.gallina then 
	    begin backtrack lexbuf; body lexbuf end 
	  else 
	    skip_to_dot lexbuf
	in 
	  if eol then coq_bol lexbuf else coq lexbuf}
      
(*s Scanning documentation, at beginning of line *)

and doc_bol = parse
  | space* nl+
      { Output.paragraph (); doc_bol lexbuf }
  | space* section space+ ([^'\n' '*'] | '*'+ [^'\n' ')' '*'])* ('*'+ '\n')?
      { let eol, lex = strip_eol (lexeme lexbuf) in
        let lev, s = sec_title lex in
          if subtitle (Output.get_module false) s then
            ()
          else
            Output.section lev (fun () -> ignore (doc None (from_string s)));
	    if eol then doc_bol lexbuf else doc None lexbuf }
  | space* nl space* '-'+
      { (* adding this production instead of just letting the paragraph
           production and the begin list production fire eliminates
           extra vertical whitespace. *)
        let buf' = lexeme lexbuf in
        let buf = 
          let bufs = Str.split_delim (Str.regexp "['\n']") buf' in
            match bufs with
              | (_ :: s :: []) -> s
              | (_ :: _ :: s :: _) -> s
              | _ -> eprintf "Internal error bad_split1 - please report\n";
                     exit 1
        in
          match check_start_list buf with
          | Neither -> backtrack_past_newline lexbuf; doc None lexbuf
          | List n -> Output.item 1; doc (Some [n]) lexbuf
          | Rule -> Output.rule (); doc None lexbuf
      }
  | space* '-'+
      { let buf = lexeme lexbuf in
          match check_start_list buf with
          | Neither -> backtrack lexbuf; doc None lexbuf
          | List n -> Output.item 1; doc (Some [n]) lexbuf
          | Rule -> Output.rule (); doc None lexbuf
      }
  | "<<" space*
      { Output.start_verbatim (); verbatim lexbuf; doc_bol lexbuf }
  | eof 
      { true }
  | '_'
      { Output.start_emph (); 
        doc None lexbuf }
  | _ 
      { backtrack lexbuf; doc None lexbuf }

(*s Scanning lists - using whitespace *)
and doc_list_bol indents = parse
  | space* '-'
      { let (n_spaces,_) = count_spaces (lexeme lexbuf) in
        match find_level indents n_spaces with
        | Before -> backtrack lexbuf; doc_bol lexbuf
        | StartLevel n -> Output.item n; doc (Some (take n indents)) lexbuf
        | InLevel (n,true) -> 
            let items = List.length indents in
              Output.item (items+1);
              doc (Some (List.append indents [n_spaces])) lexbuf
        | InLevel (_,false) ->
            backtrack lexbuf; doc_bol lexbuf
      }
  | "<<" space*
      { Output.start_verbatim (); 
        verbatim lexbuf; 
        doc_list_bol indents lexbuf }
  | "[[" nl
      { formatted := true;
        Output.paragraph ();
        Output.start_inline_coq (); 
        ignore(body_bol lexbuf);
        Output.end_inline_coq ();
        formatted := false;
        doc_list_bol indents lexbuf }
  | space* nl space* '-'
      { (* Like in the doc_bol production, these two productions
           exist only to deal properly with whitespace *)
        Output.paragraph ();
        backtrack_past_newline lexbuf;
        doc_list_bol indents lexbuf }
  | space* nl space* _
      { let buf' = lexeme lexbuf in
        let buf = 
          let bufs = Str.split_delim (Str.regexp "['\n']") buf' in
            match bufs with
              | (_ :: s :: []) -> s
              | (_ :: _ :: s :: _) -> s
              | _ -> eprintf "Internal error bad_split2 - please report\n";
                     exit 1
        in
        let (n_spaces,_) = count_spaces buf in
        match find_level indents n_spaces with 
        | InLevel _ ->
            Output.paragraph ();
            backtrack_past_newline lexbuf;
            doc_list_bol indents lexbuf
        | StartLevel n ->
            if n = 1 then
              begin
                Output.stop_item ();
                backtrack_past_newline lexbuf;
                doc_bol lexbuf
              end
            else
              begin
                Output.paragraph ();
                backtrack_past_newline lexbuf;
                doc_list_bol indents lexbuf
              end
        | Before -> Output.stop_item (); 
                    backtrack_past_newline lexbuf; 
                    doc_bol lexbuf

      }
  | space* _ 
      { let (n_spaces,_) = count_spaces (lexeme lexbuf) in
        match find_level indents n_spaces with 
        | Before -> Output.stop_item (); backtrack lexbuf; 
                    doc_bol lexbuf
        | StartLevel n ->
            Output.reach_item_level (n-1);
            backtrack lexbuf;
            doc (Some (take (n-1) indents)) lexbuf
        | InLevel (n,_) ->
            Output.reach_item_level n;
            backtrack lexbuf;
            doc (Some (take n indents)) lexbuf
      }

(*s Scanning documentation elsewhere *)
and doc indents = parse
  | nl
      { Output.char '\n'; 
        match indents with 
        | Some ls -> doc_list_bol ls lexbuf 
        | None -> doc_bol lexbuf }
  | "[[" nl
      { if !Cdglobals.plain_comments
        then (Output.char '['; Output.char '['; doc indents lexbuf)
        else (formatted := true; 
              Output.line_break (); Output.start_inline_coq ();
	      let eol = body_bol lexbuf in 
	        Output.end_inline_coq (); formatted := false;
	        if eol then
		  match indents with 
		  | Some ls -> doc_list_bol ls lexbuf 
		  | None -> doc_bol lexbuf
		else doc indents lexbuf)}
  | "[]"
      { Output.proofbox (); doc indents lexbuf }
  | "["
      { if !Cdglobals.plain_comments then Output.char '['
        else (brackets := 1;  Output.start_inline_coq (); escaped_coq lexbuf;
              Output.end_inline_coq ()); doc indents lexbuf }
  | "(*"
      { backtrack lexbuf ;
        let bol_parse = match indents with
                        | Some is -> doc_list_bol is
                        | None   -> doc_bol
        in
        let eol = comment lexbuf in
          if eol then bol_parse lexbuf else doc indents lexbuf
      }
  | '*'* "*)" space* nl
      { true }
  | '*'* "*)"
      { false }
  | "$"
      { if !Cdglobals.plain_comments then Output.char '$'
        else (Output.start_latex_math (); escaped_math_latex lexbuf);
        doc indents lexbuf }
  | "$$"
      { if !Cdglobals.plain_comments then Output.char '$'; 
        Output.char '$'; doc indents lexbuf }
  | "%"
      { if !Cdglobals.plain_comments then Output.char '%'
        else escaped_latex lexbuf; doc indents lexbuf }
  | "%%"
      { if !Cdglobals.plain_comments then Output.char '%';
        Output.char '%'; doc indents lexbuf }
  | "#"
      { if !Cdglobals.plain_comments then Output.char '#'
        else escaped_html lexbuf; doc indents lexbuf }
  | "##"
      { if !Cdglobals.plain_comments then Output.char '#';
        Output.char '#'; doc indents lexbuf }
  | nonidentchar '_' nonidentchar
      { List.iter (fun x -> Output.char (lexeme_char lexbuf x)) [0;1;2];
        doc indents lexbuf}
  | nonidentchar '_'
      { Output.char (lexeme_char lexbuf 0); 
        Output.start_emph (); 
        doc indents lexbuf }
  | '_' nonidentchar
      { Output.stop_emph (); 
        Output.char (lexeme_char lexbuf 1);
        doc indents lexbuf }
  | eof 
      { false }
  | _ 
      { Output.char (lexeme_char lexbuf 0); doc indents lexbuf }

(*s Various escapings *)

and escaped_math_latex = parse
  | "$" { Output.stop_latex_math () }
  | eof { Output.stop_latex_math () }
  | _   { Output.latex_char (lexeme_char lexbuf 0); escaped_math_latex lexbuf }

and escaped_latex = parse
  | "%" { () }
  | eof { () }
  | _   { Output.latex_char (lexeme_char lexbuf 0); escaped_latex lexbuf }

and escaped_html = parse
  | "#" { () }
  | "&#"
        { Output.html_char '&'; Output.html_char '#'; escaped_html lexbuf }
  | "##"
        { Output.html_char '#'; escaped_html lexbuf }
  | eof { () }
  | _   { Output.html_char (lexeme_char lexbuf 0); escaped_html lexbuf }

and verbatim = parse
  | nl ">>" space* nl { Output.verbatim_char '\n'; Output.stop_verbatim () }
  | nl ">>" { Output.verbatim_char '\n'; Output.stop_verbatim () }
  | eof { Output.stop_verbatim () }
  | _ { Output.verbatim_char (lexeme_char lexbuf 0); verbatim lexbuf }

(*s Coq, inside quotations *)

and escaped_coq = parse
  | "]"
      { decr brackets; 
	if !brackets > 0 then begin Output.char ']'; escaped_coq lexbuf end }
  | "["
      { incr brackets; Output.char '['; escaped_coq lexbuf }
  | "(*"
      { comment_level := 1; ignore (comment lexbuf); escaped_coq lexbuf }
  | "*)"
      { (* likely to be a syntax error: we escape *) backtrack lexbuf }
  | eof
      { () }
  | token_brackets
      { let s = lexeme lexbuf in
	  symbol lexbuf s; escaped_coq lexbuf }
  | (identifier '.')* identifier
      { Output.ident (lexeme lexbuf) (lexeme_start lexbuf); escaped_coq lexbuf }
  | _ 
      { Output.char (lexeme_char lexbuf 0); escaped_coq lexbuf }

(*s Coq "Comments" command. *)

and comments = parse
  | space_nl+ 
      { Output.char ' '; comments lexbuf }
  | '"' [^ '"']* '"' 
      { let s = lexeme lexbuf in
	let s = String.sub s 1 (String.length s - 2) in
	ignore (doc None (from_string s)); comments lexbuf }
  | ([^ '.' '"'] | '.' [^ ' ' '\t' '\n'])+
      { escaped_coq (from_string (lexeme lexbuf)); comments lexbuf }
  | "." (space_nl | eof)
      { () }
  | eof 
      { () }
  | _   
      { Output.char (lexeme_char lexbuf 0); comments lexbuf }

(*s Skip comments *)

and comment = parse
  | "(*" { incr comment_level;
	   if !Cdglobals.parse_comments then Output.start_comment ();
	   comment lexbuf }
  | "*)" space* nl {
      if !Cdglobals.parse_comments then	
	(Output.end_comment (); Output.line_break ());
      decr comment_level; if !comment_level > 0 then comment lexbuf else true }
  | "*)" { 
      if !Cdglobals.parse_comments then (Output.end_comment ());
      decr comment_level; if !comment_level > 0 then comment lexbuf else false }
  | "[" {
      if !Cdglobals.parse_comments then
	if !Cdglobals.plain_comments then Output.char '['
        else (brackets := 1; Output.start_inline_coq ();
              escaped_coq lexbuf; Output.end_inline_coq ());
      comment lexbuf }
  | "[[" {
      if !Cdglobals.parse_comments then
        if !Cdglobals.plain_comments then (Output.char '['; Output.char '[')
        else (formatted := true;
              Output.line_break (); Output.start_inline_coq ();
              let _ = body_bol lexbuf in
                Output.end_inline_coq (); formatted := false);
      comment lexbuf}
  | "$"
      { if !Cdglobals.parse_comments then
          if !Cdglobals.plain_comments then Output.char '$'
          else (Output.start_latex_math (); escaped_math_latex lexbuf);
        comment lexbuf }
  | "$$"
      { if !Cdglobals.parse_comments 
        then 
          (if !Cdglobals.plain_comments then Output.char '$'; Output.char '$');
        doc None lexbuf }
  | "%"
      { if !Cdglobals.parse_comments
          then 
            if !Cdglobals.plain_comments then Output.char '%'
            else escaped_latex lexbuf; comment lexbuf }
  | "%%"
      { if !Cdglobals.parse_comments 
        then 
          (if !Cdglobals.plain_comments then Output.char '%'; Output.char '%');
        comment lexbuf }
  | "#"
      { if !Cdglobals.parse_comments
        then
          if !Cdglobals.plain_comments then Output.char '$'
          else escaped_html lexbuf; comment lexbuf }
  | "##"
      { if !Cdglobals.parse_comments 
        then 
          (if !Cdglobals.plain_comments then Output.char '#'; Output.char '#');
        comment lexbuf }
  | eof  { false }
  | space+ { if !Cdglobals.parse_comments
             then Output.indentation (fst (count_spaces (lexeme lexbuf)));
             comment lexbuf }
  | nl   { if !Cdglobals.parse_comments
           then Output.line_break (); comment lexbuf }
  | _    { if !Cdglobals.parse_comments then Output.char (lexeme_char lexbuf 0);
           comment lexbuf }
      
and skip_to_dot = parse
  | '.' space* nl { true }
  | eof | '.' space+ { false }
  | "(*" { comment_level := 1; ignore (comment lexbuf); skip_to_dot lexbuf }
  | _ { skip_to_dot lexbuf }

and body_bol = parse
  | space+
      { Output.indentation (fst (count_spaces (lexeme lexbuf))); body lexbuf }
  | _ { backtrack lexbuf; Output.indentation 0; body lexbuf }

and body = parse
  | nl {Output.line_break(); body_bol lexbuf}
  | nl+ space* "]]" space* nl
      { if not !formatted then 
          begin 
            symbol lexbuf (lexeme lexbuf); 
            body lexbuf 
          end 
        else 
          begin
            Output.paragraph ();
            true
          end }
  | "]]" space* nl
      { if not !formatted then 
          begin 
            symbol lexbuf (lexeme lexbuf); 
            body lexbuf 
          end 
        else 
          begin
            Output.paragraph ();
            true
          end }
  | eof { false }
  | '.' space* nl | '.' space* eof 
	{ Output.char '.'; Output.line_break(); 
	  if not !formatted then true else body_bol lexbuf }      
  | '.' space* nl "]]" space* nl
	{ Output.char '.';
        if not !formatted then
          begin
            eprintf "Error: stray ]] at %d\n"  (lexeme_start lexbuf); 
            flush stderr;
            exit 1
          end
	  else 
          begin
            Output.paragraph ();
            true
          end
      }
  | '.' space+ { Output.char '.'; Output.char ' '; 
	  if not !formatted then false else body lexbuf }
  | '"' { Output.char '"'; ignore(notation lexbuf); body lexbuf }
  | "(**" space_nl
      { Output.end_coq (); Output.start_doc (); 
	let eol = doc_bol lexbuf in
	  Output.end_doc (); Output.start_coq (); 
	  if eol then body_bol lexbuf else body lexbuf }
  | "(*" { comment_level := 1; 
	   if !Cdglobals.parse_comments then Output.start_comment ();
	   let eol = comment lexbuf in 
	     if eol 
	     then begin if not !Cdglobals.parse_comments then Output.line_break(); body_bol lexbuf end
	     else body lexbuf }
  | identifier 
      { let s = lexeme lexbuf in 
	  Output.ident s (lexeme_start lexbuf); 
	  body lexbuf }
  | token_no_brackets
      { let s = lexeme lexbuf in
	  symbol lexbuf s; body lexbuf }
  | _ { let c = lexeme_char lexbuf 0 in 
	  Output.char c; 
          body lexbuf }

and notation_bol = parse
  | space+
      { Output.indentation (fst (count_spaces (lexeme lexbuf))); notation lexbuf }
  | _ { backtrack lexbuf; notation lexbuf }

and notation = parse
  | nl { Output.line_break(); notation_bol lexbuf }
  | '"' { Output.char '"'}
  | token
      { let s = lexeme lexbuf in
	  symbol lexbuf s; notation lexbuf }
  | _ { let c = lexeme_char lexbuf 0 in 
	  Output.char c; 
          notation lexbuf }

and skip_hide = parse
  | eof | end_hide { () }
  | _ { skip_hide lexbuf }

(*s Reading token pretty-print *)

and printing_token_body = parse
  | "*)" nl? | eof 
	{ let s = Buffer.contents token_buffer in 
	  Buffer.clear token_buffer;
	  s }
  | _   { Buffer.add_string token_buffer (lexeme lexbuf); 
	  printing_token_body lexbuf }

(*s A small scanner to support the chapter subtitle feature *)
and st_start m = parse
  | "(*" "*"+ space+ "*" space+
      { st_modname m lexbuf }
  | _ 
      { None }

and st_modname m = parse
  | identifier space* ":" space*
      { if subtitle m (lexeme lexbuf) then
          st_subtitle lexbuf
        else
          None
      }
  | _ 
      { None }

and st_subtitle = parse
  | [^ '\n']* '\n'
      { let st = lexeme lexbuf in
        let i = try Str.search_forward (Str.regexp "\\**)") st 0 with 
                   Not_found -> 
                     (eprintf "unterminated comment at beginning of file\n";
                      exit 1)
        in
          Some (cut_head_tail_spaces (String.sub st 0 i))
      }
  | _ 
      { None }
(*s Applying the scanners to files *)

{
  let coq_file f m =
    reset ();
    let c = open_in f in
    let lb = from_channel c in
      (Index.current_library := m;
       Output.start_module ();
       Output.start_coq (); coq_bol lb; Output.end_coq ();
       close_in c)

  let detect_subtitle f m =
    let c = open_in f in
    let lb = from_channel c in
    let sub = st_start m lb in
      close_in c;
      sub
}
