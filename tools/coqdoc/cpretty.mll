(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(*s Utility functions for the scanners *)

{
  open Printf
  open Lexing
  open Common

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

  let count_newlines s =
    let len = String.length s in
    let n = ref 0 in
    String.iteri (fun i c ->
      match c with (* skip "\r\n" *)
      | '\r' when i + 1 = len || s.[i+1] = '\n' -> incr n
      | '\n' -> incr n
      | _ -> ()) s;
    !n

  (* Whether a string starts with a newline (used on strings that might match the [nl] regexp) *)
  let is_nl s = String.length s = 0 || let c = s.[0] in c = '\n' || c = '\r'

  let remove_newline s =
    let n = String.length s in
    let rec count i = if i == n || s.[i] <> '\n' then i else count (i + 1) in
    let i = count 0 in
    i, String.sub s i (n - i)

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

  let is_none x =
    match x with
    | None -> true
    | Some _ -> false

  let formatted : position option ref = ref None
  let brackets = ref 0
  let comment_level = ref 0
  let in_proof = ref None

  let in_env start stop =
    let r = ref false in
    let start_env () = r := true; start () in
    let stop_env () = if !r then stop (); r := false in
      (fun x -> !r), start_env, stop_env

  let _, start_emph, stop_emph = in_env Output.start_emph Output.stop_emph
  let in_quote, start_quote, stop_quote = in_env Output.start_quote Output.stop_quote

  let url_buffer = Buffer.create 40
  let url_name_buffer = Buffer.create 40

  let backtrack lexbuf = lexbuf.lex_curr_pos <- lexbuf.lex_start_pos;
    lexbuf.lex_curr_p <- lexbuf.lex_start_p

  let backtrack_past_newline lexbuf =
    let buf = lexeme lexbuf in
    let splits = Str.bounded_split_delim (Str.regexp "['\n']") buf 2 in
      match splits with
        | [] -> ()
        | (_ :: []) -> ()
        | (s1 :: rest :: _) ->
            let length_skip = 1 + String.length s1 in
              lexbuf.lex_curr_pos <- lexbuf.lex_start_pos + length_skip

  (* saving/restoring the PP state *)

  type state = {
    st_gallina : bool;
    st_light : bool
  }

  let state_stack = Stack.create ()

  let save_state () =
    Stack.push { st_gallina = !prefs.gallina; st_light = !prefs.light } state_stack

  let restore_state () =
    let s = Stack.pop state_stack in
    prefs := { !prefs with gallina = s.st_gallina };
    prefs := { !prefs with light = s.st_light }

  let begin_show () = save_state ();
  prefs := { { !prefs with gallina = false } with light = false }
  let end_show () = restore_state ()

  let begin_details s =
    save_state ();
    prefs := { { !prefs with gallina = false } with light = false };
    Output.start_details s
  let end_details () = Output.stop_details (); restore_state ()

  (* Reset the globals *)

  let reset () =
    formatted := None;
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
      if n_dashes >= 4 && not !prefs.plain_comments then
        Rule
      else
        if n_dashes = 1 && not !prefs.plain_comments then
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
      "[ \t]*\\(\\(%\\([^%]*\\)%\\)\\|\\(\\$[^$]*\\$\\)\\)?[ \t]*\\(#\\(\\(&#\\|[^#]\\)*\\)#\\)?"

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

  let output_indented_keyword s lexbuf =
    let nbsp,isp = count_spaces s in
    Output.indentation nbsp;
    let s = String.sub s isp (String.length s - isp) in
    Output.keyword s (lexeme_start lexbuf + isp)

  let only_gallina () =
    !prefs.gallina && !in_proof <> None

  let parse_comments () =
    !prefs.parse_comments && not (only_gallina ())

  (* Advance lexbuf by n lines. Equivalent to calling [Lexing.new_line lexbuf] n times *)
  let new_lines n lexbuf =
    let lcp = lexbuf.lex_curr_p in
    if lcp != dummy_pos then
      lexbuf.lex_curr_p <-
        { lcp with
          pos_lnum = lcp.pos_lnum + n;
          pos_bol = lcp.pos_cnum }

  let print_position_p chan p =
    Printf.fprintf chan "%s%d, character %d"
    (if p.pos_fname = "" then "Line " else "File \"" ^ p.pos_fname ^ "\", line ")
    p.pos_lnum (p.pos_cnum - p.pos_bol)

  let print_position chan {lex_start_p = p} = print_position_p chan p

  let warn msg lexbuf =
    eprintf "%a, warning: %s\n" print_position lexbuf msg;
    flush stderr

  exception MismatchPreformatted of position

  (* let debug lexbuf msg = Printf.printf "%a %s\n" print_position lexbuf.lex_start_p msg *)
}

(*s Regular expressions *)

let space = [' ' '\t']
let nl = "\r\n" | '\n' | '\r'
let space_nl = space | nl

let firstchar =
  ['A'-'Z' 'a'-'z' '_'] |
  (* superscript 1 *)
  '\194' '\185' |
  (* utf-8 latin 1 supplement *)
  '\195' ['\128'-'\150'] |
  '\195' ['\152'-'\182'] |
  '\195' ['\184'-'\191'] |
  (* utf-8 letterlike symbols *)
  '\206' (['\145'-'\161'] | ['\163'-'\191']) |
  '\207' (['\145'-'\191']) |
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
let nonidentchar = [^ 'A'-'Z' 'a'-'z' '_' '[' ']' '\'' '0'-'9' '@' '\"' '\'' '`']

let printing_token = [^ ' ' '\t']*

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
  | "Proof" (space* "." | space+ "with" | space+ "using")

let immediate_prf_token =
  (* Approximation of a proof term, if not in the prf_token case *)
  (* To be checked after prf_token *)
  "Proof" space* [^ '.' 'w' 'u']

let def_token =
  "Definition"
  | "Let"
  | "Let" space* "Fixpoint"
  | "Let" space* "CoFixpoint"
  | "Class"
  | "SubClass"
  | "Example"
  | "Fixpoint"
  | "Function"
  | "Boxed"
  | "CoFixpoint"
  | "Record"
  | "Variant"
  | "Structure"
  | "Scheme"
  | "Combined" space+ "Scheme"
  | "Inductive"
  | "CoInductive"
  | "Equations"
  | "Instance"
  | "Existing" space+ ("Instance" | "Instances" | "Class")
  | "Declare" space+ "Instance"
  | "Functional" space+ "Scheme"

let decl_token =
  "Hypothesis"
  | "Hypotheses"
  | "Parameter" 's'?
  | "Axiom" 's'?
  | "Conjecture"
  | "Primitive"
  | "Constraint"
  | "Universe"
  | "Universes"
  | "Register"

let gallina_ext =
  "Module"
  | "Include" space+ "Type"
  | "Include"
  | "Declare" space+ "Module"
  | "Transparent"
  | "Opaque"
  | "Typeclasses" space+ "Transparent"
  | "Typeclasses" space+ "Opaque"
  | "Canonical"
  | "Coercion"
  | "Identity"
  | "Implicit"
  | "Tactic" space+ "Notation"
  | "Section"
  | "Context"
  | "Variable" 's'?
  | ("Hypothesis" | "Hypotheses")
  | "End"

let notation_kw =
    "Notation"
  | "Infix"
  | "Reserved" space+ "Notation"
  | "Reserved" space+ "Infix"
  | "Number" space+ "Notation"
  | "String" space+ "Notation"
  | "Enable" space+ "Notation"
  | "Disable" space+ "Notation"

let commands =
  "Pwd"
  | "Cd"
  | "Drop"
  | "ProtectedLoop"
  | "Quit"
  | "Restart"
  | "Load"
  | "Add"
  | "Remove" space+ "Loadpath"
  | "Print"
  | "Inspect"
  | "About"
  | "SearchAbout"
  | "SearchRewrite"
  | "Search"
  | "Locate"
  | "Eval"
  | "Reset"
  | "Check"
  | "Type"

  | "Section"
  | "Chapter"
  | "Variable" 's'?
  | ("Hypothesis" | "Hypotheses")
  | "End"

let end_kw =
  immediate_prf_token | "Qed" | "Defined" | "Save" | "Admitted" | "Abort"

let extraction =
  "Extraction"
  | "Recursive" space+ "Extraction"
  | "Extract"

let gallina_kw = thm_token | def_token | decl_token | gallina_ext | commands | extraction

let legacy_attr_kw =
  "Local"
  | "Global"
  | "Polymorphic"
  | "Monomorphic"
  | "Cumulative"
  | "NonCumulative"
  | "Private"

let prog_kw =
  "Program" space+ (legacy_attr_kw space+)* gallina_kw
  | "Obligation"
  | "Obligations"
  | "Solve"

let hint_kw =
  "Extern" | "Rewrite" | "Resolve" | "Immediate" | "Transparent" | "Opaque" | "Unfold" | "Constructors"

let set_kw =
    "Printing" space+ ("Coercions" | "Universes" | "All")
  | "Implicit" space+ "Arguments"


let gallina_kw_to_hide =
    "Implicit" space+ "Arguments"
  | "Arguments"
  | "Ltac"
  | "From"
  | "Require"
  | "Import"
  | "Export"
  | "Load"
  | "Hint" space+ hint_kw
  | "Create" space+ "HintDb"
  | "Removed" space+ "Hints"
  | "Open"
  | "Close"
  | "Delimit"
  | "Undelimit"
  | "Declare" space+ "Scope"
  | "Bind" space+ "Scope"
  | "Format"
  | "Transparent"
  | "Opaque"
  | "Strategy"
  | "Derive"
  | "Generalizable" space+ ("All" space+ "Variables" | "No" space+ "Variables" | "Variable" | "Variables")
  | ("Declare" space+ ("Morphism" | "Step") )
  | ("Set" | "Unset") space+ set_kw
  | "Declare" space+ ("Left" | "Right") space+ "Step"
  | "Debug" space+ ("On" | "Off")
  | "Collection"


let section = "*" | "**" | "***" | "****"

let item_space = "    "

let begin_hide = "(*" space* "begin" space+ "hide" space* "*)" space*
let end_hide = "(*" space* "end" space+ "hide" space* "*)" space*
let begin_show = "(*" space* "begin" space+ "show" space* "*)" space*
let end_show = "(*" space* "end" space+ "show" space* "*)" space*
let begin_details = "(*" space* "begin" space+ "details" space*
let end_details = "(*" space* "end" space+ "details" space* "*)" space*
(*
let begin_verb = "(*" space* "begin" space+ "verb" space* "*)"
let end_verb = "(*" space* "end" space+ "verb" space* "*)"
*)

(*s Scanning Rocq, at beginning of line *)

rule coq_bol = parse
  | space* (nl+ as s)
      { new_lines (String.length s) lexbuf;
        if not (!in_proof <> None && (!prefs.gallina || !prefs.light))
        then Output.empty_line_of_code ();
        coq_bol lexbuf }
  | space* "(**" (space_nl as s)
    { if is_nl s then new_lines 1 lexbuf;
      Output.end_coq (); Output.start_doc ();
      let eol = doc_bol lexbuf in
        Output.end_doc (); Output.start_coq ();
        if eol then coq_bol lexbuf else coq lexbuf }
  | space* "Comments" (space_nl as s)
      { if is_nl s then new_lines 1 lexbuf;
        Output.end_coq (); Output.start_doc ();
        comments lexbuf;
        Output.end_doc (); Output.start_coq ();
        coq lexbuf }
  | space* begin_hide nl
      { new_lines 1 lexbuf; skip_hide lexbuf; coq_bol lexbuf }
  | space* begin_show nl
      { new_lines 1 lexbuf; begin_show (); coq_bol lexbuf }
  | space* end_show nl
      { new_lines 1 lexbuf; end_show (); coq_bol lexbuf }
  | space* begin_details (* At this point, the comment remains open,
                            and will be closed by [details_body] *)
      { let s = details_body lexbuf in
        Output.end_coq (); begin_details s; Output.start_coq (); coq_bol lexbuf }
  | space* end_details nl
      { new_lines 1 lexbuf;
        Output.end_coq (); end_details (); Output.start_coq (); coq_bol lexbuf }
  | space* (legacy_attr_kw space+)* gallina_kw_to_hide
      { let s = lexeme lexbuf in
          if !prefs.light && section_or_end s then
            let eol = skip_to_dot lexbuf in
              if eol then (coq_bol lexbuf) else coq lexbuf
          else
            begin
              output_indented_keyword s lexbuf;
              let eol = body lexbuf in
              if eol then coq_bol lexbuf else coq lexbuf
            end }
  | space* (legacy_attr_kw space+)* thm_token
      { let s = lexeme lexbuf in
          output_indented_keyword s lexbuf;
        let eol = body lexbuf in
          in_proof := Some eol;
        if eol then coq_bol lexbuf else coq lexbuf }
  | space* prf_token
      { in_proof := Some true;
        let eol =
          if not !prefs.gallina then
            begin backtrack lexbuf; body_bol lexbuf end
          else
            let s = lexeme lexbuf in
              if s.[String.length s - 1] = '.' then false
              else skip_to_dot lexbuf
        in if eol then coq_bol lexbuf else coq lexbuf }
  | space* end_kw {
      let eol =
        if not (only_gallina ()) then
          begin backtrack lexbuf; body_bol lexbuf end
        else skip_to_dot lexbuf
      in
        in_proof := None;
        if eol then coq_bol lexbuf else coq lexbuf }
  | space* (legacy_attr_kw space+)* gallina_kw
      {
        in_proof := None;
        let s = lexeme lexbuf in
          output_indented_keyword s lexbuf;
        let eol= body lexbuf in
          if eol then coq_bol lexbuf else coq lexbuf }
  | space* (legacy_attr_kw space+)* prog_kw
      {
        in_proof := None;
        let s = lexeme lexbuf in
          output_indented_keyword s lexbuf;
        let eol= body lexbuf in
          if eol then coq_bol lexbuf else coq lexbuf }
  | space* (legacy_attr_kw space+)* notation_kw
      {	let s = lexeme lexbuf in
          output_indented_keyword s lexbuf;
        let eol= start_notation_string lexbuf in
          if eol then coq_bol lexbuf else coq lexbuf }

  | space* "(**" space+ "printing" space+ printing_token space+
      { let tok = lexeme lexbuf in
        let s = printing_token_body lexbuf in
          add_printing_token tok s;
          coq_bol lexbuf }
  | space* "(**" space+ "printing" space+
      { warn "bad 'printing' command" lexbuf;
        comment_level := 1;
        ignore (comment lexbuf);
        coq_bol lexbuf }
  | space* "(**" space+ "remove" space+ "printing" space+
      printing_token space* "*)"
      { remove_printing_token (lexeme lexbuf);
        coq_bol lexbuf }
  | space* "(**" space+ "remove" space+ "printing" space+
      { warn "bad 'remove printing' command" lexbuf;
        comment_level := 1;
        ignore (comment lexbuf);
        coq_bol lexbuf }
  | space* "(*"
      { comment_level := 1;
        let eol =
          if parse_comments () then begin
            let s = lexeme lexbuf in
            let nbsp, isp = count_spaces s in
            Output.indentation nbsp;
            Output.start_comment ();
            comment lexbuf
          end else skipped_comment lexbuf in
        if eol then coq_bol lexbuf else coq lexbuf }
  | space* "#[" {
    let eol = begin backtrack lexbuf; body_bol lexbuf end
    in if eol then coq_bol lexbuf else coq lexbuf }
  | eof
      { () }
  | _
      { let eol =
          if not !prefs.gallina then
            begin backtrack lexbuf; body_bol lexbuf end
          else
            skip_to_dot_or_brace lexbuf
        in
          if eol then coq_bol lexbuf else coq lexbuf }

(*s Scanning Rocq elsewhere *)

and coq = parse
  | nl
    { new_lines 1 lexbuf; if not (only_gallina ()) then Output.line_break(); coq_bol lexbuf }
  | "(**" (space_nl as s)
    { if is_nl s then new_lines 1 lexbuf;
      Output.end_coq (); Output.start_doc ();
      let eol = doc_bol lexbuf in
        Output.end_doc (); Output.start_coq ();
        if eol then coq_bol lexbuf else coq lexbuf }
  | "(*"
      { comment_level := 1;
        let eol =
          if parse_comments () then begin
            Output.start_comment ();
            comment lexbuf
          end else skipped_comment lexbuf in
        if eol then coq_bol lexbuf else coq lexbuf }
  | (nl+ as s) space* "]]"
      { new_lines (count_newlines s) lexbuf;
        if is_none !formatted then
        begin
          (* Isn't this an anomaly *)
          let s = lexeme lexbuf in
          let nlsp,s = remove_newline s in
          let nbsp,isp = count_spaces s in
          Output.indentation nbsp;
          let loc = lexeme_start lexbuf + isp + nlsp in
          Output.sublexer ']' loc;
          Output.sublexer ']' (loc+1);
          coq lexbuf
          end }
  | eof
      { () }
  | (legacy_attr_kw space+)* gallina_kw_to_hide
      { let s = lexeme lexbuf in
          if !prefs.light && section_or_end s then
            begin
              let eol = skip_to_dot lexbuf in
                if eol then coq_bol lexbuf else coq lexbuf end
          else
            begin
              Output.ident s None;
              let eol=body lexbuf in
                if eol then coq_bol lexbuf else coq lexbuf end }
  | prf_token
      { let eol =
          if not !prefs.gallina then
            begin backtrack lexbuf; body lexbuf end
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
        if not !prefs.gallina then
          begin backtrack lexbuf; body lexbuf end
        else
          let eol = skip_to_dot lexbuf in
            if !in_proof <> Some true && eol then
              Output.line_break ();
            eol
       in
        in_proof := None;
        if eol then coq_bol lexbuf else coq lexbuf }
  | (legacy_attr_kw space+)* gallina_kw
      { let s = lexeme lexbuf in
          Output.ident s None;
        let eol = body lexbuf in
          if eol then coq_bol lexbuf else coq lexbuf }
  | (legacy_attr_kw space+)* notation_kw
      { let s = lexeme lexbuf in
          Output.ident s None;
        let eol= start_notation_string lexbuf in
          if eol then coq_bol lexbuf else coq lexbuf }
  | (legacy_attr_kw space+)* prog_kw
      { let s = lexeme lexbuf in
          Output.ident s None;
        let eol = body lexbuf in
          if eol then coq_bol lexbuf else coq lexbuf }
  | "#["
      { ignore(lexeme lexbuf);
        Output.char '#'; Output.char '[';
        let eol = body lexbuf in
          if eol then coq_bol lexbuf else coq lexbuf }
  | space+ { Output.char ' '; coq lexbuf }
  | eof
      { () }
  | _ {	let eol =
          if not !prefs.gallina then
            begin backtrack lexbuf; body lexbuf end
          else
            skip_to_dot_or_brace lexbuf
        in
          if eol then coq_bol lexbuf else coq lexbuf}

(*s Scanning documentation, at beginning of line *)

and doc_bol = parse
  | space* section space+ ([^'\n' '\r' '*'] | '*'+ [^'\n' '\r' ')' '*'])* ('*'+ (nl as s))?
      { if not (is_none s) then new_lines 1 lexbuf;
        let eol, lex = strip_eol (lexeme lexbuf) in
        let lev, s = sec_title lex in
          if (!prefs.lib_subtitles) &&
             (subtitle (Output.get_module false) s) then
            ()
          else
            Output.section lev (fun () -> ignore (doc None (from_string s)));
            if eol then doc_bol lexbuf else doc None lexbuf }
  | ((space_nl* nl)? as s) (space* '-'+ as line)
      { let nl_count = count_newlines s in
        match check_start_list line with
          | Neither -> backtrack_past_newline lexbuf; new_lines 1 lexbuf; doc None lexbuf
          | List n ->
              new_lines nl_count lexbuf;
              if nl_count > 0 then Output.paragraph ();
              Output.item 1; doc (Some [n]) lexbuf
          | Rule ->
              new_lines nl_count lexbuf;
              Output.rule (); doc None lexbuf
      }
  | (space_nl* nl) as s
      { new_lines (count_newlines s) lexbuf; Output.paragraph (); doc_bol lexbuf }
  | "<<" space* nl
      { new_lines 1 lexbuf; Output.start_verbatim false; verbatim_block lexbuf; doc_bol lexbuf }
  | "<<"
      { Output.start_verbatim true; verbatim_inline lexbuf; doc None lexbuf }
  | eof
      { true }
  | '_'
      { if !prefs.plain_comments then Output.char '_' else start_emph ();
        doc None lexbuf }
  | "" { doc None lexbuf }

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
  | "<<" space* nl
      { new_lines 1 lexbuf; Output.start_verbatim false;
        verbatim_block lexbuf;
        doc_list_bol indents lexbuf }
  | "<<" space*
      { Output.start_verbatim true;
        verbatim_inline lexbuf;
        doc (Some indents) lexbuf }
  | "[[" nl
      { new_lines 1 lexbuf; formatted := Some lexbuf.lex_start_p;
        Output.start_inline_coq_block ();
        ignore(body_bol lexbuf);
        Output.end_inline_coq_block ();
        formatted := None;
        doc_list_bol indents lexbuf }
  | "[[[" nl
      { new_lines 1 lexbuf; inf_rules (Some indents) lexbuf }
  | space* nl space* '-'
      { (* Like in the doc_bol production, these two productions
           exist only to deal properly with whitespace *)
        new_lines 1 lexbuf;
        Output.paragraph ();
        backtrack_past_newline lexbuf;
        doc_list_bol indents lexbuf }
  | space* nl space* _
      { new_lines 1 lexbuf;
        let buf' = lexeme lexbuf in
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
        | StartLevel 1 | Before ->
        (* Here we were at the beginning of a line, and it was blank.
           The next line started before any list items.  So: insert
           a paragraph for the empty line, rewind to whatever's just
           after the newline, then toss over to doc_bol for whatever
           comes next. *)
            Output.stop_item ();
            Output.paragraph ();
            backtrack_past_newline lexbuf;
            doc_bol lexbuf
        | StartLevel _ | InLevel _ ->
            Output.paragraph ();
            backtrack_past_newline lexbuf;
            doc_list_bol indents lexbuf

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
      { new_lines 1 lexbuf;
        Output.char '\n';
        match indents with
        | Some ls -> doc_list_bol ls lexbuf
        | None -> doc_bol lexbuf }
  | "[[" nl
      { new_lines 1 lexbuf;
        if !prefs.plain_comments
        then (Output.char '['; Output.char '['; doc indents lexbuf)
        else (formatted := Some lexbuf.lex_start_p;
              Output.start_inline_coq_block ();
              let eol = body_bol lexbuf in
                Output.end_inline_coq_block (); formatted := None;
                if eol then
                  match indents with
                  | Some ls -> doc_list_bol ls lexbuf
                  | None -> doc_bol lexbuf
                else doc indents lexbuf)}
  | "[[[" nl
      { new_lines 1 lexbuf; inf_rules indents lexbuf }
  | "[]"
      { Output.proofbox (); doc indents lexbuf }
  | "{{" { url lexbuf; doc indents lexbuf }
  | "["
      { if !prefs.plain_comments then Output.char '['
        else (brackets := 1;  Output.start_inline_coq (); escaped_coq lexbuf;
              Output.end_inline_coq ()); doc indents lexbuf }
  | "(*"
      { backtrack lexbuf ;
        let bol_parse = match indents with
                        | Some is -> doc_list_bol is
                        | None   -> doc_bol
        in
        let eol =
          if !prefs.parse_comments then comment lexbuf
          else skipped_comment lexbuf in
        if eol then bol_parse lexbuf else doc indents lexbuf }
  | '*'* "*)" (space_nl* as s) "(**"
      { let nl_count = count_newlines s in
        new_lines nl_count lexbuf;
       (match indents with
        | Some _ -> Output.stop_item ()
        | None -> ());
       (* this says - if there is a blank line between the two comments,
          insert one in the output too *)
         if nl_count > 1 then Output.paragraph ();
       doc_bol lexbuf
      }
  | '*'* "*)" space* nl
      { new_lines 1 lexbuf; Output.char '\n'; true }
  | '*'* "*)"
      { false }
  | "$"
      { if !prefs.plain_comments then Output.char '$'
        else (Output.start_latex_math (); escaped_math_latex lexbuf);
        doc indents lexbuf }
  | "$$"
      { if !prefs.plain_comments then Output.char '$';
        Output.char '$'; doc indents lexbuf }
  | "%"
      { if !prefs.plain_comments then Output.char '%'
        else escaped_latex lexbuf; doc indents lexbuf }
  | "%%"
      { if !prefs.plain_comments then Output.char '%';
        Output.char '%'; doc indents lexbuf }
  | "#"
      { if !prefs.plain_comments then Output.char '#'
        else escaped_html lexbuf; doc indents lexbuf }
  | "##"
      { if !prefs.plain_comments then Output.char '#';
        Output.char '#'; doc indents lexbuf }
  | nonidentchar '_' nonidentchar
      { List.iter (fun x -> Output.char (lexeme_char lexbuf x)) [0;1;2];
        doc indents lexbuf}
  | nonidentchar '_'
      { Output.char (lexeme_char lexbuf 0);
        if !prefs.plain_comments then Output.char '_' else  start_emph () ;
        doc indents lexbuf }
  | '_' nonidentchar
      { if !prefs.plain_comments then Output.char '_' else stop_emph () ;
        Output.char (lexeme_char lexbuf 1);
        doc indents lexbuf }
  | "<<" space*
      { Output.start_verbatim true; verbatim_inline lexbuf; doc indents lexbuf }
  | '"'
      { if !prefs.plain_comments
        then Output.char '"'
        else if in_quote ()
        then stop_quote ()
        else start_quote ();
        doc indents lexbuf }
  | eof
      { false }
  | _
      { Output.char (lexeme_char lexbuf 0); doc indents lexbuf }

(*s Various escapings *)

and escaped_math_latex = parse
  | "$" { Output.stop_latex_math () }
  | eof { Output.stop_latex_math () }
  | "*)"
        { Output.stop_latex_math (); backtrack lexbuf }
  | _   { Output.latex_char (lexeme_char lexbuf 0); escaped_math_latex lexbuf }

and escaped_latex = parse
  | "%" { () }
  | eof { () }
  | "*)"
        { backtrack lexbuf }
  | _   { Output.latex_char (lexeme_char lexbuf 0); escaped_latex lexbuf }

and escaped_html = parse
  | "#" { () }
  | "&#"
        { Output.html_char '&'; Output.html_char '#'; escaped_html lexbuf }
  | "##"
        { Output.html_char '#'; escaped_html lexbuf }
  | eof { () }
  | "*)"
        { backtrack lexbuf }
  | _   { Output.html_char (lexeme_char lexbuf 0); escaped_html lexbuf }

and verbatim_block = parse
  | nl ">>" space* nl { new_lines 2 lexbuf; Output.verbatim_char false '\n'; Output.stop_verbatim false }
  | nl ">>"
        { new_lines 1 lexbuf;
          warn "missing newline after \">>\" block" lexbuf;
          Output.verbatim_char false '\n';
          Output.stop_verbatim false }
  | eof { warn "unterminated \">>\" block" lexbuf; Output.stop_verbatim false }
  | nl { new_lines 1 lexbuf; Output.verbatim_char false (lexeme_char lexbuf 0); verbatim_block lexbuf }
  | _ { Output.verbatim_char false (lexeme_char lexbuf 0); verbatim_block lexbuf }

and verbatim_inline = parse
  | nl { new_lines 1 lexbuf;
         warn "unterminated inline \">>\"" lexbuf;
         Output.char '\n';
         Output.stop_verbatim true }
  | ">>" { Output.stop_verbatim true }
  | eof { warn "unterminated inline \">>\"" lexbuf; Output.stop_verbatim true }
  | _ { Output.verbatim_char true (lexeme_char lexbuf 0); verbatim_inline lexbuf }

and url = parse
  | "}}" { Output.url (Buffer.contents url_buffer) None; Buffer.clear url_buffer }
  | "}" { url_name lexbuf }
  | _ { Buffer.add_char url_buffer (lexeme_char lexbuf 0); url lexbuf }

and url_name = parse
  | "}" { Output.url (Buffer.contents url_buffer) (Some (Buffer.contents url_name_buffer));
          Buffer.clear url_buffer; Buffer.clear url_name_buffer }
  | _ { Buffer.add_char url_name_buffer (lexeme_char lexbuf 0); url_name lexbuf }

(*s Rocq, inside quotations *)

and escaped_coq = parse
  | "]"
      { decr brackets;
        if !brackets > 0 then
          (Output.sublexer_in_doc ']'; escaped_coq lexbuf)
        else Tokens.flush_sublexer () }
  | "["
      { incr brackets;
        Output.sublexer_in_doc '['; escaped_coq lexbuf }
  | "(*"
      { Tokens.flush_sublexer (); comment_level := 1;
        ignore (if !prefs.parse_comments then comment lexbuf
                else skipped_comment lexbuf);
        escaped_coq lexbuf }
  | "*)"
      { (* likely to be a syntax error *)
        warn "unterminated \"]\"" lexbuf; backtrack lexbuf }
  | eof
      { Tokens.flush_sublexer () }
  | identifier
      { Tokens.flush_sublexer();
        Output.ident (lexeme lexbuf) None;
        escaped_coq lexbuf }
  | space_nl*
      { let str = lexeme lexbuf in
          Tokens.flush_sublexer();
          (if !prefs.inline_notmono then ()
                                        else Output.end_inline_coq ());
          String.iter Output.char str;
          (if !prefs.inline_notmono then ()
                                        else Output.start_inline_coq ());
          escaped_coq lexbuf }
  | _
      { Output.sublexer_in_doc (lexeme_char lexbuf 0);
        escaped_coq lexbuf }

(*s Rocq "Comments" command. *)

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

and skipped_comment = parse
  | "(*"
      { incr comment_level;
        skipped_comment lexbuf }
  | "*)" space* nl
      { new_lines 1 lexbuf;
        decr comment_level;
        if !comment_level > 0 then skipped_comment lexbuf else true }
  | "*)"
      { decr comment_level;
        if !comment_level > 0 then skipped_comment lexbuf else false }
  | eof { false }
  | _ { skipped_comment lexbuf }

and comment = parse
  | "(*"
      { incr comment_level;
        Output.start_comment ();
        comment lexbuf }
  | "*)" space* nl
      { new_lines 1 lexbuf;
        Output.end_comment ();
        Output.line_break ();
        decr comment_level;
        if !comment_level > 0 then comment lexbuf else true }
  | "*)"
      { Output.end_comment ();
        decr comment_level;
        if !comment_level > 0 then comment lexbuf else false }
  | "["
      { if !prefs.plain_comments then Output.char '['
        else (brackets := 1; Output.start_inline_coq ();
              escaped_coq lexbuf; Output.end_inline_coq ());
        comment lexbuf }
  | "[[" nl
      { new_lines 1 lexbuf;
        if !prefs.plain_comments then (Output.char '['; Output.char '[')
        else (formatted := Some lexbuf.lex_start_p;
              Output.start_inline_coq_block ();
              let _ = body_bol lexbuf in
                Output.end_inline_coq_block (); formatted := None);
        comment lexbuf }
  | "$"
      { if !prefs.plain_comments then Output.char '$'
        else (Output.start_latex_math (); escaped_math_latex lexbuf);
        comment lexbuf }
  | "$$"
      { if !prefs.plain_comments then Output.char '$';
        Output.char '$';
        comment lexbuf }
  | "%"
      { if !prefs.plain_comments then Output.char '%'
        else escaped_latex lexbuf;
        comment lexbuf }
  | "%%"
      { if !prefs.plain_comments then Output.char '%';
        Output.char '%';
        comment lexbuf }
  | "#"
      { if !prefs.plain_comments then Output.char '#'
        else escaped_html lexbuf;
        comment lexbuf }
  | "##"
      { if !prefs.plain_comments then Output.char '#';
        Output.char '#';
        comment lexbuf }
  | eof  { false }
  | space+
      { Output.indentation (fst (count_spaces (lexeme lexbuf)));
        comment lexbuf }
  | nl
      { new_lines 1 lexbuf;
        Output.line_break ();
        comment lexbuf }
  | _ { Output.char (lexeme_char lexbuf 0);
        comment lexbuf }

and skip_to_dot = parse
  | '.' space* nl { new_lines 1 lexbuf; true }
  | eof | '.' space+ { false }
  | "(*"
      { comment_level := 1;
        ignore (skipped_comment lexbuf);
        skip_to_dot lexbuf }
  | _ { skip_to_dot lexbuf }

and skip_to_dot_or_brace = parse
  | '.' space* nl { new_lines 1 lexbuf; true }
  | eof | '.' space+ { false }
  | "(*"
      { comment_level := 1;
        ignore (skipped_comment lexbuf);
        skip_to_dot_or_brace lexbuf }
  | "}" space* nl
      { new_lines 1 lexbuf; true }
  | "}"
      { false }
  | space*
      { skip_to_dot_or_brace lexbuf }
  | _ { skip_to_dot lexbuf }

and body_bol = parse
  | space+
      { Output.indentation (fst (count_spaces (lexeme lexbuf))); body lexbuf }
  | "" { Output.indentation 0; body lexbuf }

and body = parse
  | nl { Tokens.flush_sublexer(); Output.line_break(); new_lines 1 lexbuf; body_bol lexbuf}
  | (nl+ as s) space* "]]" space* nl
      { new_lines (count_newlines s + 1) lexbuf;
        Tokens.flush_sublexer();
        if is_none !formatted then
          begin
            let s = lexeme lexbuf in
            let nlsp,s = remove_newline s in
            let _,isp = count_spaces s in
            let loc = lexeme_start lexbuf + nlsp + isp in
            Output.sublexer ']' loc;
            Output.sublexer ']' (loc+1);
            Tokens.flush_sublexer();
            body lexbuf
          end
        else
          begin
            Output.paragraph ();
            true
          end }
  | "]]" space* nl
      { Tokens.flush_sublexer();
        new_lines 1 lexbuf;
        if is_none !formatted then
          begin
            let loc = lexeme_start lexbuf in
            Output.sublexer ']' loc;
            Output.sublexer ']' (loc+1);
            Tokens.flush_sublexer();
            Output.line_break();
            body lexbuf
          end
        else
          begin
            Output.paragraph ();
            true
          end }
  | eof
    { Tokens.flush_sublexer();
      match !formatted with
      | None -> false
      | Some p -> raise (MismatchPreformatted p) }
  | '.' space* (nl as s | eof)
    { if not (is_none s) then new_line lexbuf;
      Tokens.flush_sublexer(); Output.char '.'; Output.line_break();
      if is_none !formatted then true else body_bol lexbuf }
  | '.' space* nl "]]" space* nl
    { new_lines 2 lexbuf;
      Tokens.flush_sublexer(); Output.char '.';
        if is_none !formatted then
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
  | '.' space+
        { Tokens.flush_sublexer(); Output.char '.'; Output.char ' ';
          if is_none !formatted then false else body lexbuf }
  | "(**" (space_nl as s)
      { if is_nl s then new_line lexbuf;
        Tokens.flush_sublexer(); Output.end_coq (); Output.start_doc ();
        let eol = doc_bol lexbuf in
          Output.end_doc (); Output.start_coq ();
          if eol then body_bol lexbuf else body lexbuf }
  | "(*"
      { Tokens.flush_sublexer(); comment_level := 1;
        let eol =
          if parse_comments () then begin
            Output.start_comment ();
            comment lexbuf
          end else begin
            let eol = skipped_comment lexbuf in
            if eol then Output.line_break();
            eol
          end in
        if eol then body_bol lexbuf else body lexbuf }
  | "where"
      { Tokens.flush_sublexer();
        Output.ident (lexeme lexbuf) None;
        start_notation_string lexbuf }
  | identifier
      { Tokens.flush_sublexer();
        Output.ident (lexeme lexbuf) (Some (lexeme_start lexbuf));
        body lexbuf }
  | ".."
      { Tokens.flush_sublexer(); Output.char '.'; Output.char '.';
        body lexbuf }
  | '"'
      { Tokens.flush_sublexer(); Output.char '"';
        string lexbuf;
        body lexbuf }
  | space
      { Tokens.flush_sublexer(); Output.char (lexeme_char lexbuf 0);
        body lexbuf }

  | _ { let c = lexeme_char lexbuf 0 in
        Output.sublexer c (lexeme_start lexbuf);
        body lexbuf }

and start_notation_string = parse
  | space { Tokens.flush_sublexer(); Output.char (lexeme_char lexbuf 0);
            start_notation_string lexbuf }
  | '"' (* a true notation *)
      { Output.sublexer '"' (lexeme_start lexbuf);
        notation_string lexbuf;
        body lexbuf }
  | _ (* an abbreviation *)
      { backtrack lexbuf; body lexbuf }

and notation_string = parse
  | "\"\""
      { Output.char '"'; Output.char '"'; (* Unlikely! *)
        notation_string lexbuf }
  | '"'
      { Tokens.flush_sublexer(); Output.char '"' }
  | _ { let c = lexeme_char lexbuf 0 in
        Output.sublexer c (lexeme_start lexbuf);
        notation_string lexbuf }

and string = parse
  | "\"\"" { Output.char '"'; Output.char '"'; string lexbuf }
  | '"'    { Output.char '"' }
  | _      { let c = lexeme_char lexbuf 0 in Output.char c; string lexbuf }

and skip_hide = parse
  | eof | end_hide nl { new_lines 1 lexbuf; () }
  | _ { skip_hide lexbuf }

(*s Reading token pretty-print *)

and printing_token_body = parse
  | "*)" (nl as s)? | eof
    { if not (is_none s) then new_lines 1 lexbuf;
      let s = Buffer.contents token_buffer in
        Buffer.clear token_buffer;
        s }
  | (nl | _) as s
    { if is_nl s then new_lines 1 lexbuf;
      Buffer.add_string token_buffer (lexeme lexbuf);
      printing_token_body lexbuf }

and details_body = parse
  | "*)" space* (nl as s)? | eof
      { if not (is_none s) then new_lines 1 lexbuf;
        None }
  | ":" space*  { details_body_rec lexbuf }

and details_body_rec = parse
  | "*)" space* (nl as s)? | eof
        { if not (is_none s) then new_lines 1 lexbuf;
          let s = Buffer.contents token_buffer in
          Buffer.clear token_buffer;
          Some s }
  | _   { Buffer.add_string token_buffer (lexeme lexbuf);
          details_body_rec lexbuf }

(*s These handle inference rules, parsing the body segments of things
    enclosed in [[[  ]]] brackets *)
and inf_rules indents = parse
  | space* nl     (* blank line, before or between definitions *)
      { new_lines 1 lexbuf; inf_rules indents lexbuf }
  | "]]]" nl      (* end of the inference rules block *)
      { new_lines 1 lexbuf;
        match indents with
        | Some ls -> doc_list_bol ls lexbuf
        | None -> doc_bol lexbuf }
  | _
      { backtrack lexbuf;  (* anything else must be the first line in a rule *)
        inf_rules_assumptions indents [] lexbuf}

(* The inference rule parsing just collects the inference rule and then
   calls the output function once, instead of doing things incrementally
   like the rest of the lexer.  If only there were a real parsing phase...
*)
and inf_rules_assumptions indents assumptions = parse
  | space* "---" '-'* [^ '\n']* nl (* hit the horizontal line *)
      { new_lines 1 lexbuf;
        let line = lexeme lexbuf in
        let (spaces,_) = count_spaces line in
        let dashes_and_name =
               cut_head_tail_spaces (String.sub line 0 (String.length line - 1))
        in
        let ldn = String.length dashes_and_name in
        let (dashes,name) =
          try (let i = String.index dashes_and_name ' ' in
               let d = String.sub dashes_and_name 0 i in
               let n = cut_head_tail_spaces
                        (String.sub dashes_and_name (i+1) (ldn-i-1))
               in
                 (d, Some n))
          with _ -> (dashes_and_name, None)

        in
          inf_rules_conclusion indents (List.rev assumptions)
                               (spaces, dashes, name) [] lexbuf }
  | [^ '\n']* nl (* if it's not the horizontal line, it's an assumption *)
      { new_lines 1 lexbuf;
        let line = lexeme lexbuf in
        let (spaces,_) = count_spaces line in
        let assumption = cut_head_tail_spaces
                            (String.sub line 0 (String.length line - 1))
        in
          inf_rules_assumptions indents ((spaces,assumption)::assumptions)
                                lexbuf }

(*s The conclusion is required to come immediately after the
    horizontal bar.  It is allowed to contain multiple lines of
    text, like the assumptions.  The conclusion ends when we spot a
    blank line or a ']]]'. *)
and inf_rules_conclusion indents assumptions middle conclusions = parse
  | space* nl | space* "]]]" nl (* end of conclusions. *)
      { new_lines 2 lexbuf; backtrack lexbuf;
        Output.inf_rule assumptions middle (List.rev conclusions);
        inf_rules indents lexbuf }
  | space* [^ '\n']+ nl (* this is a line in the conclusion *)
      { new_lines 1 lexbuf;
        let line = lexeme lexbuf in
        let (spaces,_) = count_spaces line in
        let conc = cut_head_tail_spaces (String.sub line 0
                                                    (String.length line - 1))
        in
          inf_rules_conclusion indents assumptions middle
                               ((spaces,conc) :: conclusions) lexbuf
      }

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
  (* coq_bol with error handling *)
  let coq_bol' f lb =
    try coq_bol lb with
    | MismatchPreformatted p ->
      Printf.eprintf "%a: mismatched \"[[\"\n" print_position_p p;
      exit 1

  let coq_file f m =
    reset ();
    let c = open_in f in
    let lb = from_channel c in
    let lb = { lb with lex_curr_p = { lb.lex_curr_p with pos_fname = f };
                       lex_start_p = { lb.lex_start_p with pos_fname = f } } in
      (Index.current_library := m;
       Output.initialize ();
       Output.start_module ();
       Output.start_coq (); coq_bol' f lb; Output.end_coq ();
       close_in c)

  let detect_subtitle f m =
    let c = open_in f in
    let lb = from_channel c in
    let sub = st_start m lb in
      close_in c;
      sub
}
