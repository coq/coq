{

  open Lexing

  type color = string

  type highlight_order = int * int * color

  let comment_start = ref 0

  let kwd = [
  "Add"; "AddPath"; "Axiom"; "Chapter"; "CoFixpoint";
  "CoInductive";  "Compile"; "Defined"; "Definition"; 
  "End"; "Export"; "Fact"; "Fix"; "Fixpoint"; "Global"; "Grammar"; "Hint";
  "Hints"; "Hypothesis"; "Immediate"; "Implicits"; "Import"; "Inductive"; 
  "Infix"; "Lemma"; "Load"; "Local"; 
  "Match"; "Module"; "Module Type";
  "Mutual"; "Parameter"; "Print"; "Proof"; "Qed";
  "Record"; "Recursive"; "Remark"; "Require"; "Save"; "Scheme";
  "Section"; "Show"; "Syntactic"; "Syntax"; "Tactic"; "Theorem"; 
  "Unset"; "Variable"; "Variables"; 
  ]

module SHashtbl = 
  Hashtbl.Make 
    (struct 
       type t = string
       let equal = ( = )
       let hash = Hashtbl.hash
     end)

let word_tbl = SHashtbl.create 37
let _ =  List.iter (fun w -> SHashtbl.add word_tbl w "kwd") kwd
}

let keyword = 
  "Add" | "AddPath" | "Chapter" |
  "CoInductive" |  "Compile" | "Defined" | 
  "End" | "Export" | "Fact" | "Fix" | "Global" | 
  "Grammar" | "Hint" |
  "Hints" | "Immediate" | "Implicits" | "Import" | 
  "Infix" | "Load" | "Local" | 
  "Match" | "Module" | "Module Type" |
  "Mutual" | "Print" | "Proof" | "Qed" |
  "Record" | "Recursive" | "Require" | "Save" | "Scheme" |
  "Section" | "Show" | "Syntactic" | "Syntax" | "Tactic" |
  "Unset"

let space = 
  [' ' '\010' '\013' '\009' '\012']
let firstchar = 
  ['$' 'A'-'Z' 'a'-'z' '_' '\192'-'\214' '\216'-'\246' '\248'-'\255']
let identchar = 
  ['$' 'A'-'Z' 'a'-'z' '_' '\192'-'\214' '\216'-'\246' '\248'-'\255' '\'' '0'-'9']
let ident = firstchar identchar*

let declaration = 
  "Lemma" | "Axiom" | "CoFixpoint" |"Definition"  |
  "Fixpoint" | "Hypothesis" | 
  "Inductive" | "Parameter" | "Remark" |  "Theorem" | 
  "Variable" | "Variables"

rule next_order = parse
  | "(*" { comment_start := lexeme_start lexbuf; comment lexbuf }
  | keyword { lexeme_start lexbuf,lexeme_end lexbuf, "kwd" }
  | declaration space+ ident (space* ',' space* ident)* 
            { lexeme_start lexbuf, lexeme_end lexbuf, "decl" } 
  | _    { next_order lexbuf}
  | eof  { raise End_of_file }

and comment = parse
  | "*)" { !comment_start,lexeme_end lexbuf,"comment" }
  | "(*" { ignore (comment lexbuf); comment lexbuf }
  | _    { comment lexbuf }
  | eof  { raise End_of_file }

{
  open Ideutils

  let highlight_slice (input_buffer:GText.buffer) (start:GText.iter) stop = 
  let offset = start#offset in
  let s = start#get_slice ~stop in
  let convert_pos = byte_offset_to_char_offset s in
  let lb = Lexing.from_string s in
    try 
      while true do
	process_pending ();
	let b,e,o=next_order lb in
	let b,e = convert_pos b,convert_pos e in
	let start = input_buffer#get_iter_at_char (offset + b) in
	let stop = input_buffer#get_iter_at_char (offset + e) in
	  input_buffer#apply_tag_by_name ~start ~stop o 
      done
    with End_of_file -> ()
      | _ -> ()


  let highlight_current_line input_buffer = 
  let i = get_insert input_buffer in
    highlight_slice input_buffer (i#set_line_offset 0) i

  let highlight_all input_buffer = 
  highlight_slice input_buffer input_buffer#start_iter input_buffer#end_iter

}
