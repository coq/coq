(* line-oriented Syntactic analyser for a Coq parser *)
(* This parser expects a very small number of commands, each given on a complete
line.  Some of these commands are then followed by a text fragment terminated
by a precise keyword, which is also expected to appear alone on a line. *)

(* The main parsing loop procedure is "parser_loop", given at the end of this
file.  It read lines one by one and checks whether they can be parsed using
a very simple parser.  This very simple parser uses a lexer, which is also given
in this file.

The lexical analyser:
 There are only 5 sorts of tokens *)
type simple_tokens = Tspace | Tid of string | Tint of int | Tstring of string |
      Tlbracket | Trbracket;;

(* When recognizing identifiers or strings, the lexical analyser accumulates
   the characters in a buffer, using the command add_in_buff.  To recuperate
   the characters, one can use get_buff (this code was inspired by the
   code in src/meta/lexer.ml of Coq revision 6.1) *)
let add_in_buff,get_buff =
  let buff = ref (String.create 80) in
    (fun i x ->
       let len = String.length !buff in
        if i >= len then (buff := !buff ^ (String.create len);());
         String.set !buff i x;
         succ i),
     (fun len -> String.sub !buff 0 len);;

(* Identifiers are [a-zA-Z_][.a-zA-Z0-9_]*.  When arriving here the first
   character has already been recognized. *)
let rec ident len = parser
  [<''_' | '.' | 'a'..'z' | 'A'..'Z' | '0'..'9' as c; s >] ->
    ident (add_in_buff len c) s
| [< >] -> let str = get_buff len in Tid(str);;

(* While recognizing integers, one constructs directly the integer value.
   The ascii code of '0' is important for this. *)
let code0 = Char.code '0';;

let get_digit c =  Char.code c - code0;;

(* Integers are [0-9]*
   The variable intval is the integer value of the text that has already
   been recognized.  As for identifiers, the first character has already been
   recognized. *)

let rec parse_int intval = parser
  [< ''0'..'9' as c ; i=parse_int (10 * intval + get_digit c)>] -> i
| [< >] -> Tint intval;;

(* The string lexer is borrowed from the string parser of Coq V6.1
   This may be a problem if convention have changed in Coq,
   However this parser is only used to recognize file names which should
   not contain too many special characters *)

let rec spec_char = parser
  [< ''n' >] -> '\n'
| [< ''t' >] -> '\t'
| [< ''b' >] -> '\008'
| [< ''r' >] -> '\013'
| [< ''0'..'9' as c; v= (spec1 (get_digit c)) >] ->
    Char.chr v
| [< 'x >] -> x

and spec1 v = parser
  [< ''0'..'9' as c; s >] -> spec1 (10*v+(get_digit c)) s
| [< >] -> v
;;

(* This is the actual string lexical analyser.  Strings are
   QUOT([^QUOT\\]|\\[0-9]*|\\[^0-9])QUOT (the word QUOT is used
   to represents double quotation characters, that cannot be used
   freely, even inside comments. *)

let rec string len = parser
  [< ''"' >] -> len
| [<''\\' ;
      len = (parser [< ''\n' >] -> len
             | [< c=spec_char >] -> add_in_buff len c);
      s >] -> string len s
| [< 'x; s >] -> string (add_in_buff len x) s;;

(* The lexical analyser repeats the recognized given by next_token:
   spaces and tabulations are ignored, identifiers, integers,
   strings, opening and closing square brackets.  Lexical errors are
   ignored ! *)
let rec next_token = parser _count
  [< '' ' | '\t'; tok = next_token >] -> tok
| [< ''_' | 'a'..'z' | 'A'..'Z' as c;i = (ident (add_in_buff 0 c))>] -> i
| [< ''0'..'9' as c ; i = (parse_int (get_digit c))>] -> i
| [< ''"' ; len = (string 0) >] -> Tstring (get_buff len)
| [< ''[' >] -> Tlbracket
| [< '']' >] -> Trbracket
| [< '_ ; x = next_token >] -> x;;

(* A very simple lexical analyser to recognize a integer value behind
   blank characters *)

let rec next_int = parser _count
  [< '' ' | '\t'; v = next_int >] -> v
| [< ''0'..'9' as c; i = (parse_int (get_digit c))>] ->
     (match i with
        Tint n -> n
     |  _ -> failwith "unexpected branch in next_int");;

(* This is the actual lexical analyser, implemented as a function on a stream.
   It will be used with the Stream.from primitive to construct a function
   of type char Stream.t -> simple_token option Stream.t *)
let token_stream cs _ =
 try  let tok = next_token cs in
      Some tok
 with Stream.Failure -> None;;

(* Two of the actions of the parser request that one reads the rest of
   the input up to a specific string stop_string.  This is done
   with a function that transform the input_channel into a pair of
   char Stream.t, reading from the input_channel all the lines to
   the stop_string first. *)


let rec gather_strings stop_string input_channel =
   let buff = input_line input_channel in
   if buff = stop_string then
     []
   else
     (buff::(gather_strings stop_string input_channel));;


(* the result of this function is supposed to be used in a Stream.from
   construction. *)

let line_list_to_stream string_list =
   let count = ref 0 in
   let buff = ref "" in
   let reserve = ref string_list in
   let current_length = ref 0 in
   (fun i -> if (i - !count) >= !current_length then
               begin
                  count := !count + !current_length + 1;
                  match !reserve with
		  | [] -> None
                  | s1::rest ->
                    begin
                      buff := s1;
                      current_length := String.length !buff;
		      reserve := rest;
                      Some '\n'
                    end
               end
             else
               Some(String.get !buff (i - !count)));;


(* In older revisions of this file you would find a function that
   does line oriented breakdown of the input channel without resorting to
   a list of lines.  However, the need for the list of line appeared when
   we wanted to have  a channel and a list of strings describing the same
   data, one for regular parsing and the other for error recovery. *)

let channel_to_stream_and_string_list stop_string input_channel =
   let string_list = gather_strings stop_string input_channel in
   (line_list_to_stream string_list, string_list);;

let flush_until_end_of_stream char_stream =
 Stream.iter (function _ -> ()) char_stream;;

(* There are only 5 kinds of lines recognized by our little parser.
   Unrecognized lines are ignored. *)
type parser_request =
  | PRINT_VERSION
  | PARSE_STRING of string
      (* parse_string <int> [<ident>] then text and && END--OF--DATA *)
  | QUIET_PARSE_STRING
      (* quiet_parse_string then text and && END--OF--DATA *)
  | PARSE_FILE of string
      (* parse_file <int> <string> *)
  | ADD_PATH of string
      (* add_path <int> <string> *)
  | ADD_REC_PATH of string * string
      (* add_rec_path <int> <string> <ident> *)
  | LOAD_SYNTAX of string
      (* load_syntax_file <int> <ident> *)
  | GARBAGE
;;

(* The procedure parser_loop should never terminate while the input_channel is
   not closed. This procedure receives the functions called for each sentence
   as arguments.  Thus the code is completely independent from the Coq sources. *)
let parser_loop functions input_channel =
  let print_version_action,
      parse_string_action,
      quiet_parse_string_action,
      parse_file_action,
      add_path_action,
      add_rec_path_action,
      load_syntax_action = functions in
  let rec parser_loop_rec input_channel =
  (let line = input_line input_channel in
  let reqid, parser_request =
      try
      (match Stream.from (token_stream (Stream.of_string line)) with
        parser
        | [< 'Tid "print_version" >] ->
                     0, PRINT_VERSION
        | [< 'Tid "parse_string" ; 'Tint reqid ; 'Tlbracket ;
             'Tid phylum ; 'Trbracket >]
                  -> reqid,PARSE_STRING phylum
        | [< 'Tid "quiet_parse_string" >] ->
                     0,QUIET_PARSE_STRING
        | [< 'Tid "parse_file" ; 'Tint reqid ; 'Tstring fname >] ->
                     reqid, PARSE_FILE fname
        | [< 'Tid "add_rec_path"; 'Tint reqid ; 'Tstring directory ;  'Tid alias >]
            -> reqid, ADD_REC_PATH(directory, alias)
        | [< 'Tid "add_path"; 'Tint reqid ; 'Tstring directory >]
            -> reqid, ADD_PATH directory
        | [< 'Tid "load_syntax_file"; 'Tint reqid; 'Tid module_name >] ->
               reqid, LOAD_SYNTAX module_name
	| [< 'Tid "quit_parser" >] -> raise End_of_file
        | [< >] -> 0, GARBAGE)
       with
         Stream.Failure | Stream.Error _ -> 0,GARBAGE in
   match parser_request with
     PRINT_VERSION -> print_version_action ()
   | PARSE_STRING phylum ->
     let regular_stream, string_list =
        channel_to_stream_and_string_list "&& END--OF--DATA" input_channel in
      parse_string_action reqid phylum (Stream.from regular_stream)
        string_list;()
   | QUIET_PARSE_STRING ->
     let regular_stream, string_list =
        channel_to_stream_and_string_list "&& END--OF--DATA" input_channel in
       quiet_parse_string_action
        (Stream.from regular_stream);()
   | PARSE_FILE file_name ->
        parse_file_action reqid file_name
   | ADD_PATH path -> add_path_action reqid path
   | ADD_REC_PATH(path, alias) -> add_rec_path_action reqid path alias
   | LOAD_SYNTAX syn -> load_syntax_action reqid syn
   | GARBAGE -> ());
   parser_loop_rec input_channel in
   parser_loop_rec input_channel;;
