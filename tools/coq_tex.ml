(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* coq-tex
 * JCF, 16/1/98
 * adapted from caml-tex (perl script written by Xavier Leroy)
 *
 * Perl isn't as portable as it pretends to be, and is quite difficult
 * to read and maintain... Let us rewrite the stuff in Caml! *)

let linelen = ref 72
let output = ref ""
let output_specified = ref false
let image = ref ""
let cut_at_blanks = ref false
let verbose = ref false
let slanted = ref false
let hrule = ref false
let small = ref false
let boot = ref false

let coq_prompt = Str.regexp "Coq < "
let any_prompt = Str.regexp "^[A-Z0-9a-z_\\$']* < "

let remove_prompt s = Str.replace_first any_prompt "" s

(* First pass: extract the Coq phrases to evaluate from [texfile]
 * and put them into the file [inputv] *)

let begin_coq = Str.regexp "\\\\begin{coq_\\(example\\|example\\*\\|example\\#\\|eval\\)}[ \t]*$"
let end_coq   = Str.regexp "\\\\end{coq_\\(example\\|example\\*\\|example\\#\\|eval\\)}[ \t]*$"

let extract texfile inputv =
  let chan_in = open_in texfile in
  let chan_out = open_out inputv in
  let rec inside () =
    let s = input_line chan_in in
    if Str.string_match end_coq s 0 then
      outside ()
    else begin
      output_string chan_out (s ^ "\n");
      inside ()
    end
  and outside () =
    let s = input_line chan_in in
    if Str.string_match begin_coq s 0 then
      inside ()
    else
      outside ()
  in
  try
    output_string chan_out
      ("Set Printing Width " ^ (string_of_int !linelen) ^".\n");
    outside ()
  with End_of_file ->
    begin close_in chan_in; close_out chan_out end

(* Second pass: insert the answers of Coq from [coq_output] into the
 * TeX file [texfile]. The result goes in file [result]. *)

let begin_coq_example =
  Str.regexp "\\\\begin{coq_\\(example\\|example\\*\\|example\\#\\)}[ \t]*$"
let begin_coq_eval = Str.regexp "\\\\begin{coq_eval}[ \t]*$"
let end_coq_example = Str.regexp "\\\\end{coq_\\(example\\|example\\*\\|example\\#\\)}[ \t]*$"
let end_coq_eval = Str.regexp "\\\\end{coq_eval}[ \t]*$"
let dot_end_line = Str.regexp "\\.[ \t]*\\((\\*.*\\*)\\)?[ \t]*$"

let has_match r s =
  try let _ = Str.search_forward r s 0 in true with Not_found -> false

let percent = Str.regexp "%"
let bang    = Str.regexp "!"
let expos   = Str.regexp "^"

let tex_escaped s =
  let dollar = "\\$" and  backslash = "\\\\" and expon = "\\^" in
  let delims = Str.regexp ("[_{}&%#" ^ dollar ^ backslash ^ expon ^"~ <>']") in
  let adapt_delim = function
    | "_" | "{" | "}" | "&" | "%" | "#" | "$" as c -> "\\"^c
    | "\\" -> "{\\char'134}"
    | "^" -> "{\\char'136}"
    | "~" -> "{\\char'176}"
    | " " -> "~"
    | "<" -> "{<}"
    | ">" -> "{>}"
    | "'" -> "{\\textquotesingle}"
    | _ -> assert false
  in
  let adapt = function
    | Str.Text s -> s
    | Str.Delim s -> adapt_delim s
  in
  String.concat "" (List.map adapt (Str.full_split delims s))

let encapsule sl c_out s =
  if sl then
    Printf.fprintf c_out "\\texttt{\\textit{%s}}\\\\\n" (tex_escaped s)
  else
    Printf.fprintf c_out "\\texttt{%s}\\\\\n" (tex_escaped s)

let print_block c_out bl =
  List.iter (fun s -> if s="" then () else encapsule !slanted c_out s) bl

let insert texfile coq_output result =
  let c_tex = open_in texfile in
  let c_coq = open_in coq_output in
  let c_out = open_out result in
  (* next_block k : this function reads the next block of Coq output
   * removing the k leading prompts.
   * it returns the block as a list of string) *)
  let last_read = ref "" in
  let next_block k =
    if !last_read = "" then last_read := input_line c_coq;
    (* skip k prompts *)
    for _i = 1 to k do
      last_read := remove_prompt !last_read;
    done;
    (* read and return the following lines until a prompt is found *)
    let rec read_lines () =
      let s = input_line c_coq in
      if Str.string_match any_prompt s 0 then begin
	last_read := s; []
      end else
	s :: (read_lines ())
    in
    let first = !last_read in first :: (read_lines ())
  in
  (* we are just after \end{coq_...} block *)
  let rec just_after () =
    let s = input_line c_tex in
    if Str.string_match begin_coq_example s 0 then begin
      inside (Str.matched_group 1 s <> "example*")
             (Str.matched_group 1 s <> "example#") 0 false
    end
    else begin
      if !hrule then output_string c_out "\\hrulefill\\\\\n";
      output_string c_out "\\end{flushleft}\n";
      if !small then output_string c_out "\\end{small}\n";
      if Str.string_match begin_coq_eval s 0 then
	eval 0
      else begin
	output_string c_out (s ^ "\n");
	outside ()
      end
    end
  (* we are outside of a \begin{coq_...} ... \end{coq_...} block *)
  and outside () =
    let s = input_line c_tex in
    if Str.string_match begin_coq_example s 0 then begin
      if !small then output_string c_out "\\begin{small}\n";
      output_string c_out "\\begin{flushleft}\n";
      if !hrule then output_string c_out "\\hrulefill\\\\\n";
      inside (Str.matched_group 1 s <> "example*")
             (Str.matched_group 1 s <> "example#") 0 true
    end else if Str.string_match begin_coq_eval s 0 then
      eval 0
    else begin
      output_string c_out (s ^ "\n");
      outside ()
    end
  (* we are inside a \begin{coq_example?} ... \end{coq_example?} block
   * show_answers tells what kind of block it is
   * k is the number of lines read until now *)
  and inside show_answers  show_questions k first_block =
    let s = input_line c_tex in
    if Str.string_match end_coq_example s 0 then begin
      just_after ()
    end else begin
      let prompt = if k = 0 then "Coq < " else "      " in
      if !verbose then Printf.printf "%s%s\n" prompt s;
      if (not first_block) && k=0 then output_string c_out "\\medskip\n";
      if show_questions then encapsule false c_out (prompt ^ s);
      if has_match dot_end_line s then begin
	let bl = next_block (succ k) in
	if !verbose then List.iter print_endline bl;
	if show_answers then print_block c_out bl;
	inside show_answers  show_questions 0 false
      end else
	inside show_answers  show_questions (succ k) first_block
    end
  (* we are inside a \begin{coq_eval} ... \end{coq_eval} block
   * k is the number of lines read until now *)
  and eval k =
    let s = input_line c_tex in
    if Str.string_match end_coq_eval s 0 then
      outside ()
    else begin
      if !verbose then Printf.printf "Coq < %s\n" s;
      if has_match dot_end_line s then
	let bl = next_block (succ k) in
	if !verbose then List.iter print_endline bl;
	eval 0
      else
	eval (succ k)
    end
  in
  try
    let _ = next_block 0 in (* to skip the Coq banner *)
    let _ = next_block 0 in (* to skip the Coq answer to Set Printing Width *)
    outside ()
  with End_of_file -> begin
    close_in c_tex;
    close_in c_coq;
    close_out c_out
  end

(* Process of one TeX file *)

let rm f = try Sys.remove f with any -> ()

let one_file texfile =
  let inputv = Filename.temp_file "coq_tex" ".v" in
  let coq_output = Filename.temp_file "coq_tex" ".coq_output"in
  let result =
    if !output_specified then
      !output
    else if Filename.check_suffix texfile ".tex" then
      (Filename.chop_suffix texfile ".tex") ^ ".v.tex"
    else
      texfile ^ ".v.tex"
  in
  try
    (* 1. extract Coq phrases *)
    extract texfile inputv;
    (* 2. run Coq on input *)
    let _ = Sys.command (Printf.sprintf "%s < %s > %s 2>&1" !image inputv
			   coq_output)
    in
    (* 3. insert Coq output into original file *)
    insert texfile coq_output result;
    (* 4. clean up *)
    rm inputv; rm coq_output
  with reraise -> begin
    rm inputv; rm coq_output;
    raise reraise
  end

(* Parsing of the command line, check of the Coq command and process
 * of all the files in the command line, one by one *)

let files = ref []

let parse_cl () =
  Arg.parse
      [ "-o", Arg.String (fun s -> output_specified := true; output := s),
	"output-file    Specifiy the resulting LaTeX file";
	"-n", Arg.Int (fun n -> linelen := n),
	"line-width     Set the line width";
	"-image", Arg.String (fun s -> image := s),
	"coq-image  Use coq-image as Coq command";
	"-w", Arg.Set cut_at_blanks,
	"               Try to cut lines at blanks";
	"-v", Arg.Set verbose,
	"               Verbose mode (show Coq answers on stdout)";
	"-sl", Arg.Set slanted,
	"              Coq answers in slanted font (only with LaTeX2e)";
	"-hrule", Arg.Set hrule,
	"           Coq parts are written between 2 horizontal lines";
	"-small", Arg.Set small,
	"           Coq parts are written in small font";
	"-boot", Arg.Set boot,
	"           Launch coqtop with the -boot option"
      ]
      (fun s -> files := s :: !files)
      "coq-tex [options] file ..."

let find_coqtop () =
  let prog = Sys.executable_name in
  try
    let size = String.length prog in
    let i = Str.search_backward (Str.regexp_string "coq-tex") prog (size-7) in
    (String.sub prog 0 i)^"coqtop"^(String.sub prog (i+7) (size-i-7))
  with Not_found -> begin
    Printf.printf "Warning: preprocessing with default image \"coqtop\"\n";
    "coqtop"
  end

let main () =
  parse_cl ();
  if !image = "" then image := Filename.quote (find_coqtop ());
  if !boot then image := !image ^ " -boot";
  if Sys.command (!image ^ " -batch -silent") <> 0 then begin
    Printf.printf "Error: ";
    let _ = Sys.command (!image ^ " -batch") in
    exit 1
  end else begin
    Printf.printf "Your version of coqtop seems OK\n";
    flush stdout
  end;
  List.iter one_file (List.rev !files)

let _ = Printexc.catch main ()
