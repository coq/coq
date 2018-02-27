(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
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

let any_prompt = Str.regexp "[A-Z0-9a-z_\\$']* < "

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
    (* a dummy command, just in case the last line was a comment *)
    output_string chan_out "Set Printing Width 78.\n";
    close_in chan_in;
    close_out chan_out

(* Second pass: insert the answers of Coq from [coq_output] into the
 * TeX file [texfile]. The result goes in file [result]. *)

let tex_escaped s =
  let delims = Str.regexp "[_{}&%#$\\^~ <>'`]" in
  let adapt_delim = function
    | "{" | "}" | "&" | "%" | "#" | "$" as c -> "\\"^c
    | "_" -> "{\\char`\\_}"
    | "\\" -> "{\\char'134}"
    | "^" -> "{\\char'136}"
    | "~" -> "{\\char'176}"
    | " " -> "~"
    | "<" -> "{<}"
    | ">" -> "{>}"
    | "'" -> "{\\textquotesingle}"
    | "`" -> "\\`{}"
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
  (* read lines until a prompt is found (starting from the second line),
     purge prompts on the first line and return their number *)
  let last_read = ref (input_line c_coq) in
  let read_output () =
    let first = !last_read in
    let nb = ref 0 in
    (* remove the leading prompts *)
    let rec skip_prompts pos =
      if Str.string_match any_prompt first pos then
        let () = incr nb in
        skip_prompts (Str.match_end ())
      else pos in
    let first =
      let start = skip_prompts 0 in
      String.sub first start (String.length first - start) in
    (* read and return the following lines until a prompt is found *)
    let rec read_lines () =
      let s = input_line c_coq in
      if Str.string_match any_prompt s 0 then begin
	last_read := s; []
      end else
	s :: read_lines () in
    (first :: read_lines (), !nb) in
  let unhandled_output = ref None in
  let read_output () =
    match !unhandled_output with
    | Some some -> unhandled_output := None; some
    | None -> read_output () in
  (* we are inside a \begin{coq_...} ... \end{coq_...} block
   * show_... tell what kind of block it is *)
  let rec inside show_answers show_questions not_first discarded =
    let s = input_line c_tex in
    if s = "" then
      inside show_answers show_questions not_first (discarded + 1)
    else if not (Str.string_match end_coq s 0) then begin
      let (bl,n) = read_output () in
      assert (n > discarded);
      let n = n - discarded in
      if not_first then output_string c_out "\\medskip\n";
      if !verbose then Printf.printf "Coq < %s\n" s;
      if show_questions then encapsule false c_out ("Coq < " ^ s);
      let rec read_lines k =
        if k = 0 then []
        else
          let s = input_line c_tex in
          if Str.string_match end_coq s 0 then []
          else s :: read_lines (k - 1) in
      let al = read_lines (n - 1) in
      if !verbose then List.iter (Printf.printf "      %s\n") al;
      if show_questions then
        List.iter (fun s -> encapsule false c_out ("      " ^ s)) al;
      let la = n - 1 - List.length al in
      if la <> 0 then
        (* this happens when the block ends with a comment; the output
           is for the command at the beginning of the next block *)
        unhandled_output := Some (bl, la)
      else begin
        if !verbose then List.iter print_endline bl;
        if show_answers then print_block c_out bl;
        inside show_answers show_questions (show_answers || show_questions) 0
      end
    end else if discarded > 0 then begin
      (* this happens when the block ends with an empty line *)
      let (bl,n) = read_output () in
      assert (n > discarded);
      unhandled_output := Some (bl, n - discarded)
    end in
  (* we are outside of a \begin{coq_...} ... \end{coq_...} block *)
  let rec outside just_after =
    let start_block () =
      if !small then output_string c_out "\\begin{small}\n";
      output_string c_out "\\begin{flushleft}\n";
      if !hrule then output_string c_out "\\hrulefill\\\\\n" in
    let end_block () =
      if !hrule then output_string c_out "\\hrulefill\\\\\n";
      output_string c_out "\\end{flushleft}\n";
      if !small then output_string c_out "\\end{small}\n" in
    let s = input_line c_tex in
    if Str.string_match begin_coq s 0 then begin
      let kind = Str.matched_group 1 s in
      if kind = "eval" then begin
        if just_after then end_block ();
        inside false false false 0;
        outside false
      end else begin
        let show_answers   = kind <> "example*" in
        let show_questions = kind <> "example#" in
        if not just_after then start_block ();
        inside show_answers show_questions just_after 0;
        outside true
      end
    end else begin
      if just_after then end_block ();
      output_string c_out (s ^ "\n");
      outside false
    end in
  try
    let _ = read_output () in (* to skip the Coq banner *)
    let _ = read_output () in (* to skip the Coq answer to Set Printing Width *)
    outside false
  with End_of_file -> begin
    close_in c_tex;
    close_in c_coq;
    close_out c_out
  end

(* Process of one TeX file *)

let rm f = try Sys.remove f with _ -> ()

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
	"output-file    Specify the resulting LaTeX file";
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
	"            Launch coqtop with the -boot option"
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

let _ =
  parse_cl ();
  if !image = "" then image := Filename.quote (find_coqtop ());
  if !boot then image := !image ^ " -boot";
  if Sys.command (!image ^ " -batch -silent") <> 0 then begin
    Printf.printf "Error: ";
    let _ = Sys.command (!image ^ " -batch") in
    exit 1
  end else begin
    (*Printf.printf "Your version of coqtop seems OK\n";*)
    flush stdout
  end;
  List.iter one_file (List.rev !files)
