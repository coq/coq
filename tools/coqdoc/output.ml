(* -*- compile-command: "make -C ../.. bin/coqdoc" -*- *)
(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

open Cdglobals
open Index

(*s Low level output *)

let output_char c = Pervasives.output_char !out_channel c

let output_string s = Pervasives.output_string !out_channel s

let printf s = Printf.fprintf !out_channel s

let sprintf = Printf.sprintf


(*s Coq keywords *)

let build_table l = 
  let h = Hashtbl.create 101 in
  List.iter (fun key ->Hashtbl.add h  key ()) l;
  function s -> try Hashtbl.find h s; true with Not_found -> false

let is_keyword = 
  build_table
    [ "AddPath"; "Axiom"; "Abort"; "Chapter"; "Check"; "Coercion"; "CoFixpoint";
      "CoInductive"; "Corollary"; "Defined"; "Definition"; "End"; "Eval"; "Example"; 
      "Export"; "Fact"; "Fix"; "Fixpoint"; "Global"; "Grammar"; "Goal"; "Hint";
      "Hypothesis"; "Hypotheses"; 
      "Resolve"; "Unfold"; "Immediate"; "Extern"; "Implicit"; "Import"; "Inductive"; 
      "Infix"; "Lemma"; "Let"; "Load"; "Local"; "Ltac"; 
      "Module"; "Module Type"; "Declare Module"; "Include";
      "Mutual"; "Parameter"; "Parameters"; "Print"; "Proof"; "Proof with"; "Qed";
      "Record"; "Recursive"; "Remark"; "Require"; "Save"; "Scheme";
      "Induction"; "for"; "Sort"; "Section"; "Show"; "Structure"; "Syntactic"; "Syntax"; "Tactic"; "Theorem"; 
      "Set"; "Types"; "Undo"; "Unset"; "Variable"; "Variables"; "Context";
      "Notation"; "Reserved Notation"; "Tactic Notation";
      "Delimit"; "Bind"; "Open"; "Scope"; 
      "Boxed"; "Unboxed"; "Inline";
      "Implicit Arguments"; "Add"; "Strict";
      "Typeclasses"; "Instance"; "Global Instance"; "Class"; "Instantiation";
      "subgoal";
      (* Program *)
      "Program Definition"; "Program Example"; "Program Fixpoint"; "Program Lemma";
      "Obligation"; "Obligations"; "Solve"; "using"; "Next Obligation"; "Next";
      "Program Instance"; "Equations"; "Equations_nocomp";
      (*i (* coq terms *) *)
      "forall"; "match"; "as"; "in"; "return"; "with"; "end"; "let"; "dest"; "fun"; 
      "if"; "then"; "else"; "Prop"; "Set"; "Type"; ":="; "where"; "struct"; "wf"; "measure";
      (* Ltac *)
      "before"; "after"
       ]

let is_tactic = 
  build_table
    [ "intro"; "intros"; "apply"; "rewrite"; "refine"; "case"; "clear"; "injection";
      "elimtype"; "progress"; "setoid_rewrite";
      "destruct"; "destruction"; "destruct_call"; "dependent"; "elim"; "extensionality";
      "f_equal"; "generalize"; "generalize_eqs"; "generalize_eqs_vars"; "induction"; "rename"; "move"; "omega";
      "set"; "assert";
      "cut"; "assumption"; "exact"; "split"; "subst"; "try"; "discriminate";
      "simpl"; "unfold"; "red"; "compute"; "at"; "in"; "by";
      "reflexivity"; "symmetry"; "transitivity";
      "replace"; "setoid_replace"; "inversion"; "inversion_clear";
      "pattern"; "intuition"; "congruence"; "fail"; "fresh";
      "trivial"; "exact"; "tauto"; "firstorder"; "ring";
      "clapply"; "program_simpl"; "program_simplify"; "eapply"; "auto"; "eauto" ]

(*s Current Coq module *)

let current_module = ref ""

let set_module m = current_module := m; page_title := m

(*s Common to both LaTeX and HTML *)

let item_level = ref 0

(*s Customized pretty-print *)

let token_pp = Hashtbl.create 97

let add_printing_token = Hashtbl.replace token_pp

let find_printing_token tok = 
  try Hashtbl.find token_pp tok with Not_found -> None, None

let remove_printing_token = Hashtbl.remove token_pp

(* predefined pretty-prints *)
let initialize () = 
  let if_utf8 = if !Cdglobals.utf8 then fun x -> Some x else fun _ -> None in
    List.iter 
      (fun (s,l,l') -> Hashtbl.add token_pp s (Some l, l'))
      [ "*" ,  "\\ensuremath{\\times}", if_utf8 "×";
	"|", "\\ensuremath{|}", None;
	"->",  "\\ensuremath{\\rightarrow}", if_utf8 "→";
	"->~",  "\\ensuremath{\\rightarrow\\lnot}", None;
	"->~~",  "\\ensuremath{\\rightarrow\\lnot\\lnot}", None;
	"<-",  "\\ensuremath{\\leftarrow}", None;
	"<->", "\\ensuremath{\\leftrightarrow}", if_utf8 "↔";
	"=>",  "\\ensuremath{\\Rightarrow}", if_utf8 "⇒";
	"<=",  "\\ensuremath{\\le}", if_utf8 "≤";
	">=",  "\\ensuremath{\\ge}", if_utf8 "≥";
	"<>",  "\\ensuremath{\\not=}", if_utf8 "≠";
	"~",   "\\ensuremath{\\lnot}", if_utf8 "¬";
	"/\\", "\\ensuremath{\\land}", if_utf8 "∧";
	"\\/", "\\ensuremath{\\lor}", if_utf8 "∨";
	"|-",  "\\ensuremath{\\vdash}", None;
	"forall", "\\ensuremath{\\forall}", if_utf8 "∀";
	"exists", "\\ensuremath{\\exists}", if_utf8 "∃";
	"Π", "\\ensuremath{\\Pi}", if_utf8 "Π";
	"λ", "\\ensuremath{\\lambda}", if_utf8 "λ"
	(* "fun", "\\ensuremath{\\lambda}" ? *)
      ]

(*s Table of contents *)

type toc_entry = 
  | Toc_library of string
  | Toc_section of int * (unit -> unit) * string

let (toc_q : toc_entry Queue.t) = Queue.create ()

let add_toc_entry e = Queue.add e toc_q

let new_label = let r = ref 0 in fun () -> incr r; "lab" ^ string_of_int !r

(*s LaTeX output *)

module Latex = struct

  (*s Latex preamble *)

  let (preamble : string Queue.t) = Queue.create ()

  let push_in_preamble s = Queue.add s preamble

  let header () =
    if !header_trailer then begin
      printf "\\documentclass[12pt]{report}\n";
      if !inputenc != "" then printf "\\usepackage[%s]{inputenc}\n" !inputenc;
      printf "\\usepackage[T1]{fontenc}\n";
      printf "\\usepackage{fullpage}\n";
      printf "\\usepackage{coqdoc}\n";
      Queue.iter (fun s -> printf "%s\n" s) preamble;
      printf "\\begin{document}\n"
    end;
    output_string 
      "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%\n";
    output_string
      "%% This file has been automatically generated with the command\n";
    output_string "%% ";
    Array.iter (fun s -> printf "%s " s) Sys.argv;
    printf "\n";
    output_string
      "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%\n"

  let trailer () =
    if !header_trailer then begin
      printf "\\end{document}\n"
    end

  let char c = match c with
    | '\\' -> 
	printf "\\symbol{92}"
    | '$' | '#' | '%' | '&' | '{' | '}' | '_' -> 
	output_char '\\'; output_char c
    | '^' | '~' -> 
	output_char '\\'; output_char c; printf "{}"
    | _ -> 
	output_char c

  let label_char c = match c with
    | '\\' | '$' | '#' | '%' | '&' | '{' | '}' | '_'
    | '^' | '~' -> ()
    | _ -> 
	output_char c

  let latex_char = output_char
  let latex_string = output_string

  let html_char _ = ()
  let html_string _ = ()

  let raw_ident s =
    for i = 0 to String.length s - 1 do char s.[i] done

  let label_ident s =
    for i = 0 to String.length s - 1 do label_char s.[i] done

  let start_module () = 
    if not !short then begin
      printf "\\coqlibrary{"; 
      label_ident !current_module; 
      printf "}{";
      raw_ident !current_module; 
      printf "}\n\n"
    end

  let start_latex_math () = output_char '$'

  let stop_latex_math () = output_char '$'

  let start_verbatim () = printf "\\begin{verbatim}"

  let stop_verbatim () = printf "\\end{verbatim}\n"

  let indentation n = 
    if n == 0 then 
      printf "\\coqdocnoindent\n"
    else
      let space = 0.5 *. (float n) in
      printf "\\coqdocindent{%2.2fem}\n" space

  let with_latex_printing f tok =
    try 
      (match Hashtbl.find token_pp tok with
	 | Some s, _ -> output_string s
	 | _ -> f tok)
    with Not_found -> 
      f tok

  let module_ref m s = 
    printf "\\moduleid{%s}{" m; raw_ident s; printf "}"
      (*i
    match find_module m with
    | Local ->
	printf "<a href=\"%s.html\">" m; raw_ident s; printf "</a>"
    | Coqlib when !externals ->
	let m = Filename.concat !coqlib m in
	printf "<a href=\"%s.html\">" m; raw_ident s; printf "</a>"
    | Coqlib | Unknown ->
	raw_ident s
    i*)

  let ident_ref m fid typ s =
    let id = if fid <> "" then (m ^ "." ^ fid) else m in
    match find_module m with
      | Local ->
	  printf "\\coq%sref{" (type_name typ); label_ident id; printf "}{"; raw_ident s; printf "}"
      | Coqlib when !externals ->
	  let _m = Filename.concat !coqlib m in
	    printf "\\coq%sref{" (type_name typ); label_ident id; printf "}{"; raw_ident s; printf "}"
      | Coqlib | Unknown ->
	  printf "\\coq%sref{" (type_name typ); label_ident id; printf "}{"; raw_ident s; printf "}"

  let defref m id ty s =
    printf "\\coq%s{" (type_name ty); label_ident (m ^ "." ^ id); printf "}{"; raw_ident s; printf "}"

  let reference s = function
    | Def (fullid,typ) -> 
	defref !current_module fullid typ s
    | Mod (m,s') when s = s' ->
	module_ref m s
    | Ref (m,fullid,typ) -> 
	ident_ref m fullid typ s
    | Mod _ ->
	printf "\\coqdocvar{"; raw_ident s; printf "}"

  let ident s loc = 
    if is_keyword s then begin
      printf "\\coqdockw{"; raw_ident s; printf "}"
    end else begin
      begin
	try
	  reference s (Index.find !current_module loc)
	with Not_found ->
	  if is_tactic s then begin
	    printf "\\coqdoctac{"; raw_ident s; printf "}"
	  end else begin
	    if !Cdglobals.interpolate then
	      try reference s (Index.find_string !current_module s)
	      with _ -> printf "\\coqdocvar{"; raw_ident s; printf "}"
	    else (printf "\\coqdocvar{"; raw_ident s; printf "}")
	  end
      end
    end

  let ident s l = with_latex_printing (fun s -> ident s l) s

  let symbol = with_latex_printing raw_ident

  let rec reach_item_level n = 
    if !item_level < n then begin
      printf "\n\\begin{itemize}\n\\item "; incr item_level;
      reach_item_level n
    end else if !item_level > n then begin
      printf "\n\\end{itemize}\n"; decr item_level;
      reach_item_level n
    end

  let item n =
    let old_level = !item_level in
    reach_item_level n;
    if n <= old_level then printf "\n\\item "

  let stop_item () = reach_item_level 0

  let start_doc () = printf "\\begin{coqdocdoc}\n"

  let end_doc () = stop_item (); printf "\\end{coqdocdoc}\n"

  let start_coq () = printf "\\begin{coqdoccode}\n"

  let end_coq () = printf "\\end{coqdoccode}\n"

  let start_code () = end_doc (); start_coq ()

  let end_code () = end_coq (); start_doc ()

  let section_kind = function
    | 1 -> "\\section{"
    | 2 -> "\\subsection{"
    | 3 -> "\\subsubsection{"
    | 4 -> "\\paragraph{"
    | _ -> assert false

  let section lev f =
    stop_item ();
    output_string (section_kind lev);
    f ();
    printf "}\n\n"

  let rule () =
    printf "\\par\n\\noindent\\hrulefill\\par\n\\noindent{}"

  let paragraph () = stop_item (); printf "\n\n"

  let line_break () = printf "\\coqdoceol\n"

  let empty_line_of_code () = printf "\\coqdocemptyline\n"

  let start_inline_coq () = ()

  let end_inline_coq () = ()

  let make_multi_index () = ()

  let make_index () = ()

  let make_toc () = printf "\\tableofcontents\n"

end


(*s HTML output *)

module Html = struct

  let header () =
    if !header_trailer then
      if !header_file_spec then
	let cin = Pervasives.open_in !header_file in
	  try 
	    while true do 
	      let s = Pervasives.input_line cin in 
		printf "%s\n" s
	    done
	  with End_of_file -> Pervasives.close_in cin
      else
	begin
	  printf "<!DOCTYPE html PUBLIC \"-//W3C//DTD XHTML 1.0 Strict//EN\"\n";
	  printf "\"http://www.w3.org/TR/xhtml1/DTD/xhtml1-strict.dtd\">\n";
	  printf "<html xmlns=\"http://www.w3.org/1999/xhtml\">\n<head>\n";
	  printf "<meta http-equiv=\"Content-Type\" content=\"text/html; charset=%s\"/>\n" !charset;
	  printf "<link href=\"coqdoc.css\" rel=\"stylesheet\" type=\"text/css\"/>\n";
	  printf "<title>%s</title>\n</head>\n\n" !page_title;
	  printf "<body>\n\n<div id=\"page\">\n\n<div id=\"header\">\n</div>\n\n";
	  printf "<div id=\"main\">\n\n"
	end

  let self = "http://coq.inria.fr"

  let trailer () =
    if !index && !current_module <> "Index" then 
      printf "</div>\n\n<div id=\"footer\">\n<hr/><a href=\"index.html\">Index</a>";
    if !header_trailer then 
      if !footer_file_spec then
	let cin = Pervasives.open_in !footer_file in
	  try 
	    while true do 
	      let s = Pervasives.input_line cin in 
		printf "%s\n" s
	    done
	  with End_of_file -> Pervasives.close_in cin
      else
	begin
	  printf "<hr/>This page has been generated by ";
	  printf "<a href=\"%s\">coqdoc</a>\n" self;
	  printf "</div>\n\n</div>\n\n</body>\n</html>"
	end

  let start_module () = 
    if not !short then begin
      add_toc_entry (Toc_library !current_module);
      printf "<h1 class=\"libtitle\">Library %s</h1>\n\n" !current_module
    end

  let indentation n = for i = 1 to n do printf "&nbsp;" done

  let line_break () = printf "<br/>\n"

  let empty_line_of_code () = 
    printf "\n<br/>\n"

  let char = function
    | '<' -> printf "&lt;"
    | '>' -> printf "&gt;"
    | '&' -> printf "&amp;"
    | c -> output_char c

  let raw_ident s = for i = 0 to String.length s - 1 do char s.[i] done

  let latex_char _ = ()
  let latex_string _ = ()

  let html_char = output_char
  let html_string = output_string

  let start_latex_math () = ()
  let stop_latex_math () = ()

  let start_verbatim () = printf "<pre>"
  let stop_verbatim () = printf "</pre>\n"

  let module_ref m s = 
    match find_module m with
      | Local ->
	  printf "<a class=\"modref\" href=\"%s.html\">" m; raw_ident s; printf "</a>"
      | Coqlib when !externals ->
	  let m = Filename.concat !coqlib m in
	    printf "<a class=\"modref\" href=\"%s.html\">" m; raw_ident s; printf "</a>"
      | Coqlib | Unknown ->
	  raw_ident s

  let ident_ref m fid typ s =
    match find_module m with
    | Local ->
	printf "<a class=\"idref\" href=\"%s.html#%s\">" m fid; 
	printf "<div class=\"id\" type=\"%s\">" typ; raw_ident s; printf "</div></a>"
    | Coqlib when !externals ->
	let m = Filename.concat !coqlib m in
	  printf "<a class=\"idref\" href=\"%s.html#%s\">" m fid;
	  printf "<div class=\"id\" type=\"%s\">" typ; raw_ident s; printf "</div></a>"
    | Coqlib | Unknown ->
	printf "<div class=\"id\" type=\"%s\">" typ; raw_ident s; printf "</div>"
	  
  let ident s loc = 
    if is_keyword s then begin
      printf "<div class=\"id\" type=\"keyword\">"; 
      raw_ident s; 
      printf "</div>"
    end else 
      begin
	try
	  (match Index.find !current_module loc with
	     | Def (fullid,ty) -> 
		 printf "<a name=\"%s\">" fullid; 
		 printf "<div class=\"id\" type=\"%s\">" (type_name ty); raw_ident s; printf "</div></a>"
             | Mod (m,s') when s = s' ->
		 module_ref m s
	     | Ref (m,fullid,ty) -> 
		 ident_ref m fullid (type_name ty) s
	     | Mod _ ->
		 printf "<div class=\"id\" type=\"mod\">"; raw_ident s ; printf "</div>")
	with Not_found ->
	  if is_tactic s then
	    (printf "<div class=\"id\" type=\"tactic\">"; raw_ident s; printf "</div>")
	  else
	    (printf "<div class=\"id\" type=\"var\">"; raw_ident s ; printf "</div>")
      end

  let with_html_printing f tok =
    try 
      (match Hashtbl.find token_pp tok with
	 | _, Some s -> output_string s
	 | _ -> f tok)
    with Not_found -> 
      f tok

  let ident s l = with_html_printing (fun s -> ident s l) s

  let symbol = with_html_printing raw_ident

  let rec reach_item_level n = 
    if !item_level < n then begin
      printf "\n<ul>\n<li>"; incr item_level;
      reach_item_level n
    end else if !item_level > n then begin
      printf "\n</li>\n</ul>\n"; decr item_level;
      reach_item_level n
    end

  let item n =
    let old_level = !item_level in
    reach_item_level n;
    if n <= old_level then printf "\n</li>\n<li>"

  let stop_item () = reach_item_level 0

  let start_coq () = if not !raw_comments then printf "<code>\n"

  let end_coq () = if not !raw_comments then printf "</code>\n"

  let start_doc () = 
    if not !raw_comments then
      printf "\n<div class=\"doc\">\n"

  let end_doc () =
    stop_item (); 
    if not !raw_comments then printf "\n</div>\n"

  let start_code () = end_doc (); start_coq ()

  let end_code () = end_coq (); start_doc ()

  let start_inline_coq () = printf "<code>"

  let end_inline_coq () = printf "</code>"

  let paragraph () = stop_item (); printf "\n<br/><br/>\n"

  let section lev f =
    let lab = new_label () in
    let r = sprintf "%s.html#%s" !current_module lab in
    add_toc_entry (Toc_section (lev, f, r));
    stop_item ();
    printf "<a name=\"%s\"></a><h%d class=\"section\">" lab lev;
    f ();
    printf "</h%d>\n" lev

  let rule () = printf "<hr/>\n"

  (* make a HTML index from a list of triples (name,text,link) *)
  let index_ref i c =
    let idxc = sprintf "%s_%c" i.idx_name c in
    if !multi_index then "index_" ^ idxc ^ ".html" else "index.html#" ^ idxc

  let letter_index category idx (c,l) =
    if l <> [] then begin
      let cat = if category && idx <> "global" then "(" ^ idx ^ ")" else "" in
      printf "<a name=\"%s_%c\"></a><h2>%c %s</h2>\n" idx c c cat;
      List.iter 
	(fun (id,(text,link)) -> 
	   printf "<a href=\"%s\">%s</a> %s<br/>\n" link id text) l;
      printf "<br/><br/>"
    end
		
  let all_letters i = List.iter (letter_index false i.idx_name) i.idx_entries

  (* Construction d'une liste des index (1 index global, puis 1
     index par catégorie) *)
  let format_global_index =
    Index.map 
      (fun s (m,t) -> 
	 if t = Library then 
	   "[library]", m ^ ".html"
	 else
	   sprintf "[%s, in <a href=\"%s.html\">%s</a>]" (type_name t) m m ,
	 sprintf "%s.html#%s" m s)

  let format_bytype_index = function
    | Library, idx ->
	Index.map (fun id m -> "", m ^ ".html") idx
    | (t,idx) ->
	Index.map 
	  (fun s m -> 
	     let text = sprintf "[in <a href=\"%s.html\">%s</a>]" m m in
	       (text, sprintf "%s.html#%s" m s)) idx

  (* Impression de la table d'index *)
  let print_index_table_item i =
    printf "<tr>\n<td>%s Index</td>\n" (String.capitalize i.idx_name);
    List.iter 
      (fun (c,l) -> 
	 if l <> [] then
	   printf "<td><a href=\"%s\">%c</a></td>\n" (index_ref i c) c
	 else
	   printf "<td>%c</td>\n" c)
      i.idx_entries;
    let n = i.idx_size in
      printf "<td>(%d %s)</td>\n" n (if n > 1 then "entries" else "entry");
      printf "</tr>\n"

  let print_index_table idxl = 
    printf "<table>\n";
    List.iter print_index_table_item idxl;
    printf "</table>\n"
	
  let make_one_multi_index prt_tbl i =
    (* Attn: make_one_multi_index créé un nouveau fichier... *)
    let idx = i.idx_name in
    let one_letter ((c,l) as cl) =
      open_out_file (sprintf "index_%s_%c.html" idx c);
      if (!header_trailer) then header ();
      prt_tbl (); printf "<hr/>";
      letter_index true idx cl;
      if List.length l > 30 then begin printf "<hr/>"; prt_tbl () end;
      if (!header_trailer) then trailer ();
      close_out_file ()
    in
      List.iter one_letter i.idx_entries

  let make_multi_index () = 
    let all_index = 
      let glob,bt = Index.all_entries () in
	(format_global_index glob) ::
	  (List.map format_bytype_index bt) in
    let print_table () = print_index_table all_index in
      List.iter (make_one_multi_index print_table) all_index
	
  let make_index () =
    let all_index = 
      let glob,bt = Index.all_entries () in
	(format_global_index glob) ::
	  (List.map format_bytype_index bt) in
    let print_table () = print_index_table all_index in
    let print_one_index i =
      if i.idx_size > 0 then begin
	printf "<hr/>\n<h1>%s Index</h1>\n" (String.capitalize i.idx_name);
	all_letters i
      end
    in
      current_module := "Index";
      if !title <> "" then printf "<h1>%s</h1>\n" !title;
      print_table ();
      if not (!multi_index) then 
	begin
	  List.iter print_one_index all_index;
	  printf "<hr/>"; print_table ()
	end
	    
  let make_toc () = 
    let make_toc_entry = function
      | Toc_library m -> 
	  stop_item ();
	  printf "<a href=\"%s.html\"><h2>Library %s</h2></a>\n" m m
      | Toc_section (n, f, r) ->
	  item n; 
	  printf "<a href=\"%s\">" r; f (); printf "</a>\n"
    in
      Queue.iter make_toc_entry toc_q;
      stop_item ();

end


(*s TeXmacs-aware output *)

module TeXmacs = struct

  (*s Latex preamble *)

  let in_doc = ref false

  let (preamble : string Queue.t) = 
    in_doc := false; Queue.create ()

  let push_in_preamble s = Queue.add s preamble

  let header () =
    output_string 
      "(*i This file has been automatically generated with the command  \n";
    output_string 
      "    "; Array.iter (fun s -> printf "%s " s) Sys.argv; printf " *)\n"

  let trailer () = ()

  let char_true c = match c with
    | '\\' -> printf "\\\\"
    | '<' -> printf "\\<"
    | '|' -> printf "\\|"
    | '>' -> printf "\\>"
    | _ -> output_char c

  let char c = if !in_doc then char_true c else output_char c

  let latex_char = char_true
  let latex_string = String.iter latex_char

  let html_char _ = ()
  let html_string _ = ()

  let raw_ident s =
    for i = 0 to String.length s - 1 do char s.[i] done

  let start_module () = ()

  let start_latex_math () = printf "<with|mode|math|"

  let stop_latex_math () = output_char '>'

  let start_verbatim () = in_doc := true; printf "<\\verbatim>"

  let stop_verbatim () = in_doc := false; printf "</verbatim>"

  let indentation n = ()

  let ident_true s = 
    if is_keyword s then begin
      printf "<kw|"; raw_ident s; printf ">"
    end else begin
      raw_ident s
    end

  let ident s _ = if !in_doc then ident_true s else raw_ident s
 
  let symbol_true s = 
    let ensuremath x = printf "<with|mode|math|\\<%s\\>>" x in
      match s with
	| "*"  -> ensuremath "times"
	| "->" -> ensuremath "rightarrow"
	| "<-" -> ensuremath "leftarrow"
	| "<->" ->ensuremath "leftrightarrow"
	| "=>" -> ensuremath "Rightarrow"
	| "<=" -> ensuremath "le"
	| ">=" -> ensuremath "ge"
	| "<>" -> ensuremath "noteq"
	| "~" ->  ensuremath "lnot"
	| "/\\" -> ensuremath "land"
	| "\\/" -> ensuremath "lor"
	| "|-" -> ensuremath "vdash"
	| s    -> raw_ident s

  let symbol s = if !in_doc then symbol_true s else raw_ident s

  let rec reach_item_level n = 
    if !item_level < n then begin
      printf "\n<\\itemize>\n<item>"; incr item_level;
      reach_item_level n
    end else if !item_level > n then begin
      printf "\n</itemize>"; decr item_level;
      reach_item_level n
    end

  let item n =
    let old_level = !item_level in
    reach_item_level n;
    if n <= old_level then printf "\n\n<item>"

  let stop_item () = reach_item_level 0

  let start_doc () = in_doc := true; printf "(** texmacs: "

  let end_doc () = stop_item (); in_doc := false; printf " *)"

  let start_coq () = ()

  let end_coq () = ()

  let start_code () = in_doc := true; printf "<\\code>\n"
  let end_code () = in_doc := false; printf "\n</code>"

  let section_kind = function
    | 1 -> "section"
    | 2 -> "subsection"
    | 3 -> "subsubsection"
    | 4 -> "paragraph"
    | _ -> assert false

  let section lev f =
    stop_item ();
    printf "<"; output_string (section_kind lev); printf "|"; 
    f (); printf ">\n\n"

  let rule () =
    printf "\n<hrule>\n"

  let paragraph () = stop_item (); printf "\n\n"

  let line_break_true () = printf "<format|line break>"

  let line_break () = printf "\n"

  let empty_line_of_code () = printf "\n"

  let start_inline_coq () = printf "<verbatim|["

  let end_inline_coq () = printf "]>"

  let make_multi_index () = ()

  let make_index () = ()

  let make_toc () = ()

end

(*s Generic output *)

let select f1 f2 f3 x = 
  match !target_language with LaTeX -> f1 x | HTML -> f2 x | TeXmacs -> f3 x

let push_in_preamble = Latex.push_in_preamble

let header = select Latex.header Html.header TeXmacs.header
let trailer = select Latex.trailer Html.trailer TeXmacs.trailer

let start_module = 
  select Latex.start_module Html.start_module TeXmacs.start_module

let start_doc = select Latex.start_doc Html.start_doc TeXmacs.start_doc
let end_doc = select Latex.end_doc Html.end_doc TeXmacs.end_doc

let start_coq = select Latex.start_coq Html.start_coq TeXmacs.start_coq
let end_coq = select Latex.end_coq Html.end_coq TeXmacs.end_coq

let start_code = select Latex.start_code Html.start_code TeXmacs.start_code
let end_code = select Latex.end_code Html.end_code TeXmacs.end_code

let start_inline_coq = 
  select Latex.start_inline_coq Html.start_inline_coq TeXmacs.start_inline_coq
let end_inline_coq = 
  select Latex.end_inline_coq Html.end_inline_coq TeXmacs.end_inline_coq

let indentation = select Latex.indentation Html.indentation TeXmacs.indentation
let paragraph = select Latex.paragraph Html.paragraph TeXmacs.paragraph
let line_break = select Latex.line_break Html.line_break TeXmacs.line_break
let empty_line_of_code = select 
  Latex.empty_line_of_code Html.empty_line_of_code TeXmacs.empty_line_of_code

let section = select Latex.section Html.section TeXmacs.section
let item = select Latex.item Html.item TeXmacs.item
let stop_item = select Latex.stop_item Html.stop_item TeXmacs.stop_item
let rule = select Latex.rule Html.rule TeXmacs.rule

let char = select Latex.char Html.char TeXmacs.char
let ident = select Latex.ident Html.ident TeXmacs.ident
let symbol = select Latex.symbol Html.symbol TeXmacs.symbol

let latex_char = select Latex.latex_char Html.latex_char TeXmacs.latex_char
let latex_string = 
  select Latex.latex_string Html.latex_string TeXmacs.latex_string
let html_char = select Latex.html_char Html.html_char TeXmacs.html_char
let html_string = 
  select Latex.html_string Html.html_string TeXmacs.html_string

let start_latex_math = 
  select Latex.start_latex_math Html.start_latex_math TeXmacs.start_latex_math
let stop_latex_math = 
  select Latex.stop_latex_math Html.stop_latex_math TeXmacs.stop_latex_math

let start_verbatim = 
  select Latex.start_verbatim Html.start_verbatim TeXmacs.start_verbatim
let stop_verbatim = 
  select Latex.stop_verbatim Html.stop_verbatim TeXmacs.stop_verbatim
let verbatim_char = 
  select output_char Html.char TeXmacs.char
let hard_verbatim_char = output_char

let make_multi_index = select Latex.make_multi_index Html.make_multi_index TeXmacs.make_multi_index
let make_index = select Latex.make_index Html.make_index TeXmacs.make_index
let make_toc = select Latex.make_toc Html.make_toc TeXmacs.make_toc
