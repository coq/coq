(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Cdglobals
open Index
open Output

open Format

(* Function to Print index entries *)
let pp_idxo fmt idx = match idx with
  (* refs:  Index.index_entry: the index type of the token (if any) *)
  | Some refs -> fprintf fmt ""
  | None      -> fprintf fmt ""

module Debug : S = struct

  let oc = ref (formatter_of_out_channel stdout)

  let printf        s = fprintf !oc s
  let output_char   c = printf "%c" c
  let output_string s = printf "%s" s

  let cur_mod = ref ""

  let output_sublexer_string esc sym idx s =
    let s_esc = if esc then "e" else "" in
    let s_sym = if esc then "S" else "" in
    let s_tot = if esc || sym then "<" ^ s_esc ^ s_sym ^ ">" else "" in
    fprintf !oc "%s%s" s_tot s

  let appendix ~toc ~index ~split_index ~standalone =
    printf "#appendix [toc: %B|idx: %B|splt: %B|std: %B]@\n"
      toc index split_index standalone

  let push_in_preamble s = printf "#preamble: %s@\n" s

  let support_files = []

  let start_file out ~toc ~index ~split_index ~standalone =
    oc := formatter_of_out_channel out;
    Tokens.token_tree := ref Tokens.empty_ttree;
    Tokens.outfun     := output_sublexer_string;
    printf "#start_file [toc: %B|idx: %B|splt: %B|std: %B]@\n"
      toc index split_index standalone

  let end_file () =
    printf "#end_file@\n%!"

  let start_module coq_mod =
    cur_mod := coq_mod;
    printf "#start_module: %s/%s@\n" !lib_name coq_mod

  let indentation n = for _i = 1 to n do printf "␣" done

  let line_break         () = printf "¶@\n"
  let empty_line_of_code () = printf "⏎@\n"

  let nbsp () = printf "<␣>"

  let char                   = output_char
  let verbatim_char inline c = printf "`%c`" c
  let hard_verbatim_char     = output_char

  let latex_char   s = printf "[!%c]" s
  let latex_string s = printf "[\\%s]" s

  let html_char   c = printf "<h>%c" c
  let html_string s = printf "<h>%s" s

  let start_latex_math () = printf "#begin_math@\n"
  let stop_latex_math  () = printf "#end_math@\n"

  let start_quote () = printf "#start_quote@\n"
  let stop_quote  () = printf "#stop_quote@\n"

  let start_verbatim inline =
    if inline then printf "<tt>"
    else printf "<pre>"

  let stop_verbatim inline =
    if inline then printf "</tt>"
    else printf "</pre>\n"

  let url addr name =
    printf "<a href=\"%s\">%s</a>" addr
      (match name with
       | Some n -> n
       | None -> addr)

  let sublexer c loc =
    let tag = try Some (Index.find !cur_mod loc) with Not_found -> None
    in Tokens.output_tagged_symbol_char tag c

  let sublexer_in_doc c = Tokens.output_tagged_symbol_char None c

  let keyword s loc = printf "<k>%s" s
  let ident   s loc = printf "<i>%s" s
  let proofbox ()   = printf "#proofbox "

  let reach_item_level n = printf "#reach-item-level: %d@\n" n

  let item n       = printf "#start-item: %d@\n" n
  let stop_item () = printf "#stop-item@\n"

  let start_coq () = printf "#start-coq@\n"
  let end_coq   () = printf "#end-coq@\n"

  let start_doc () = printf "#start-doc@\n"
  let end_doc   () = printf "#end-doc@\n"

  let start_emph () = printf "<em>"
  let stop_emph  () = printf "</em>"

  let start_comment () = printf "#start_comment@\n"
  let end_comment   () = printf "#end_comment@\n"

  let start_code () = printf "#start_code@\n"
  let end_code   () = printf "#end_code@\n"

  let start_inline_coq () = printf "#start-inline-coq@\n"
  let end_inline_coq   () = printf "#end-inline-coq@\n"

  let start_inline_coq_block () = printf "#start-inline-coq-block@\n"
  let end_inline_coq_block   () = printf "#end-inline-coq-block@\n"

  let paragraph () = printf "#par@\n"

  let inf_rule _ _ _ = printf "#inf_rule @\n"

  let section lev f =
    printf "#start-sec-%d: " lev;
    f ();
    printf "#end-sec-%d@\n" lev

  let rule () = printf "<hr/>\n"

end
