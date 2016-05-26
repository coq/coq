(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Cdglobals
open Output
open Format

let item_level = ref 0

module Constants = struct

  let coqdoc_locate f = List.fold_left Filename.concat !coqlib_path ["tools"; "coqdoc"; f]

  let hd_file = coqdoc_locate "jscoq_header.html"
  let ft_file = coqdoc_locate "jscoq_footer.html"

  let pp_file fmt file =
    let in_f = open_in file   in
    try while true do fprintf fmt "%s\n" (input_line in_f) done
    with End_of_file -> close_in in_f

  let header fmt =
    pp_file fmt (if !header_file_spec then !header_file else hd_file)
  let footer fmt =
    pp_file fmt (if !footer_file_spec then !footer_file else ft_file)

end

module JsCoq : S = struct

  let oc = ref (formatter_of_out_channel stdout)

  let printf        s = fprintf !oc s
  let output_char   c = printf "%c" c
  let output_string s = printf "%s" s

  let cur_mod = ref ""

  (* Dummy functions *)
  let push_in_preamble _ = ()
  let appendix ~toc ~index ~split_index ~standalone = ()

  (* This could be fixed *)
  let support_files      = []

  (*  *)
  let output_sublexer_string _esc _sym _idx s = output_string s

  (* Print the header *)
  let start_file out ~toc ~index ~split_index ~standalone =
    oc := out;
    Tokens.token_tree := ref Tokens.empty_ttree;
    Tokens.outfun     := output_sublexer_string;
    printf "@[";
    Constants.header !oc

  (* Number of Coq textareas *)
  let coq_ids = ref 0

  let pp_coq_id fmt coq_id =
    fprintf fmt "'coq-ta-%d'" coq_id

  (* Don't use it with m > n XD *)
  let rec iota m n = if n = 0 then [] else
      (m :: iota (m+1) (n-1))

  let rec pp_list_js pp fmt l = match l with
      []         -> fprintf fmt ""
    | csx :: []  -> fprintf fmt "@[%a@]" pp csx
    | csx :: csl -> fprintf fmt "@[%a@], @;%a" pp csx (pp_list_js pp) csl

  let rec pp_coq_ids fmt n =
    fprintf fmt "[%a]" (pp_list_js pp_coq_id) (iota 1 !coq_ids)

  let gen_coq_ids () =
    fprintf !oc "<script type=\"text/javascript\">@\n var coqdoc_ids = @[<hov>%a@];@\n</script>@\n"
      pp_coq_ids !coq_ids

  let end_file () =
    gen_coq_ids ();
    Constants.footer !oc;
    printf "@]"

  let start_module coq_mod =
    fprintf !oc "@[<hov><h1>%s</h1>@]@\n" coq_mod;
    cur_mod := coq_mod

  let indentation n = for _i = 1 to n do printf " " done

  let line_break         () = printf "\n"
  let empty_line_of_code () = printf "\n"

  let nbsp () = printf " "

  let char                 = output_char
  let verbatim_char inline = output_char
  let hard_verbatim_char   = output_char

  (* Omit the latex things from html *)
  let latex_char   s = ()
  let latex_string s = ()

  let html_char   = output_char
  let html_string = output_string

  let start_latex_math () = printf "$$ "
  let stop_latex_math  () = printf " $$"

  let start_quote () = printf "<quote>"
  let stop_quote  () = printf "</quote>"

  let url addr name =
    printf "<a href=\"%s\">%s</a>" addr
      (match name with
       | Some n -> n
       | None -> addr)

  let sublexer c loc    = Tokens.output_tagged_symbol_char None c
  let sublexer_in_doc c = Tokens.output_tagged_symbol_char None c

  let keyword s _loc = output_string s
  let ident   s _loc = output_string s
  let proofbox ()    = ()

  let item_level = ref 0

  let rec reach_item_level n =
    if !item_level < n then begin
      fprintf !oc "<ul class=\"doclist\">@\n  @[<hov><li>"; incr item_level;
      reach_item_level n
    end else if !item_level > n then begin
      printf "@\n</li>@]@\n</ul>@\n"; decr item_level;
      reach_item_level n
    end

  let item n =
    let old_level = !item_level in
    reach_item_level n;
    if n <= old_level then printf "@\n</li>@]@\n@[<hov><li>"

  let stop_item () = reach_item_level 0

  let new_coq_id () = incr coq_ids; !coq_ids

  let start_coq () = printf "<div><textarea id=%a>@\n" pp_coq_id (new_coq_id ())
  let end_coq   () = printf "</textarea></div>@\n"

  let start_doc () = printf "<div><p>@\n"
  let end_doc   () = printf "</div>@\n"

  let start_emph () = printf "<em>"
  let stop_emph  () = printf "</em>"

  let start_comment () = printf "(*"
  let end_comment   () = printf "*)"

  let start_inline_coq () = printf "<tt>"
  let end_inline_coq   () = printf "</tt>"

  let start_verbatim inline =
    if inline then printf "<tt>"
    else printf "<pre>"

  let stop_verbatim inline =
    if inline then printf "</tt>"
    else printf "</pre>\n"

  let start_inline_coq_block () =
    printf "<pre class=\"inline-coq\" data-lang=\"coq\">\n"

  let end_inline_coq_block   () = printf "</pre>"

  (* XXX: close pars like in XHTML??? *)
  let paragraph () = printf "<p>@\n"

  (* XXX: *)
  let inf_rule _ _ _ = printf "#inf_rule @\n"

  let section lev f =
    printf "<h%d>@\n @[" lev;
    f ();
    printf "@]@\n</h%d>@\n" lev

  let rule () = printf "<hr/>@\n"

end
