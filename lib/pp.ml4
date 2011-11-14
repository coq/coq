(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp_control

(* This should not be used outside of this file. Use
   Flags.print_emacs instead. This one is updated when reading
   command line options. This was the only way to make [Pp] depend on
   an option without creating a circularity: [Flags. -> [Util] ->
   [Pp] -> [Flags. *)
let print_emacs = ref false
let make_pp_emacs() = print_emacs:=true
let make_pp_nonemacs() = print_emacs:=false

(* The different kinds of blocks are:
   \begin{description}
   \item[hbox:] Horizontal block no line breaking;
   \item[vbox:] Vertical block each break leads to a new line;
   \item[hvbox:] Horizontal-vertical block: same as vbox, except if
      this block is small enough to fit on a single line
   \item[hovbox:] Horizontal or Vertical block: breaks lead to new line
      only when necessary to print the content of the block
   \item[tbox:] Tabulation block: go to tabulation marks and no line breaking
      (except if no mark yet on the reste of the line)
   \end{description}
 *)

let comments = ref []

let rec split_com comacc acc pos = function
    [] -> comments := List.rev acc; comacc
  | ((b,e),c as com)::coms ->
      (* Take all comments that terminates before pos, or begin exactly
         at pos (used to print comments attached after an expression) *)
      if e<=pos || pos=b then split_com (c::comacc) acc pos coms
      else  split_com comacc (com::acc) pos coms


type block_type =
  | Pp_hbox of int
  | Pp_vbox of int
  | Pp_hvbox of int
  | Pp_hovbox of int
  | Pp_tbox

type 'a ppcmd_token =
  | Ppcmd_print of 'a
  | Ppcmd_box of block_type * ('a ppcmd_token Stream.t)
  | Ppcmd_print_break of int * int
  | Ppcmd_set_tab
  | Ppcmd_print_tbreak of int * int
  | Ppcmd_white_space of int
  | Ppcmd_force_newline
  | Ppcmd_print_if_broken
  | Ppcmd_open_box of block_type
  | Ppcmd_close_box
  | Ppcmd_close_tbox
  | Ppcmd_comment of int

type 'a ppdir_token =
  | Ppdir_ppcmds of 'a ppcmd_token Stream.t
  | Ppdir_print_newline
  | Ppdir_print_flush

type ppcmd = (int*string) ppcmd_token

type std_ppcmds = ppcmd Stream.t

type 'a ppdirs = 'a ppdir_token Stream.t

(* Compute length of an UTF-8 encoded string
   Rem 1 : utf8_length <= String.length (equal if pure ascii)
   Rem 2 : if used for an iso8859_1 encoded string, the result is
   wrong in very rare cases. Such a wrong case corresponds to any
   sequence of a character in range 192..253 immediately followed by a
   character in range 128..191 (typical case in french is "déçu" which
   is counted 3 instead of 4); then no real harm to use always
   utf8_length even if using an iso8859_1 encoding *)

let utf8_length s =
  let len = String.length s
  and cnt = ref 0
  and nc = ref 0
  and p = ref 0 in
  while !p < len do
    begin
      match s.[!p] with
      | '\000'..'\127' -> nc := 0 (* ascii char *)
      | '\128'..'\191' -> nc := 0 (* cannot start with a continuation byte *)
      |	'\192'..'\223' -> nc := 1 (* expect 1 continuation byte *)
      |	'\224'..'\239' -> nc := 2 (* expect 2 continuation bytes *)
      |	'\240'..'\247' -> nc := 3 (* expect 3 continuation bytes *)
      |	'\248'..'\251' -> nc := 4 (* expect 4 continuation bytes *)
      |	'\252'..'\253' -> nc := 5 (* expect 5 continuation bytes *)
      |	'\254'..'\255' -> nc := 0 (* invalid byte *)
    end ;
    incr p ;
    while !p < len && !nc > 0 do
      match s.[!p] with
      |	'\128'..'\191' (* next continuation byte *) -> incr p ; decr nc
      |	_ (* not a continuation byte *) -> nc := 0
    done ;
    incr cnt
  done ;
  !cnt

(* formatting commands *)
let str s = [< 'Ppcmd_print (utf8_length s,s) >]
let stras (i,s) = [< 'Ppcmd_print (i,s) >]
let brk (a,b) = [< 'Ppcmd_print_break (a,b) >]
let tbrk (a,b) = [< 'Ppcmd_print_tbreak (a,b) >]
let tab () = [< 'Ppcmd_set_tab >]
let fnl () = [< 'Ppcmd_force_newline >]
let pifb () = [< 'Ppcmd_print_if_broken >]
let ws n = [< 'Ppcmd_white_space n >]
let comment n = [< ' Ppcmd_comment n >]

(* derived commands *)
let mt () = [< >]
let spc () = [< 'Ppcmd_print_break (1,0) >]
let cut () = [< 'Ppcmd_print_break (0,0) >]
let align () = [< 'Ppcmd_print_break (0,0) >]
let int n = str (string_of_int n)
let real r = str (string_of_float r)
let bool b = str (string_of_bool b)
let strbrk s =
  let rec aux p n =
    if n < String.length s then
      if s.[n] = ' ' then
	if p=n then [< spc (); aux (n+1) (n+1) >]
	else [< str (String.sub s p (n-p)); spc (); aux (n+1) (n+1) >]
      else aux p (n+1)
    else if p=n then [< >] else [< str (String.sub s p (n-p)) >]
  in aux 0 0

let ismt s = try let _ = Stream.empty s in true with Stream.Failure -> false

(* boxing commands *)
let h n s = [< 'Ppcmd_box(Pp_hbox n,s) >]
let v n s = [< 'Ppcmd_box(Pp_vbox n,s) >]
let hv n s = [< 'Ppcmd_box(Pp_hvbox n,s) >]
let hov n s = [< 'Ppcmd_box(Pp_hovbox n,s) >]
let t s = [< 'Ppcmd_box(Pp_tbox,s) >]

(* Opening and closing of boxes *)
let hb n = [< 'Ppcmd_open_box(Pp_hbox n) >]
let vb n = [< 'Ppcmd_open_box(Pp_vbox n) >]
let hvb n = [< 'Ppcmd_open_box(Pp_hvbox n) >]
let hovb n = [< 'Ppcmd_open_box(Pp_hovbox n) >]
let tb () = [< 'Ppcmd_open_box Pp_tbox >]
let close () = [< 'Ppcmd_close_box >]
let tclose () = [< 'Ppcmd_close_tbox >]

let (++) = Stream.iapp

(* In new syntax only double quote char is escaped by repeating it *)
let rec escape_string s =
  let rec escape_at s i =
    if i<0 then s
    else if s.[i] == '"' then
      let s' = String.sub s 0 i^"\""^String.sub s i (String.length s - i) in
      escape_at s' (i-1)
    else escape_at s (i-1) in
  escape_at s (String.length s - 1)

let qstring s = str ("\""^escape_string s^"\"")
let qs = qstring
let quote s = h 0 (str "\"" ++ s ++ str "\"")

let rec xmlescape ppcmd =
  let rec escape what withwhat (len, str) =
    try
      let pos = String.index str what in
      let (tlen, tail) =
        escape what withwhat ((len - pos - 1),
          (String.sub str (pos + 1) (len - pos - 1)))
      in
      (pos + tlen + String.length withwhat, String.sub str 0 pos ^ withwhat ^ tail)
    with Not_found -> (len, str)
  in
  match ppcmd with
    | Ppcmd_print (len, str) ->
        Ppcmd_print (escape '"' "&quot;"
          (escape '<' "&lt;" (escape '&' "&amp;" (len, str))))
      (* In XML we always print whole content so we can npeek the whole stream *)
    | Ppcmd_box (x, str) -> Ppcmd_box (x, Stream.of_list
        (List.map xmlescape (Stream.npeek max_int str)))
    | x -> x


(* This flag tells if the last printed comment ends with a newline, to
  avoid empty lines *)
let com_eol = ref false

let com_brk ft = com_eol := false
let com_if ft f =
  if !com_eol then (com_eol := false; Format.pp_force_newline ft ())
  else Lazy.force f

let rec pr_com ft s =
  let (s1,os) =
    try
      let n = String.index s '\n' in
      String.sub s 0 n, Some (String.sub s (n+1) (String.length s - n - 1))
    with Not_found -> s,None in
  com_if ft (Lazy.lazy_from_val());
(*  let s1 =
    if String.length s1 <> 0 && s1.[0] = ' ' then
      (Format.pp_print_space ft (); String.sub s1 1 (String.length s1 - 1))
    else s1 in*)
  Format.pp_print_as ft (utf8_length s1) s1;
  match os with
      Some s2 ->
        if String.length s2 = 0 then (com_eol := true)
        else
          (Format.pp_force_newline ft (); pr_com ft s2)
    | None -> ()

(* pretty printing functions *)
let pp_dirs ft =
  let pp_open_box = function
    | Pp_hbox n   -> Format.pp_open_hbox ft ()
    | Pp_vbox n   -> Format.pp_open_vbox ft n
    | Pp_hvbox n  -> Format.pp_open_hvbox ft n
    | Pp_hovbox n -> Format.pp_open_hovbox ft n
    | Pp_tbox     -> Format.pp_open_tbox ft ()
  in
  let rec pp_cmd = function
    | Ppcmd_print(n,s)        ->
        com_if ft (Lazy.lazy_from_val()); Format.pp_print_as ft n s
    | Ppcmd_box(bty,ss)       -> (* Prevent evaluation of the stream! *)
        com_if ft (Lazy.lazy_from_val());
        pp_open_box bty ;
        if not (Format.over_max_boxes ()) then Stream.iter pp_cmd ss;
        Format.pp_close_box ft ()
    | Ppcmd_open_box bty      -> com_if ft (Lazy.lazy_from_val()); pp_open_box bty
    | Ppcmd_close_box         -> Format.pp_close_box ft ()
    | Ppcmd_close_tbox        -> Format.pp_close_tbox ft ()
    | Ppcmd_white_space n     ->
        com_if ft (Lazy.lazy_from_fun (fun()->Format.pp_print_break ft n 0))
    | Ppcmd_print_break(m,n)  ->
        com_if ft (Lazy.lazy_from_fun(fun()->Format.pp_print_break ft m n))
    | Ppcmd_set_tab           -> Format.pp_set_tab ft ()
    | Ppcmd_print_tbreak(m,n) ->
        com_if ft (Lazy.lazy_from_fun(fun()->Format.pp_print_tbreak ft m n))
    | Ppcmd_force_newline     ->
        com_brk ft; Format.pp_force_newline ft ()
    | Ppcmd_print_if_broken   ->
        com_if ft (Lazy.lazy_from_fun(fun()->Format.pp_print_if_newline ft ()))
    | Ppcmd_comment i         ->
        let coms = split_com [] [] i !comments in
(*        Format.pp_open_hvbox ft 0;*)
        List.iter (pr_com ft) coms(*;
        Format.pp_close_box ft ()*)
  in
  let pp_dir = function
    | Ppdir_ppcmds cmdstream -> Stream.iter pp_cmd cmdstream
    | Ppdir_print_newline    ->
        com_brk ft; Format.pp_print_newline ft ()
    | Ppdir_print_flush      -> Format.pp_print_flush ft ()
  in
  fun dirstream ->
    try
      Stream.iter pp_dir dirstream; com_brk ft
    with
      | e -> Format.pp_print_flush ft () ; raise e


(* pretty print on stdout and stderr *)

(* Special chars for emacs, to detect warnings inside goal output *)
let emacs_warning_start_string = String.make 1 (Char.chr 254)
let emacs_warning_end_string = String.make 1 (Char.chr 255)

let warnstart() =
  if not !print_emacs then mt() else str emacs_warning_start_string

let warnend() =
  if not !print_emacs then mt() else str emacs_warning_end_string

let warnbody strm =
  [< warnstart() ; hov 0 (str "Warning: " ++ strm) ; warnend() >]

(* pretty printing functions WITHOUT FLUSH *)
let pp_with ft strm =
  pp_dirs ft [< 'Ppdir_ppcmds strm >]

let ppnl_with ft strm =
  pp_dirs ft [< 'Ppdir_ppcmds [< strm ; 'Ppcmd_force_newline >] >]

let default_warn_with ft strm = ppnl_with ft (warnbody strm)

let pp_warn_with = ref default_warn_with

let set_warning_function pp_warn = pp_warn_with := pp_warn

let warn_with ft strm = !pp_warn_with ft strm

let warning_with ft string = warn_with ft (str string)

let pp_flush_with ft = Format.pp_print_flush ft

(* pretty printing functions WITH FLUSH *)
let msg_with ft strm =
  pp_dirs ft [< 'Ppdir_ppcmds strm ; 'Ppdir_print_flush >]

let msgnl_with ft strm =
  pp_dirs ft [< 'Ppdir_ppcmds strm ; 'Ppdir_print_newline >]

let msg_warning_with ft strm =
  msgnl_with ft (warnbody strm)

(* pretty printing functions WITHOUT FLUSH *)
let pp        x = pp_with   !std_ft x
let ppnl      x = ppnl_with !std_ft x
let pperr     x = pp_with   !err_ft x
let pperrnl   x = ppnl_with !err_ft x
let message   s = ppnl      (str s)
let warning   x = warning_with !err_ft x
let warn      x = warn_with    !err_ft x
let pp_flush  x = Format.pp_print_flush !std_ft x
let flush_all() = flush stderr; flush stdout; pp_flush()

(* pretty printing functions WITH FLUSH *)
let msg x = msg_with !std_ft x
let msgnl x = msgnl_with !std_ft x
let msgerr x = msg_with !err_ft x
let msgerrnl x = msgnl_with !err_ft x
let msg_warning x = msg_warning_with !err_ft x

let string_of_ppcmds c =
  msg_with Format.str_formatter c;
  Format.flush_str_formatter ()
