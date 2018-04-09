(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* The different kinds of blocks are:
   \begin{description}
   \item[hbox:] Horizontal block no line breaking;
   \item[vbox:] Vertical block each break leads to a new line;
   \item[hvbox:] Horizontal-vertical block: same as vbox, except if
      this block is small enough to fit on a single line
   \item[hovbox:] Horizontal or Vertical block: breaks lead to new line
      only when necessary to print the content of the block
   \end{description}
 *)

type pp_tag = string

type block_type =
  | Pp_hbox   of int
  | Pp_vbox   of int
  | Pp_hvbox  of int
  | Pp_hovbox of int

type doc_view =
  | Ppcmd_empty
  | Ppcmd_string of string
  | Ppcmd_glue of doc_view list
  | Ppcmd_box  of block_type * doc_view
  | Ppcmd_tag of pp_tag * doc_view
  (* Are those redundant? *)
  | Ppcmd_print_break of int * int
  | Ppcmd_force_newline
  | Ppcmd_comment of string list

(* Following discussion on #390, we play on the safe side and make the
   internal representation opaque here. *)
type t = doc_view

type std_ppcmds = t
[@@ocaml.deprecated "alias of Pp.t"]

let repr x = x
let unrepr x = x

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
      | '\192'..'\223' -> nc := 1 (* expect 1 continuation byte *)
      | '\224'..'\239' -> nc := 2 (* expect 2 continuation bytes *)
      | '\240'..'\247' -> nc := 3 (* expect 3 continuation bytes *)
      | '\248'..'\251' -> nc := 4 (* expect 4 continuation bytes *)
      | '\252'..'\253' -> nc := 5 (* expect 5 continuation bytes *)
      | '\254'..'\255' -> nc := 0 (* invalid byte *)
    end ;
    incr p ;
    while !p < len && !nc > 0 do
      match s.[!p] with
      | '\128'..'\191' (* next continuation byte *) -> incr p ; decr nc
      | _ (* not a continuation byte *) -> nc := 0
    done ;
    incr cnt
  done ;
  !cnt

let rec app d1 d2 = match d1, d2 with
  | Ppcmd_empty,        d
  | d,                  Ppcmd_empty      -> d

  (* Optimizations *)
  | Ppcmd_glue [l1;l2], Ppcmd_glue l3    -> Ppcmd_glue (l1 :: l2 :: l3)
  | Ppcmd_glue [l1;l2], d2               -> Ppcmd_glue [l1 ; l2 ; d2]
  | d1,                 Ppcmd_glue l2    -> Ppcmd_glue (d1 :: l2)

  | Ppcmd_tag(t1,d1),   Ppcmd_tag(t2,d2)
    when t1 = t2                         -> Ppcmd_tag(t1,app d1 d2)
  | d1, d2                               -> Ppcmd_glue [d1; d2]
  (* Optimizations deemed too costly *)
  (* | Ppcmd_glue l1,    Ppcmd_glue l2    -> Ppcmd_glue   (l1 @ l2) *)
  (* | Ppcmd_string s1,  Ppcmd_string s2  -> Ppcmd_string (s1 ^ s2) *)

let seq s = Ppcmd_glue s

let (++) = app

(* formatting commands *)
let str s     = Ppcmd_string s
let brk (a,b) = Ppcmd_print_break (a,b)
let fnl  ()   = Ppcmd_force_newline
let ws n      = Ppcmd_print_break (n,0)
let comment l = Ppcmd_comment l

(* derived commands *)
let mt    () = Ppcmd_empty
let spc   () = Ppcmd_print_break (1,0)
let cut   () = Ppcmd_print_break (0,0)
let align () = Ppcmd_print_break (0,0)
let int   n  = str (string_of_int n)
let real  r  = str (string_of_float r)
let bool  b  = str (string_of_bool b)

(* XXX: To Remove *)
let strbrk s =
  let rec aux p n =
    if n < String.length s then
      if s.[n] = ' ' then
        if p = n then spc() :: aux (n+1) (n+1)
        else str (String.sub s p (n-p)) :: spc () :: aux (n+1) (n+1)
      else aux p (n + 1)
    else if p = n then [] else [str (String.sub s p (n-p))]
  in Ppcmd_glue (aux 0 0)

let ismt = function | Ppcmd_empty -> true | _ -> false

(* boxing commands *)
let h   n s = Ppcmd_box(Pp_hbox n,s)
let v   n s = Ppcmd_box(Pp_vbox n,s)
let hv  n s = Ppcmd_box(Pp_hvbox n,s)
let hov n s = Ppcmd_box(Pp_hovbox n,s)

(* Opening and closing of tags *)
let tag t s = Ppcmd_tag(t,s)

(* In new syntax only double quote char is escaped by repeating it *)
let escape_string s =
  let rec escape_at s i =
    if i<0 then s
    else if s.[i] == '"' then
      let s' = String.sub s 0 i^"\""^String.sub s i (String.length s - i) in
      escape_at s' (i-1)
    else escape_at s (i-1) in
  escape_at s (String.length s - 1)

let qstring s = str "\"" ++ str (escape_string s) ++ str "\""
let qs = qstring
let quote s = h 0 (str "\"" ++ s ++ str "\"")

let rec pr_com ft s =
  let (s1,os) =
    try
      let n = String.index s '\n' in
      String.sub s 0 n, Some (String.sub s (n+1) (String.length s - n - 1))
    with Not_found -> s,None in
  Format.pp_print_as ft (utf8_length s1) s1;
  match os with
      Some s2 -> Format.pp_force_newline ft (); pr_com ft s2
    | None -> ()

let start_pfx = "start."
let end_pfx = "end."

let split_pfx pfx str =
  let (str_len, pfx_len) = (String.length str, String.length pfx) in
  if str_len >= pfx_len && (String.sub str 0 pfx_len) = pfx then
    (pfx, String.sub str pfx_len (str_len - pfx_len)) else ("", str);;

let split_tag tag =
  let (pfx, ttag) = split_pfx start_pfx tag in
  if pfx <> "" then (pfx, ttag) else
    let (pfx, ttag) = split_pfx end_pfx tag in
    (pfx, ttag);;

(* pretty printing functions *)
let pp_with ft pp =
  let cpp_open_box = function
    | Pp_hbox n   -> Format.pp_open_hbox ft ()
    | Pp_vbox n   -> Format.pp_open_vbox ft n
    | Pp_hvbox n  -> Format.pp_open_hvbox ft n
    | Pp_hovbox n -> Format.pp_open_hovbox ft n
  in
  let rec pp_cmd = let open Format in function
    | Ppcmd_empty             -> ()
    | Ppcmd_glue sl           -> List.iter pp_cmd sl
    | Ppcmd_string str        -> let n = utf8_length str in
                                 pp_print_as ft n str
    | Ppcmd_box(bty,ss)       -> cpp_open_box bty ;
                                 if not (over_max_boxes ()) then pp_cmd ss;
                                 pp_close_box ft ()
    | Ppcmd_print_break(m,n)  -> pp_print_break ft m n
    | Ppcmd_force_newline     -> pp_force_newline ft ()
    | Ppcmd_comment coms      -> List.iter (pr_com ft) coms
    | Ppcmd_tag(tag, s)       -> pp_open_tag  ft tag;
                                 pp_cmd s;
                                 pp_close_tag ft ()
  in
  try pp_cmd pp
  with reraise ->
    let reraise = Backtrace.add_backtrace reraise in
    let () = Format.pp_print_flush ft () in
    Exninfo.iraise reraise

(* If mixing some output and a goal display, please use msg_warning,
   so that interfaces (proofgeneral for example) can easily dispatch
   them to different windows. *)

(** Output to a string formatter *)
let string_of_ppcmds c =
  Format.fprintf Format.str_formatter "@[%a@]" pp_with c;
  Format.flush_str_formatter ()

(* Copy paste from Util *)

let pr_comma () = str "," ++ spc ()
let pr_semicolon () = str ";" ++ spc ()
let pr_bar () = str "|" ++ spc ()
let pr_spcbar () = str " |" ++ spc ()
let pr_arg pr x = spc () ++ pr x
let pr_non_empty_arg pr x = let pp = pr x in if ismt pp then mt () else spc () ++ pr x
let pr_opt pr = function None -> mt () | Some x -> pr_arg pr x
let pr_opt_no_spc pr = function None -> mt () | Some x -> pr x

(** TODO: merge with CString.ordinal *)
let pr_nth n =
  let s =
    if (n / 10) mod 10 = 1 then "th"
    else match n mod 10 with
    | 1 -> "st"
    | 2 -> "nd"
    | 3 -> "rd"
    | _ -> "th"
  in
  int n ++ str s

(* [prlist pr [a ; ... ; c]] outputs [pr a ++ ... ++ pr c] *)

let prlist pr l = Ppcmd_glue (List.map pr l)

(* unlike all other functions below, [prlist] works lazily.
   if a strict behavior is needed, use [prlist_strict] instead.
   evaluation is done from left to right. *)

let prlist_sep_lastsep no_empty sep_thunk lastsep_thunk elem l =
  let sep = sep_thunk () in
  let lastsep = lastsep_thunk () in
  let elems = List.map elem l in
  let filtered_elems =
    if no_empty then
      List.filter (fun e -> not (ismt e)) elems
    else
      elems
  in
  let rec insert_seps es =
    match es with
    | []     -> mt ()
    | [e]    -> e
    | h::[e] -> h ++ lastsep ++ e
    | h::t   -> h ++ sep ++ insert_seps t
  in
  insert_seps filtered_elems
  
let prlist_strict pr l = prlist_sep_lastsep true mt mt pr l
(* [prlist_with_sep sep pr [a ; ... ; c]] outputs
   [pr a ++ sep() ++ ... ++ sep() ++ pr c] *)
let prlist_with_sep sep pr l = prlist_sep_lastsep false sep sep pr l
(* Print sequence of objects separated by space (unless an element is empty) *)
let pr_sequence pr l = prlist_sep_lastsep true spc spc pr l
(* [pr_enum pr [a ; b ; ... ; c]] outputs
   [pr a ++ str "," ++ pr b ++ str "," ++ ... ++ str "and" ++ pr c] *)
let pr_enum pr l = prlist_sep_lastsep true pr_comma (fun () -> str " and" ++ spc ()) pr l

let pr_vertical_list pr = function
  | [] -> str "none" ++ fnl ()
  | l -> fnl () ++ str "  " ++ hov 0 (prlist_with_sep fnl pr l) ++ fnl ()

(* [prvecti_with_sep sep pr [|a0 ; ... ; an|]] outputs
   [pr 0 a0 ++ sep() ++ ... ++ sep() ++ pr n an] *)

let prvecti_with_sep sep elem v =
  let rec pr i =
    if Int.equal i 0 then
      elem 0 v.(0)
    else
      let r = pr (i-1) and s = sep () and e = elem i v.(i) in
      r ++ s ++ e
  in
  let n = Array.length v in
  if Int.equal n 0 then mt () else pr (n - 1)

(* [prvecti pr [|a0 ; ... ; an|]] outputs [pr 0 a0 ++ ... ++ pr n an] *)

let prvecti elem v = prvecti_with_sep mt elem v

(* [prvect_with_sep sep pr [|a ; ... ; c|]] outputs
   [pr a ++ sep() ++ ... ++ sep() ++ pr c] *)

let prvect_with_sep sep elem v = prvecti_with_sep sep (fun _ -> elem) v

(* [prvect pr [|a ; ... ; c|]] outputs [pr a ++ ... ++ pr c] *)

let prvect elem v = prvect_with_sep mt elem v

let surround p = hov 1 (str"(" ++ p ++ str")")

(*** DEBUG code ***)

let db_print_pp fmt pp =
  let open Format in
  let block_type fmt btype =
    let (bt, v) =
      match btype with
      | Pp_hbox v -> ("Pp_hbox", v)
      | Pp_vbox v -> ("Pp_vbox", v)
      | Pp_hvbox v -> ("Pp_hvbox", v)
      | Pp_hovbox v -> ("Pp_hovbox", v)
    in
    fprintf fmt "%s %d" bt v
  in
  let rec db_print_pp_r indent pp =
    let ind () = fprintf fmt "%s" (String.make (2 * indent) ' ') in
    ind();
    match pp with
    | Ppcmd_empty ->
        fprintf fmt "Ppcmd_empty@;"
    | Ppcmd_string str ->
        fprintf fmt "Ppcmd_string '%s'@;" str
    | Ppcmd_glue list ->
        fprintf fmt "Ppcmd_glue@;";
        List.iter (fun x -> db_print_pp_r (indent + 1) (repr x)) list;
    | Ppcmd_box (block, pp) ->
        fprintf fmt "Ppcmd_box %a@;" block_type block;
        db_print_pp_r (indent + 1) (repr pp);
    | Ppcmd_tag (tag, pp) ->
        fprintf fmt "Ppcmd_tag %s@;" tag;
        db_print_pp_r (indent + 1) (repr pp);
    | Ppcmd_print_break (i, j) ->
        fprintf fmt "Ppcmd_print_break %d %d@;" i j
    | Ppcmd_force_newline ->
        fprintf fmt "Ppcmd_force_newline@;"
    | Ppcmd_comment list ->
        fprintf fmt "Ppcmd_comment@;";
        List.iter (fun x -> ind(); (fprintf fmt "%s@;" x)) list
  in
  pp_open_vbox fmt 0;
  db_print_pp_r 0 pp;
  pp_close_box fmt ();
  pp_print_flush fmt ()

let db_string_of_pp pp =
  Format.asprintf "%a" db_print_pp pp

let rec flatten pp =
  match pp with
  | Ppcmd_glue l -> Ppcmd_glue (List.concat (List.map
      (fun x -> let x = flatten x in
                  match x with
                  | Ppcmd_glue l2 -> l2
                  | p -> [p])
      l))
  | Ppcmd_box (block, pp) -> Ppcmd_box (block, flatten pp)
  | Ppcmd_tag (tag, pp) -> Ppcmd_tag (tag, flatten pp)
  | p -> p
