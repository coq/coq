(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

module Glue : sig

  (** The [Glue] module implements a container data structure with
      efficient concatenation. *)

  type 'a t

  val atom : 'a -> 'a t
  val glue : 'a t -> 'a t -> 'a t
  val empty : 'a t
  val is_empty : 'a t -> bool
  val iter : ('a -> unit) -> 'a t -> unit

end = struct

  type 'a t = GEmpty | GLeaf of 'a | GNode of 'a t * 'a t

  let atom x = GLeaf x

  let glue x y =
    match x, y with
    | GEmpty, _ -> y
    | _, GEmpty -> x
    | _, _ -> GNode (x,y)

  let empty = GEmpty

  let is_empty x = x = GEmpty

  let rec iter f = function
    | GEmpty -> ()
    | GLeaf x -> f x
    | GNode (x,y) -> iter f x; iter f y

end

module Tag :
sig
  type t 
  type 'a key
  val create : string -> 'a key
  val inj : 'a -> 'a key -> t
  val prj : t -> 'a key -> 'a option
end =
struct

module Dyn = Dyn.Make(struct end)

type t = Dyn.t
type 'a key = 'a Dyn.tag
let create = Dyn.create
let inj = Dyn.Easy.inj
let prj = Dyn.Easy.prj

end

open Pp_control

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

type str_token =
| Str_def of string
| Str_len of string * int (** provided length *)

type 'a ppcmd_token =
  | Ppcmd_print of 'a
  | Ppcmd_box of block_type * ('a ppcmd_token Glue.t)
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
  | Ppcmd_open_tag of Tag.t
  | Ppcmd_close_tag

type 'a ppdir_token =
  | Ppdir_ppcmds of 'a ppcmd_token Glue.t
  | Ppdir_print_newline
  | Ppdir_print_flush

type ppcmd = str_token ppcmd_token

type std_ppcmds = ppcmd Glue.t

type 'a ppdirs = 'a ppdir_token Glue.t

let (++) = Glue.glue

let app = Glue.glue

let is_empty g = Glue.is_empty g

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

(* formatting commands *)
let str s = Glue.atom(Ppcmd_print (Str_def s))
let stras (i, s) = Glue.atom(Ppcmd_print (Str_len (s, i)))
let brk (a,b) = Glue.atom(Ppcmd_print_break (a,b))
let tbrk (a,b) = Glue.atom(Ppcmd_print_tbreak (a,b))
let tab () = Glue.atom(Ppcmd_set_tab)
let fnl () = Glue.atom(Ppcmd_force_newline)
let pifb () = Glue.atom(Ppcmd_print_if_broken)
let ws n = Glue.atom(Ppcmd_white_space n)
let comment n = Glue.atom(Ppcmd_comment n)

(* derived commands *)
let mt () = Glue.empty
let spc () = Glue.atom(Ppcmd_print_break (1,0))
let cut () = Glue.atom(Ppcmd_print_break (0,0))
let align () = Glue.atom(Ppcmd_print_break (0,0))
let int n = str (string_of_int n)
let real r = str (string_of_float r)
let bool b = str (string_of_bool b)
let strbrk s =
  let rec aux p n =
    if n < String.length s then
      if s.[n] = ' ' then
        if p = n then spc() :: aux (n+1) (n+1)
        else str (String.sub s p (n-p)) :: spc () :: aux (n+1) (n+1)
      else aux p (n + 1)
    else if p = n then [] else [str (String.sub s p (n-p))]
  in List.fold_left (++) Glue.empty (aux 0 0)

let pr_loc_pos loc =
  if Loc.is_ghost loc then (str"<unknown>")
  else
    let loc = Loc.unloc loc in
    int (fst loc) ++ str"-" ++ int (snd loc)

let pr_loc loc =
  if Loc.is_ghost loc then str"<unknown>" ++ fnl ()
  else
    let fname = loc.Loc.fname in
    if CString.equal fname "" then
      Loc.(str"Toplevel input, characters " ++ int loc.bp ++
	   str"-" ++ int loc.ep ++ str":" ++ fnl ())
    else
      Loc.(str"File " ++ str "\"" ++ str fname ++ str "\"" ++
	   str", line " ++ int loc.line_nb ++ str", characters " ++
	   int (loc.bp-loc.bol_pos) ++ str"-" ++ int (loc.ep-loc.bol_pos) ++
	   str":" ++ fnl())

let ismt = is_empty

(* boxing commands *)
let h n s = Glue.atom(Ppcmd_box(Pp_hbox n,s))
let v n s = Glue.atom(Ppcmd_box(Pp_vbox n,s))
let hv n s = Glue.atom(Ppcmd_box(Pp_hvbox n,s))
let hov n s = Glue.atom(Ppcmd_box(Pp_hovbox n,s))
let t s = Glue.atom(Ppcmd_box(Pp_tbox,s))

(* Opening and closing of boxes *)
let hb n = Glue.atom(Ppcmd_open_box(Pp_hbox n))
let vb n = Glue.atom(Ppcmd_open_box(Pp_vbox n))
let hvb n = Glue.atom(Ppcmd_open_box(Pp_hvbox n))
let hovb n = Glue.atom(Ppcmd_open_box(Pp_hovbox n))
let tb () = Glue.atom(Ppcmd_open_box Pp_tbox)
let close () = Glue.atom(Ppcmd_close_box)
let tclose () = Glue.atom(Ppcmd_close_tbox)

(* Opening and closed of tags *)
let open_tag t = Glue.atom(Ppcmd_open_tag t)
let close_tag () = Glue.atom(Ppcmd_close_tag)
let tag t s = open_tag t ++ s ++ close_tag ()
let eval_ppcmds l = l

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
  com_if ft (Lazy.from_val());
(*  let s1 =
    if String.length s1 <> 0 && s1.[0] = ' ' then
      (Format.pp_print_space ft (); String.sub s1 1 (String.length s1 - 1))
    else s1 in*)
  Format.pp_print_as ft (utf8_length s1) s1;
  match os with
      Some s2 ->
        if Int.equal (String.length s2) 0 then (com_eol := true)
        else
          (Format.pp_force_newline ft (); pr_com ft s2)
    | None -> ()

type tag_handler = Tag.t -> Format.tag

(* pretty printing functions *)
let pp_dirs ?pp_tag ft =
  let pp_open_box = function
    | Pp_hbox n   -> Format.pp_open_hbox ft ()
    | Pp_vbox n   -> Format.pp_open_vbox ft n
    | Pp_hvbox n  -> Format.pp_open_hvbox ft n
    | Pp_hovbox n -> Format.pp_open_hovbox ft n
    | Pp_tbox     -> Format.pp_open_tbox ft ()
  in
  let rec pp_cmd = function
    | Ppcmd_print tok         ->
        begin match tok with
        | Str_def s ->
          let n = utf8_length s in
          com_if ft (Lazy.from_val()); Format.pp_print_as ft n s
        | Str_len (s, n) ->
          com_if ft (Lazy.from_val()); Format.pp_print_as ft n s
        end
    | Ppcmd_box(bty,ss)       -> (* Prevent evaluation of the stream! *)
        com_if ft (Lazy.from_val());
        pp_open_box bty ;
        if not (Format.over_max_boxes ()) then Glue.iter pp_cmd ss;
        Format.pp_close_box ft ()
    | Ppcmd_open_box bty      -> com_if ft (Lazy.from_val()); pp_open_box bty
    | Ppcmd_close_box         -> Format.pp_close_box ft ()
    | Ppcmd_close_tbox        -> Format.pp_close_tbox ft ()
    | Ppcmd_white_space n     ->
        com_if ft (Lazy.from_fun (fun()->Format.pp_print_break ft n 0))
    | Ppcmd_print_break(m,n)  ->
        com_if ft (Lazy.from_fun(fun()->Format.pp_print_break ft m n))
    | Ppcmd_set_tab           -> Format.pp_set_tab ft ()
    | Ppcmd_print_tbreak(m,n) ->
        com_if ft (Lazy.from_fun(fun()->Format.pp_print_tbreak ft m n))
    | Ppcmd_force_newline     ->
        com_brk ft; Format.pp_force_newline ft ()
    | Ppcmd_print_if_broken   ->
        com_if ft (Lazy.from_fun(fun()->Format.pp_print_if_newline ft ()))
    | Ppcmd_comment i         ->
        let coms = split_com [] [] i !comments in
(*        Format.pp_open_hvbox ft 0;*)
        List.iter (pr_com ft) coms(*;
        Format.pp_close_box ft ()*)
    | Ppcmd_open_tag tag ->
      begin match pp_tag with
      | None -> ()
      | Some f -> Format.pp_open_tag ft (f tag)
      end
    | Ppcmd_close_tag ->
      begin match pp_tag with
      | None -> ()
      | Some _ -> Format.pp_close_tag ft ()
      end
  in
  let pp_dir = function
    | Ppdir_ppcmds cmdstream -> Glue.iter pp_cmd cmdstream
    | Ppdir_print_newline    ->
        com_brk ft; Format.pp_print_newline ft ()
    | Ppdir_print_flush      -> Format.pp_print_flush ft ()
  in
  fun (dirstream : _ ppdirs) ->
    try
      Glue.iter pp_dir dirstream; com_brk ft
    with reraise ->
      let reraise = Backtrace.add_backtrace reraise in
      let () = Format.pp_print_flush ft () in
      Exninfo.iraise reraise

(* pretty printing functions WITHOUT FLUSH *)
let pp_with ?pp_tag ft strm =
  pp_dirs ?pp_tag ft (Glue.atom (Ppdir_ppcmds strm))

(* pretty printing functions WITH FLUSH *)
let msg_with ?pp_tag ft strm =
  pp_dirs ?pp_tag ft (Glue.atom(Ppdir_ppcmds strm) ++ Glue.atom(Ppdir_print_flush))

(* If mixing some output and a goal display, please use msg_warning,
   so that interfaces (proofgeneral for example) can easily dispatch
   them to different windows. *)

(** Output to a string formatter *)
let string_of_ppcmds c =
  Format.fprintf Format.str_formatter "@[%a@]" (msg_with ?pp_tag:None) c;
  Format.flush_str_formatter ()

(* Copy paste from Util *)

let pr_comma () = str "," ++ spc ()
let pr_semicolon () = str ";" ++ spc ()
let pr_bar () = str "|" ++ spc ()
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

let prlist pr l = List.fold_left (fun x e -> x ++ pr e) Glue.empty l

(* unlike all other functions below, [prlist] works lazily.
   if a strict behavior is needed, use [prlist_strict] instead.
   evaluation is done from left to right. *)

let prlist_sep_lastsep no_empty sep lastsep elem =
  let rec start = function
    |[] -> mt ()
    |[e] -> elem e
    |h::t -> let e = elem h in
        if no_empty && ismt e then start t else
          let rec aux = function
            |[] -> mt ()
            |h::t ->
               let e = elem h and r = aux t in
                 if no_empty && ismt e then r else
                   if ismt r
                   then let s = lastsep () in s ++ e
                   else let s = sep () in s ++ e ++ r
          in let r = aux t in e ++ r
  in start

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

