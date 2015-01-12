(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

module Glue : sig

  (* A left associative glue implements efficient glue operator
     when used as left associative.  If glue is denoted ++ then

        a ++ b ++ c ++ d = ((a ++ b) ++ c) ++ d = [d] @ ([c] @ ([b] @  [a]))

     I.e. if the short list is the second argument
  *)
  type 'a t

  val atom : 'a -> 'a t
  val glue : 'a t -> 'a t -> 'a t
  val empty : 'a t
  val is_empty : 'a t -> bool
  val iter : ('a -> unit) -> 'a t -> unit
  val map : ('a -> 'b) -> 'a t -> 'b t

end = struct

  type 'a t = 'a list

  let atom x = [x]
  let glue x y = y @ x
  let empty = []
  let is_empty x = x = []

  let iter f g = List.iter f (List.rev g)
  let map = List.map
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
  (** See module {Dyn} for more details. *)

  type t = int * Obj.t

  type 'a key = int

  let dyntab = ref (Int.Map.empty : string Int.Map.t)

  let create (s : string) =
    let hash = Hashtbl.hash s in
    let () = assert (not (Int.Map.mem hash !dyntab)) in
    let () = dyntab := Int.Map.add hash s !dyntab in
    hash

  let inj x h = (h, Obj.repr x)

  let prj (nh, rv) h =
    if Int.equal h nh then Some (Obj.magic rv)
    else None

end

open Pp_control

(* This should not be used outside of this file. Use
   Flags.print_emacs instead. This one is updated when reading
   command line options. This was the only way to make [Pp] depend on
   an option without creating a circularity: [Flags] -> [Util] ->
   [Pp] -> [Flags] *)
let print_emacs = ref false

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

let rewrite f p =
  let strtoken = function
    | Str_len (s, n) ->
      let s' = f s in
      Str_len (s', String.length s')
    | Str_def s ->
      Str_def (f s)
  in
  let rec ppcmd_token = function
    | Ppcmd_print x -> Ppcmd_print (strtoken x)
    | Ppcmd_box (bt, g) -> Ppcmd_box (bt, Glue.map ppcmd_token g)
    | p -> p
  in
  Glue.map ppcmd_token p

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

let qstring s = str ("\""^escape_string s^"\"")
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
  com_if ft (Lazy.lazy_from_val());
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
          com_if ft (Lazy.lazy_from_val()); Format.pp_print_as ft n s
        | Str_len (s, n) ->
          com_if ft (Lazy.lazy_from_val()); Format.pp_print_as ft n s
        end
    | Ppcmd_box(bty,ss)       -> (* Prevent evaluation of the stream! *)
        com_if ft (Lazy.lazy_from_val());
        pp_open_box bty ;
        if not (Format.over_max_boxes ()) then Glue.iter pp_cmd ss;
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



(* pretty print on stdout and stderr *)

(* Special chars for emacs, to detect warnings inside goal output *)
let emacs_quote_start = String.make 1 (Char.chr 254)
let emacs_quote_end = String.make 1 (Char.chr 255)

let emacs_quote_info_start = "<infomsg>"
let emacs_quote_info_end = "</infomsg>"

let emacs_quote g =
  if !print_emacs then str emacs_quote_start ++ hov 0 g ++ str emacs_quote_end
  else hov 0 g

let emacs_quote_info g =
  if !print_emacs then str emacs_quote_info_start++fnl() ++ hov 0 g ++ str emacs_quote_info_end
  else hov 0 g


(* pretty printing functions WITHOUT FLUSH *)
let pp_with ?pp_tag ft strm =
  pp_dirs ?pp_tag ft (Glue.atom (Ppdir_ppcmds strm))

let ppnl_with ft strm =
  pp_dirs ft (Glue.atom (Ppdir_ppcmds (strm ++ fnl ())))

let pp_flush_with ft = Format.pp_print_flush ft

(* pretty printing functions WITH FLUSH *)
let msg_with ft strm =
  pp_dirs ft (Glue.atom(Ppdir_ppcmds strm) ++ Glue.atom(Ppdir_print_flush))

let msgnl_with ft strm =
  pp_dirs ft (Glue.atom(Ppdir_ppcmds strm) ++ Glue.atom(Ppdir_print_newline))

(* pretty printing functions WITHOUT FLUSH *)
let pp        x = pp_with   !std_ft x
let ppnl      x = ppnl_with !std_ft x
let pperr     x = pp_with   !err_ft x
let pperrnl   x = ppnl_with !err_ft x
let message   s = ppnl      (str s)
let pp_flush  x = Format.pp_print_flush !std_ft x
let pperr_flush x = Format.pp_print_flush !err_ft x
let flush_all () =
  flush stderr; flush stdout; pp_flush (); pperr_flush ()

(* pretty printing functions WITH FLUSH *)
let msg x = msg_with !std_ft x
let msgnl x = msgnl_with !std_ft x
let msgerr x = msg_with !err_ft x
let msgerrnl x = msgnl_with !err_ft x

(* Logging management *)

type message_level =  Feedback.message_level =
  | Debug of string
  | Info
  | Notice
  | Warning
  | Error

type message = Feedback.message = {
  message_level : message_level;
  message_content : string;
}

let of_message = Feedback.of_message
let to_message = Feedback.to_message
let is_message = Feedback.is_message

type logger = message_level -> std_ppcmds -> unit

let make_body info s =
  emacs_quote (hov 0 (info ++ spc () ++ s))

let debugbody strm = hov 0 (str "Debug:" ++ spc () ++ strm)
let warnbody strm = make_body (str "Warning:") strm
let errorbody strm = make_body (str "Error:") strm
let infobody strm = emacs_quote_info strm

let std_logger ~id:_ level msg = match level with
| Debug _ -> msgnl (debugbody msg)
| Info -> msgnl (hov 0 msg)
| Notice -> msgnl msg
| Warning -> Flags.if_warn (fun () -> msgnl_with !err_ft (warnbody msg)) ()
| Error -> msgnl_with !err_ft (errorbody msg)

let emacs_logger ~id:_ level mesg = match level with
| Debug _ -> msgnl (debugbody mesg)
| Info -> msgnl (infobody mesg)
| Notice -> msgnl mesg
| Warning -> Flags.if_warn (fun () -> msgnl_with !err_ft (warnbody mesg)) ()
| Error -> msgnl_with !err_ft (errorbody mesg)

let logger = ref std_logger

let make_pp_emacs() = print_emacs:=true; logger:=emacs_logger
let make_pp_nonemacs() = print_emacs:=false; logger := std_logger


let feedback_id = ref (Feedback.Edit 0)
let feedback_route = ref Feedback.default_route

(* If mixing some output and a goal display, please use msg_warning,
   so that interfaces (proofgeneral for example) can easily dispatch
   them to different windows. *)

let msg_info x = !logger ~id:!feedback_id Info x
let msg_notice x = !logger ~id:!feedback_id Notice x
let msg_warning x = !logger ~id:!feedback_id Warning x
let msg_error x = !logger ~id:!feedback_id Error x
let msg_debug x = !logger ~id:!feedback_id (Debug "_") x

let set_logger l = logger := (fun ~id:_ lvl msg -> l lvl msg)

let std_logger lvl msg = std_logger ~id:!feedback_id lvl msg

(** Feedback *)

let feeder = ref ignore
let set_id_for_feedback ?(route=Feedback.default_route) i =
  feedback_id := i; feedback_route := route
let feedback ?state_id ?edit_id ?route what =
  !feeder {
     Feedback.contents = what;
     Feedback.route = Option.default !feedback_route route;
     Feedback.id =
       match state_id, edit_id with
       | Some id, _ -> Feedback.State id
       | None, Some eid -> Feedback.Edit eid
       | None, None -> !feedback_id;
  }
let set_feeder f = feeder := f
let get_id_for_feedback () = !feedback_id, !feedback_route

(** Utility *)

let string_of_ppcmds c =
  msg_with Format.str_formatter c;
  Format.flush_str_formatter ()

let log_via_feedback () = logger := (fun ~id lvl msg ->
  !feeder {
     Feedback.contents = Feedback.Message {
       message_level = lvl;
       message_content = string_of_ppcmds msg };
     Feedback.route = !feedback_route;
     Feedback.id = id })

(* Copy paste from Util *)

let pr_comma () = str "," ++ spc ()
let pr_semicolon () = str ";" ++ spc ()
let pr_bar () = str "|" ++ spc ()
let pr_arg pr x = spc () ++ pr x
let pr_opt pr = function None -> mt () | Some x -> pr_arg pr x
let pr_opt_no_spc pr = function None -> mt () | Some x -> pr x

let pr_nth n =
  int n ++ str (match n mod 10 with 1 -> "st" | 2 -> "nd" | 3 -> "rd" | _ -> "th")

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
