
(* $Id$ *)

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

type 'a ppdir_token =
  | Ppdir_ppcmds of 'a ppcmd_token Stream.t
  | Ppdir_print_newline
  | Ppdir_print_flush

type std_ppcmds = (int*string) ppcmd_token Stream.t
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
let sTR s = Ppcmd_print (utf8_length s,s)
let sTRas (i,s) = Ppcmd_print (i,s)
let bRK (a,b) = Ppcmd_print_break (a,b)
let tBRK (a,b) = Ppcmd_print_tbreak (a,b)
let tAB = Ppcmd_set_tab
let fNL = Ppcmd_force_newline
let pifB = Ppcmd_print_if_broken
let wS n = Ppcmd_white_space n

(* derived commands *)
let sPC = Ppcmd_print_break (1,0)
let cUT = Ppcmd_print_break (0,0)
let aLIGN = Ppcmd_print_break (0,0)
let iNT n = sTR (string_of_int n)
let rEAL r = sTR (string_of_float r)
let bOOL b = sTR (string_of_bool b)
let qSTRING s = sTR ("\""^(String.escaped s)^"\"")
let qS = qSTRING

(* boxing commands *)
let h n s = [< 'Ppcmd_box(Pp_hbox n,s) >]
let v n s = [< 'Ppcmd_box(Pp_vbox n,s) >]
let hV n s = [< 'Ppcmd_box(Pp_hvbox n,s) >]
let hOV n s = [< 'Ppcmd_box(Pp_hovbox n,s) >]
let t s = [< 'Ppcmd_box(Pp_tbox,s) >]

(* Opening and closing of boxes *)
let hB n = Ppcmd_open_box(Pp_hbox n)
let vB n = Ppcmd_open_box(Pp_vbox n)
let hVB n = Ppcmd_open_box(Pp_hvbox n)
let hOVB n = Ppcmd_open_box(Pp_hovbox n)
let tB = Ppcmd_open_box Pp_tbox
let cLOSE = Ppcmd_close_box
let tCLOSE = Ppcmd_close_tbox


(* pretty printing functions *)
let pp_dirs ft = 
  let maxbox = (get_gp ft).max_depth in
  let pp_open_box = function
    | Pp_hbox n   -> Format.pp_open_hbox ft ()
    | Pp_vbox n   -> Format.pp_open_vbox ft n
    | Pp_hvbox n  -> Format.pp_open_hvbox ft n
    | Pp_hovbox n -> Format.pp_open_hovbox ft n
    | Pp_tbox     -> Format.pp_open_tbox ft () 
  in
  let rec pp_cmd = function
    | Ppcmd_print(n,s)        -> Format.pp_print_as ft n s
    | Ppcmd_box(bty,ss)       -> (* Prevent evaluation of the stream! *)
        pp_open_box bty ;
        if not (Format.over_max_boxes ()) then Stream.iter pp_cmd ss;
        Format.pp_close_box ft ()
    | Ppcmd_open_box bty      -> pp_open_box bty
    | Ppcmd_close_box         -> Format.pp_close_box ft ()
    | Ppcmd_close_tbox        -> Format.pp_close_tbox ft ()
    | Ppcmd_white_space n     -> Format.pp_print_break ft n 0
    | Ppcmd_print_break(m,n)  -> Format.pp_print_break ft m n
    | Ppcmd_set_tab           -> Format.pp_set_tab ft ()
    | Ppcmd_print_tbreak(m,n) -> Format.pp_print_tbreak ft m n
    | Ppcmd_force_newline     -> Format.pp_force_newline ft ()
    | Ppcmd_print_if_broken   -> Format.pp_print_if_newline ft () 
  in
  let pp_dir = function
    | Ppdir_ppcmds cmdstream -> Stream.iter pp_cmd cmdstream
    | Ppdir_print_newline    -> Format.pp_print_newline ft ()
    | Ppdir_print_flush      -> Format.pp_print_flush ft () 
  in
  fun dirstream ->
    try  
      Stream.iter pp_dir dirstream
    with 
      | e -> Format.pp_print_flush ft () ; raise e


(* pretty print on stdout and stderr *)

let pp_std_dirs = pp_dirs std_ft
let pp_err_dirs = pp_dirs err_ft

let pPCMDS x = Ppdir_ppcmds x

(* pretty printing functions WITHOUT FLUSH *)
let pP_with ft strm =
  pp_dirs ft [< 'pPCMDS strm >]

let pPNL_with ft strm =
  pp_dirs ft [< 'pPCMDS [< strm ; 'Ppcmd_force_newline >] >]

let warning_with ft string =
  pPNL_with ft [< 'sTR"Warning: " ; 'sTR string >]

let wARN_with ft pps =
  pPNL_with ft [< 'sTR"Warning: " ; pps >]

let pp_flush_with ft =
  Format.pp_print_flush ft


(* pretty printing functions WITH FLUSH *)
let mSG_with ft strm =
  pp_dirs ft [< 'pPCMDS strm ; 'Ppdir_print_flush >]

let mSGNL_with ft strm =
  pp_dirs ft [< 'pPCMDS strm ; 'Ppdir_print_newline >]

let wARNING_with ft strm=
  pp_dirs ft [<'pPCMDS ([<'sTR "Warning: "; strm>]); 'Ppdir_print_newline>]


(* pretty printing functions WITHOUT FLUSH *)
let pP        = pP_with std_ft
let pPNL      = pPNL_with std_ft
let pPERR     = pP_with err_ft
let pPERRNL   = pPNL_with err_ft
let message s = pPNL [< 'sTR s >]
let warning   = warning_with std_ft
let wARN      = wARN_with std_ft
let pp_flush  = Format.pp_print_flush std_ft
let flush_all() = flush stderr; flush stdout; pp_flush()

(* pretty printing functions WITH FLUSH *)
let mSG = mSG_with std_ft
let mSGNL = mSGNL_with std_ft
let mSGERR = mSG_with err_ft
let mSGERRNL = mSGNL_with err_ft
let wARNING = wARNING_with std_ft

