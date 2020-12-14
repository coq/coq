open Loc
open Format

type ptree =
[ `Token of string * Loc.t option
| `Prod of string * (string * int * int) * ptree list
]

let tok_loc : Loc.t option ref = ref None
let stack : ptree list ref = ref []
let print = ref (try (ignore) (Sys.getenv "PRINT_STATS"); true
                 with Not_found -> false)
let do_fail = ref (try (ignore) (Sys.getenv "DONT_FAIL"); false
               with Not_found -> true)

let enable = ref (try (ignore) (Sys.getenv "DONT_ENABLE"); false
                                  with Not_found -> true)
let cnt = ref 0  (* to ignore calls from Pcoq.epsilon_value *)
let printf = Printf.eprintf

let file, sline, eline =
  try
    (* example: export DUMPAT=./theories/ssr/ssrunder.v,52,52 *)
    match Str.split (Str.regexp_string ",") (Sys.getenv "DUMPAT") with
    | [file; sline; eline] -> file, int_of_string sline, int_of_string eline
    | _ -> printf "Invalid DUMPAT setting\n"; exit 1
  with Not_found -> ("", 0, 0)

let get_stack () = !stack
let set_stack stk =
  let olen = List.length !stack in
  let nlen = List.length stk in
  if nlen <> olen && !print then
    printf "Trim stack by %d entries\n%!" (olen - nlen);
  stack := stk

(*
let get_loc = function
  | Some loc -> Printf.sprintf "/%d" (loc.bp - loc.bol_pos_last)
  | None -> ""
*)

let rec print_item fmt = function
  | `Token (s, loc) -> Format.fprintf fmt "%s" s
  | `Prod (id, (file, lnum, char), l) ->
    Format.fprintf fmt "[%s" id;
    let len = (List.length l) - 1 in
    List.iteri (fun i item ->
        Format.fprintf fmt "@ ";
        print_item fmt item;
        if i = len then
          match item with | `Token _ -> Format.fprintf fmt "@ " | _ -> ()
    ) l;
    Format.fprintf fmt "]@,"

(* The "top" of the stack is printed last.  That reads more naturally as reductions are applied. *)
let print_stack () =
  let fmt = formatter_of_out_channel stderr in
  List.iter (fun p -> Format.fprintf fmt "  > %a\n" print_item p) (List.rev !stack);
    Format.fprintf fmt "@.\n%!"

let get_fname loc =
  match loc.fname with
    | InFile fname -> fname
    | ToplevelInput -> "ToplevelInput"

let fail () =
  (match !tok_loc with
  | Some loc ->
    let src = get_fname loc in
    Printexc.print_raw_backtrace stderr (Printexc.get_callstack 100);
    printf "Near %s (line %i, %i-%i)\n%!" src (loc.line_nb) (loc.bp-loc.bol_pos) (loc.ep-loc.bol_pos);
  | _ -> ());
  print_stack ();
  if !do_fail then exit 98

(* pop and reverse *)
let popN n0 =
  let rec aux n res =
    match !stack, n with
    | _, 0 -> res
    | hd :: tl, _ -> stack := tl; aux (n-1) (hd :: res)
    | [], _ -> printf "stack underflow (pop %d with only %d entries)\n%!" n0 (n0-n) ;fail (); res
  in
  aux n0 []

let ename = ref ""

let set_ename name = ename := name

let check_stack ntname =
  if !enable && !cnt = 1 && ntname = !ename then begin
    let len = List.length !stack in
    if len > 1 then begin  (* todo: zero could be an error *)
      printf "check_stack: stack size is %d\n" len;
      fail ()
    end;
    stack := []
  end

(* callback for parser actions in GRAMMAR EXTEND *)
let parser_action prod_id n file lnum char =  (*todo: is line num for now*)
  if !enable && !cnt = 1 then begin
    let prod_id = if prod_id = "" then "*" else prod_id in
    if !print then
      printf "Reduce %s %d %s %d\n" prod_id n file char;
    let pfx = if n = 0 then [] else popN n in
    stack := `Prod (prod_id, (file, lnum, char), pfx) :: !stack;
    if !print then print_stack ();
  end

let lookahead prod_id file line char = parser_action prod_id 0 file line char

let got_list ltype len sym =
  if !enable && !cnt = 1 then begin
    if !print then
      printf "got_list %s %d of %s\n" ltype len sym;
    let n = match ltype with
      | "Sopt"
      | "Slist0"
      | "Slist1" -> len
      | "Slist0sep"
      | "Slist1sep" -> max (len+len-1) 0
      | _ -> printf "Not handled: %s\n" ltype; assert false
    in
    let pfx = popN n in
    stack := `Prod (ltype, ("", 0, 0), pfx) :: !stack;  (* todo: sb unknown *)
    if !print then print_stack ()
  end

let got_token tok =
  if !enable && !cnt = 1 then begin
    if !print then
      (match !tok_loc with
      | Some loc ->
        printf "Read \"%s\" (line %i, %i-%i)\n%!" tok (loc.line_nb) (loc.bp-loc.bol_pos) (loc.ep-loc.bol_pos)
      | None ->
        printf "Token [%s]\n" tok);
    if String.length tok > 0 then begin  (* think this is EOI *)
      stack := `Token (tok, !tok_loc) :: !stack;
      if !print then print_stack ()
    end
  end

let got_loc loc t =
  let src = match loc.fname with
    | InFile fname -> fname
    | ToplevelInput -> "ToplevelInput"
  in
  if sline <> 0 then begin
    if src = file && loc.line_nb >= sline then
      (enable := true; print := true);
    if src = file && loc.line_nb >= eline+1 then
      exit 99;
  end;
  if !enable && !cnt = 1 then begin
    if !print then
      printf "got_loc %s (line %i, %i-%i) \"%s\"\n%!"
        src (loc.line_nb) (loc.bp-loc.bol_pos) (loc.ep-loc.bol_pos) t;
    tok_loc := Some loc
  end

let start_Parse_cmd () =
  let en = !enable in
  if not en then begin
    enable := true;
    got_token "Parse";
    parser_action "*" 1 "??" 0 0
  end;
  en

let end_Parse_cmd en =
  print_stack ();
  if not en then stack := [];
  enable := en
