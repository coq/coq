type ptree =
[ `Token of string
| `Prod of string * ptree list
]

open Loc

let tok_loc : Loc.t option ref = ref None
let stack : ptree list ref = ref []
let print = ref (try (ignore) (Sys.getenv "PRINT_STATS"); true
                 with Not_found -> false)
let do_fail = ref (try (ignore) (Sys.getenv "DONT_FAIL"); false
               with Not_found -> true)

let ignore_stuff = ref false  (* todo: is this still needed? *)
let enable = ref true
let cnt = ref 0
let progress = ref false
let printf = Printf.eprintf
(*(try (ignore) (Sys.getenv "ENABLE_PTREE"); true with Not_found -> false)*)

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

let rec print_item = function
  | `Token s -> printf "%s " s
  | `Prod (id, l) ->
    printf "[%s " id;
    List.iter (fun i -> print_item i) l;
    printf "]"

(* The "top" of the stack is printed last.  That reads more naturally as reductions are applied. *)
let print_stack () =
  List.iter (fun p -> printf "  > "; print_item p; printf "\n") (List.rev !stack);
(*  if !stack <> [] then*)
    printf "\n"

let fail () =
  (match !tok_loc with
  | Some loc ->
    let src = match loc.fname with
      | InFile fname -> fname
      | ToplevelInput -> "ToplevelInput" in
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

let check_stack () =
  if !enable && !cnt = 1 then begin
    let len = List.length !stack in
    if len > 1 then begin  (* todo: zero could be an error *)
      printf "check_stack: stack size is %d\n" len;
      fail ()
    end;
    (ignore)(popN len)
  end

(* callback for parser actions in GRAMMAR EXTEND *)
let parser_action prod_id n file char =  (*todo: is line num for now*)
  progress := true;
  if !enable && !cnt = 1 then begin
    if not !ignore_stuff then begin
      let prod_id = if prod_id = "" then "*" else prod_id in
      if !print then
        printf "Reduce %s %d %s %d\n" prod_id n file char;
      let pfx = if n = 0 then [] else popN n in
      stack := `Prod (prod_id, pfx) :: !stack;
      if !print then print_stack ();
    end
  end

let lookahead prod_id file line = parser_action prod_id 0 file line

let got_list ltype len sym =
  begin match !tok_loc with
    | None -> ()
    | Some loc ->
      let _ = match loc.fname with
        | InFile fname -> ignore_stuff := false; fname
        | ToplevelInput -> ignore_stuff := true; "ToplevelInput"
      in ()
  end;

  if !enable && !cnt = 1 then begin
    if not !ignore_stuff then begin
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
      stack := `Prod (ltype, pfx) :: !stack;
      if !print then print_stack ()
    end
  end

let got_token tok =
  if !enable && !cnt = 1 && not !ignore_stuff then begin
    if !print then
      (match !tok_loc with
      | Some loc ->
        printf "Read \"%s\" (line %i, %i-%i)\n%!" tok (loc.line_nb) (loc.bp-loc.bol_pos) (loc.ep-loc.bol_pos)
(*        if (String.length tok) = 0 then begin*)
(*          printf "String length = %d\n%!" (String.length tok);*)
(*          Printexc.print_raw_backtrace stdout (Printexc.get_callstack 100);*)
(*        end*)
      | None ->
        printf "Token [%s]\n" tok);
    if String.length tok > 0 then begin  (* think this is EOI *)
      stack := `Token tok :: !stack;
      if !print then print_stack ()
    end
  end(* else
    printf "ignore token %s\n%!" tok
*)
let got_loc loc t =
(*  let prev = !ignore_stuff in*)
  let src = match loc.fname with
    | InFile fname -> ignore_stuff := false; fname
    | ToplevelInput -> ignore_stuff := true; "ToplevelInput"
  in
(*  if !enable && !cnt = 1 && prev <> !ignore_stuff then*)
(*    printf "ignore_stuff set to %b\n%!" !ignore_stuff;*)
  if sline <> 0 then begin
    if src = file && loc.line_nb >= sline then
      (enable := true; print := true);
    if src = file && loc.line_nb >= eline+1 then
      exit 99;
  end;
  if !enable && !cnt = 1 (*&& !ignore_stuff*) then begin
    if !print then
      printf "got_loc %s (line %i, %i-%i) \"%s\"\n%!"
        src (loc.line_nb) (loc.bp-loc.bol_pos) (loc.ep-loc.bol_pos) t;
    tok_loc := Some loc
  end
