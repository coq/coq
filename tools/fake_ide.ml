(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Fake_ide : Simulate a [coqide] talking to a [coqtop -ideslave] *)

exception Comment

type coqtop = {
  xml_printer : Xml_printer.t;
  xml_parser : Xml_parser.t;
}

let logger level content = prerr_endline content

let base_eval_call ?(print=true) call coqtop =
  if print then prerr_endline (Serialize.pr_call call);
  let xml_query = Serialize.of_call call in
  Xml_printer.print coqtop.xml_printer xml_query;
  let rec loop () =
    let xml = Xml_parser.parse coqtop.xml_parser in
    if Serialize.is_message xml then
      let message = Serialize.to_message xml in
      let level = message.Interface.message_level in
      let content = message.Interface.message_content in
      logger level content;
      loop ()
    else if Serialize.is_feedback xml then
      loop ()
    else (Serialize.to_answer call xml)
  in
  let res = loop () in
  if print then prerr_endline (Serialize.pr_full_value call res);
  match res with Interface.Fail _ -> exit 1 | x -> x

let eval_call c q = ignore(base_eval_call c q)

module Parser = struct

  exception Err of string
  exception More

  type token =
    | Tok of string * string
    | Top of token list

  type grammar =
    | Alt of grammar list
    | Seq of grammar list
    | Opt of grammar
    | Item of (string * (string -> token * int))

  let eat_rex x = x, fun s ->
    if Str.string_match (Str.regexp x) s 0 then begin
      let m = Str.match_end () in
      let w = String.sub s 0 m in
      Tok(x,w), m
    end else raise (Err ("Regexp "^x^" not found in: "^s))

  let eat_balanced c =
    let c' = match c with
      | '{' -> '}' | '(' -> ')' | '[' -> ']' | _ -> assert false in
    let sc, sc' = String.make 1 c, String.make 1 c' in
    let name = sc ^ "..." ^ sc' in
    let unescape s =
      Str.global_replace (Str.regexp ("\\\\"^sc)) sc
        (Str.global_replace (Str.regexp ("\\\\"^sc')) sc' s) in
    name, fun s ->
    if s.[0] = c then
      let rec find n m =
        if String.length s <= m then raise More;
        if s.[m] = c' then
          if n = 0 then Tok (name, unescape (String.sub s 1 (m-1))), m+1
          else find (n-1) (m+1)
        else if s.[m] = c then find (n+1) (m+1)
        else if s.[m] = '\\' && String.length s > m+1 && s.[m+1] = c then
          find n (m+2)
        else if s.[m] = '\\' && String.length s > m+1 && s.[m+1] = c' then
          find n (m+2)
        else find n (m+1)
      in find ~-1 0
    else raise (Err ("Balanced "^String.make 1 c^" not found in: "^s))

  let eat_blanks s = snd (eat_rex "[ \n\t]*") s

  let s = ref ""

  let parse g =
    let read_more () = s := !s ^ read_line () ^ "\n" in
    let ensure_non_empty n = if n = String.length !s then read_more () in
    let cut_after s n = String.sub s n (String.length s - n) in
    let rec wrap f n =
      try
        ensure_non_empty n;
        let _, n' = eat_blanks (cut_after !s n) in
        ensure_non_empty n';
        let t, m = f (cut_after !s (n+n')) in
        let _, m' = eat_blanks (cut_after !s (n+n'+m)) in
        t, n+n'+m+m'
      with More -> read_more (); wrap f n in
    let rec aux n g res : token list * int =
      match g with
      | Item (_,f) ->
          let t, n = wrap f n in
          t :: res, n
      | Opt g ->
          (try let res', n = aux n g [] in Top (List.rev res') :: res, n
          with Err _ -> Top [] :: res, n)
      | Alt gl ->
          let rec fst = function
            | [] -> raise (Err ("No more alternatives for: "^cut_after !s n))
            | g :: gl ->
               try aux n g res
               with Err s -> fst gl in
          fst gl
      | Seq gl ->
          let rec all (res,n) = function
            | [] -> res, n
            | g :: gl -> all (aux n g res) gl in
          all (res,n) gl in
    let res, n = aux 0 g [] in
    s := cut_after !s n;
    List.rev res

  let clean s = Str.global_replace (Str.regexp "\n") "\\n" s

  let rec print g =
    match g with
    | Item (s,_) -> Printf.sprintf " %s " (clean s)
    | Opt g -> Printf.sprintf "[%s]" (print g)
    | Alt gs -> Printf.sprintf "(%s)" (String.concat "\n|" (List.map print gs))
    | Seq gs -> String.concat " " (List.map print gs)

  let rec print_toklist = function
    | [] -> ""
    | Tok(k,v) :: rest when k = v -> clean k ^ " " ^ print_toklist rest
    | Tok(k,v) :: rest -> clean k ^ " = \"" ^ clean v ^ "\" " ^ print_toklist rest
    | Top l :: rest -> print_toklist l ^ " " ^ print_toklist rest

end

let ids = ref []
let store_id s = function
  | Interface.Fail (_,_,s) -> prerr_endline s; exit 1
  | Interface.Good (id, _) -> ids := (s,id) :: !ids
let rec erase_ids id = function
  | Interface.Fail (_,_,s) -> prerr_endline s; exit 1
  | Interface.Good (Util.Inl ()) ->
      let rec aux () =
        match !ids with
        | [] -> ids := []
        | (_, x) :: rest when Stateid.equal x id -> ()
        | _ :: rest -> ids := rest; aux () in
      aux ()
  | Interface.Good (Util.Inr _) ->
      prerr_endline "focusing not supported by fake ide";
      exit 1
let curid () = match !ids with (_,x) :: _ -> x | _ -> Stateid.initial
let get_id id =
  try List.assoc id !ids
  with Not_found -> prerr_endline ("No state is named " ^ id); exit 1

let eid = ref 0
let edit () = incr eid; !eid

let eval_print l coq =
  let open Parser in
(*   prerr_endline ("Interpreting: " ^ print_toklist l); *)
  match l with
  | [ Tok(_,"ADD"); Top []; Tok(_,phrase) ] ->
      store_id ""
        (base_eval_call (Serialize.add ((phrase,edit()),(curid(),true))) coq)
  | [ Tok(_,"ADD"); Top [Tok(_,id)]; Tok(_,phrase) ] ->
      store_id id
        (base_eval_call (Serialize.add ((phrase,edit()),(curid(),true))) coq)
  | [ Tok(_,"EDIT_AT"); Tok(_,id) ] ->
      erase_ids (get_id id)
        (base_eval_call (Serialize.edit_at (get_id id)) coq)
  | [ Tok(_,"QUERY"); Top []; Tok(_,phrase) ] ->
      eval_call (Serialize.query (phrase,curid())) coq
  | [ Tok(_,"QUERY"); Top [Tok(_,id)]; Tok(_,phrase) ] ->
      eval_call (Serialize.query (phrase,get_id id)) coq
  | Tok("#[^\n]*",_) :: _  -> ()
  | _ ->
     prerr_endline "syntax error";
     exit 1

let grammar =
  let open Parser in
  let id = "[a-zA-Z_][a-zA-Z0-9_]*" in
  let eat_phrase = eat_balanced '{' in
  Alt
    [ Seq [Item (eat_rex "ADD"); Opt (Item (eat_rex id)); Item eat_phrase]
    ; Seq [Item (eat_rex "EDIT_AT"); Item (eat_rex id)]
    ; Seq [Item (eat_rex "QUERY"); Opt (Item (eat_rex id)); Item eat_phrase]
    ; Seq [Item (eat_rex "#[^\n]*")]
    ]

let read_command () = Parser.parse grammar

let usage () =
  Printf.printf
    "A fake coqide process talking to a coqtop -ideslave.\n\
     Usage: %s [<coqtop>]\n\
     Input syntax is the following:\n%s\n"
     (Filename.basename Sys.argv.(0))
     (Parser.print grammar);
  exit 1

let main =
  Sys.set_signal Sys.sigpipe
    (Sys.Signal_handle
       (fun _ -> prerr_endline "Broken Pipe (coqtop died ?)"; exit 1));
  let coqtop_name = match Array.length Sys.argv with
    | 1 -> "coqtop"
    | 2 when Sys.argv.(1) <> "-help" -> Sys.argv.(1)
    | _ -> usage ()
  in
  let coqtop =
    let (cin, cout) = Unix.open_process (coqtop_name^" -ideslave") in
    let ip = Xml_parser.make (Xml_parser.SChannel cin) in
    let op = Xml_printer.make (Xml_printer.TChannel cout) in
    let () = Xml_parser.check_eof ip false in
    {
      xml_printer = op;
      xml_parser = ip;
    }
  in
  (match base_eval_call ~print:false (Serialize.init ()) coqtop with
  | Interface.Good id -> ids := ["initial",id]
  | Interface.Fail _ -> assert false);
  while true do
    let l = try read_command () with End_of_file -> 
      match base_eval_call ~print:false (Serialize.status true) coqtop with
      | Interface.Good _ -> exit 0
      | Interface.Fail _ -> exit 1
    in
    try eval_print l coqtop
    with
      | Comment -> ()
      | e ->
	prerr_endline ("Uncaught exception " ^ Printexc.to_string e); exit 1
  done
