(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Fake_ide : Simulate a [coqide] talking to a [coqidetop] *)

let error s =
  prerr_endline ("fake_id: error: "^s);
  exit 1

let pperr_endline pp = Format.eprintf "@[%a@]\n%!" Pp.pp_with pp

type coqtop = {
  xml_printer : Xml_printer.t;
  xml_parser : Xml_parser.t;
}

let print_error msg =
  Format.eprintf "fake_id: error: @[%a@]\n%!" Pp.pp_with msg

let base_eval_call ?(print=true) ?(fail=true) call coqtop =
  if print then prerr_endline (Xmlprotocol.pr_call call);
  let xml_query = Xmlprotocol.of_call call in
  Xml_printer.print coqtop.xml_printer xml_query;
  let rec loop () =
    let xml = Xml_parser.parse coqtop.xml_parser in
    if Xmlprotocol.is_feedback xml then
      loop ()
    else Xmlprotocol.to_answer call xml
  in
  let res = loop () in
  if print then prerr_endline (Xmlprotocol.pr_full_value call res);
  match res with
  | Interface.Fail (_,_,s) when fail -> print_error s; exit 1
  | Interface.Fail (_,_,s) as x      -> print_error s; x
  | x -> x

let eval_call c q = ignore(base_eval_call c q)

module Parser = struct (* {{{ *)

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

  let eat_blanks s = snd (eat_rex "[ \r\n\t]*") s

  let s = ref ""

  let parse g ic =
    let read_more () = s := !s ^ input_line ic ^ "\n" in
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
    | Item (s,_) -> Printf.sprintf "%s" (clean s)
    | Opt g -> Printf.sprintf "[%s]" (print g)
    | Alt gs -> Printf.sprintf "( %s )" (String.concat " | " (List.map print gs))
    | Seq gs -> String.concat " " (List.map print gs)

  let rec print_toklist = function
    | [] -> ""
    | Tok(k,v) :: rest when k = v -> clean k ^ " " ^ print_toklist rest
    | Tok(k,v) :: rest -> clean k ^ " = \"" ^ clean v ^ "\" " ^ print_toklist rest
    | Top l :: rest -> print_toklist l ^ " " ^ print_toklist rest

end (* }}} *)

type sentence = {
  name : string;
  text : string;
  edit_id : int;
}

let doc : sentence Document.document = Document.create ()

let tip_id () =
  try Document.tip doc
  with
  | Document.Empty -> Stateid.initial
  | Invalid_argument _ -> error "add_sentence on top of non assigned tip"

let add_sentence =
  let edit_id = ref 0 in
  fun ?(name="") text ->
    let tip_id = tip_id () in
    decr edit_id;
    Document.push doc { name; text; edit_id = !edit_id };
    !edit_id, tip_id

let print_document () =
  let ellipsize s =
          Str.global_replace (Str.regexp "^[\n ]*") ""
      (if String.length s > 20 then String.sub s 0 17 ^ "..."
       else s) in
  pperr_endline (
    (Document.print doc
      (fun b state_id { name; text } ->
        Pp.str (Printf.sprintf "%s[%10s, %3s] %s"
          (if b then "*" else " ")
          name
          (Stateid.to_string (Option.default Stateid.dummy state_id))
          (ellipsize text)))))

(* This module is the logic a GUI has to implement *)
module GUILogic = struct

  let after_add = function
    | Interface.Fail (_,_,s) -> print_error s; exit 1
    | Interface.Good (id, (Util.Inl (), _)) ->
        Document.assign_tip_id doc id
    | Interface.Good (id, (Util.Inr tip, _)) ->
        Document.assign_tip_id doc id;
        Document.unfocus doc;
        ignore(Document.cut_at doc tip);
        print_document ()
  
  let at id id' _ = Stateid.equal id' id
  
  let after_edit_at (id,need_unfocus) = function
    | Interface.Fail (_,_,s) -> print_error s; exit 1
    | Interface.Good (Util.Inl ()) ->
        if need_unfocus then Document.unfocus doc;
        ignore(Document.cut_at doc id);
        print_document ()
    | Interface.Good (Util.Inr (stop_id,(start_id,tip))) ->
        if need_unfocus then Document.unfocus doc;
        ignore(Document.cut_at doc tip);
        Document.focus doc ~cond_top:(at start_id) ~cond_bot:(at stop_id);
        ignore(Document.cut_at doc id);
        print_document ()
  
  let get_id_pred pred =
    try Document.find_id doc pred
    with Not_found -> error "No state found"

  let get_id id = get_id_pred (fun _ { name } -> name = id)
  
  let after_fail coq = function
    | Interface.Fail (safe_id,_,s) ->
        prerr_endline "The command failed as expected";
        let to_id, need_unfocus =
          get_id_pred (fun id _ -> Stateid.equal id safe_id) in
        after_edit_at (to_id, need_unfocus)
          (base_eval_call (Xmlprotocol.edit_at to_id) coq)
    | Interface.Good _ -> error "The command was expected to fail but did not"

end

open GUILogic

let eval_print l coq =
  let open Parser in
  let open Xmlprotocol in
  (* prerr_endline ("Interpreting: " ^ print_toklist l); *)
  match l with
  | [ Tok(_,"ADD"); Top []; Tok(_,phrase) ] ->
      let eid, tip = add_sentence phrase in
      after_add (base_eval_call (add ((phrase,eid),(tip,true))) coq)
  | [ Tok(_,"ADD"); Top [Tok(_,name)]; Tok(_,phrase) ] ->
      let eid, tip = add_sentence ~name phrase in
      after_add (base_eval_call (add ((phrase,eid),(tip,true))) coq)
  | [ Tok(_,"GOALS"); ] ->
      eval_call (goals ()) coq
  | [ Tok(_,"FAILGOALS"); ] ->
      after_fail coq (base_eval_call ~fail:false (goals ()) coq)
  | [ Tok(_,"EDIT_AT"); Tok(_,id) ] ->
      let to_id, need_unfocus = get_id id in
      after_edit_at (to_id, need_unfocus) (base_eval_call (edit_at to_id) coq)
  | [ Tok(_,"QUERY"); Top []; Tok(_,phrase) ] ->
      eval_call (query (0,(phrase,tip_id()))) coq
  | [ Tok(_,"QUERY"); Top [Tok(_,id)]; Tok(_,phrase) ] ->
      let to_id, _ = get_id id in
      eval_call (query (0,(phrase, to_id))) coq
  | [ Tok(_,"WAIT") ] ->
      eval_call (wait ()) coq
  | [ Tok(_,"JOIN") ] ->
      eval_call (status true) coq
  | [ Tok(_,"ASSERT"); Tok(_,"TIP"); Tok(_,id) ] ->
      let to_id, _ = get_id id in
      if not(Stateid.equal (Document.tip doc) to_id) then error "Wrong tip"
      else prerr_endline "Good tip"
  | Tok("#[^\n]*",_) :: _  -> ()
  | _ -> error "syntax error"

let grammar =
  let open Parser in
  let eat_id = eat_rex "[a-zA-Z_][a-zA-Z0-9_]*" in
  let eat_phrase = eat_balanced '{' in
  Alt
    [ Seq [Item (eat_rex "ADD"); Opt (Item eat_id); Item eat_phrase]
    ; Seq [Item (eat_rex "EDIT_AT"); Item eat_id]
    ; Seq [Item (eat_rex "QUERY"); Opt (Item eat_id); Item eat_phrase]
    ; Seq [Item (eat_rex "WAIT")]
    ; Seq [Item (eat_rex "JOIN")]
    ; Seq [Item (eat_rex "GOALS")]
    ; Seq [Item (eat_rex "FAILGOALS")]
    ; Seq [Item (eat_rex "ASSERT"); Item (eat_rex "TIP"); Item eat_id ]
    ; Item (eat_rex "#[^\n]*")
    ]

let read_command inc = Parser.parse grammar inc

let usage () =
  error (Printf.sprintf
    "A fake coqide process talking to a coqtop -toploop coqidetop.\n\
     Usage: %s (file|-) [<coqtop>]\n\
     Input syntax is the following:\n%s\n"
     (Filename.basename Sys.argv.(0))
     (Parser.print grammar))

module Coqide = Spawn.Sync ()

let main =
  if Sys.os_type = "Unix" then Sys.set_signal Sys.sigpipe
    (Sys.Signal_handle
       (fun _ -> prerr_endline "Broken Pipe (coqtop died ?)"; exit 1));
  let def_args = ["--xml_format=Ppcmds"] in
  let idetop_name = System.get_toplevel_path "coqidetop" in
  let coqtop_args, input_file = match Sys.argv with
    | [| _; f |] -> Array.of_list def_args, f
    | [| _; f; ct |] ->
        let ct = Str.split (Str.regexp " ") ct in
        Array.of_list (def_args @ ct), f
    | _ -> usage () in
  let inc = if input_file = "-" then stdin else open_in input_file in
  let coq =
    let _p, cin, cout = Coqide.spawn idetop_name coqtop_args in
    let ip = Xml_parser.make (Xml_parser.SChannel cin) in
    let op = Xml_printer.make (Xml_printer.TChannel cout) in
    Xml_parser.check_eof ip false;
    { xml_printer = op; xml_parser = ip } in
  let init () =
    match base_eval_call ~print:false (Xmlprotocol.init None) coq with
    | Interface.Good id ->
        let dir = Filename.dirname input_file in
        let phrase = Printf.sprintf "Add LoadPath \"%s\". " dir in
        let eid, tip = add_sentence ~name:"initial" phrase in
        after_add (base_eval_call (Xmlprotocol.add ((phrase,eid),(tip,true))) coq)
    | Interface.Fail _ -> error "init call failed" in
  let finish () =
    match base_eval_call (Xmlprotocol.status true) coq with
    | Interface.Good _ -> exit 0
    | Interface.Fail (_,_,s) -> print_error s; exit 1 in
  (* The main loop *)
  init ();
  while true do
    let cmd = try read_command inc with End_of_file -> finish () in
    try eval_print cmd coq
    with e -> error ("Uncaught exception " ^ Printexc.to_string e)
  done

(* vim:set foldmethod=marker: *)
