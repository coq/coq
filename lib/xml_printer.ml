(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Xml_datatype

type xml = Xml_datatype.xml

type target = TChannel of out_channel | TBuffer of Buffer.t

type t = target

let make x = x

let buffer_pcdata tmp text =
  let output = Buffer.add_string tmp in
  let output' = Buffer.add_char tmp in
  let l = String.length text in
  for p = 0 to l-1 do
    match text.[p] with
      | ' ' -> output "&nbsp;";
      | '>' -> output "&gt;"
      | '<' -> output "&lt;"
      | '&' ->
        if p < l - 1 && text.[p + 1] = '#' then
          output' '&'
        else
          output "&amp;"
      | '\'' -> output "&apos;"
      | '"' -> output "&quot;"
      | c -> output' c
  done

let buffer_attr tmp (n,v) =
  let output = Buffer.add_string tmp in
  let output' = Buffer.add_char tmp in
  output' ' ';
  output n;
  output "=\"";
  let l = String.length v in
  for p = 0 to l - 1 do
    match v.[p] with
      | '\\' -> output "\\\\"
      | '"' -> output "\\\""
      | c -> output' c
  done;
  output' '"'

let to_buffer tmp x =
  let pcdata = ref false in
  let output = Buffer.add_string tmp in
  let output' = Buffer.add_char tmp in
  let rec loop = function
    | Element (tag,alist,[]) ->
      output' '<';
      output tag;
      List.iter (buffer_attr tmp) alist;
      output "/>";
      pcdata := false;
    | Element (tag,alist,l) ->
      output' '<';
      output tag;
      List.iter (buffer_attr tmp) alist;
      output' '>';
      pcdata := false;
      List.iter loop l;
      output "</";
      output tag;
      output' '>';
      pcdata := false;
    | PCData text ->
      if !pcdata then output' ' ';
      buffer_pcdata tmp text;
      pcdata := true;
  in
  loop x

let pcdata_to_string s =
  let b = Buffer.create 13 in
  buffer_pcdata b s;
  Buffer.contents b

let to_string x =
  let b = Buffer.create 200 in
  to_buffer b x;
  Buffer.contents b

let to_string_fmt x =
  let tmp = Buffer.create 200 in
  let output = Buffer.add_string tmp in
  let output' = Buffer.add_char tmp in
  let rec loop ?(newl=false) tab = function
    | Element (tag, alist, []) ->
      output tab;
      output' '<';
      output tag;
      List.iter (buffer_attr tmp) alist;
      output "/>";
      if newl then output' '\n';
    | Element (tag, alist, [PCData text]) ->
      output tab;
      output' '<';
      output tag;
      List.iter (buffer_attr tmp) alist;
      output ">";
      buffer_pcdata tmp text;
      output "</";
      output tag;
      output' '>';
      if newl then output' '\n';
    | Element (tag, alist, l) ->
      output tab;
      output' '<';
      output tag;
      List.iter (buffer_attr tmp) alist;
      output ">\n";
      List.iter (loop ~newl:true (tab^"  ")) l;
      output tab;
      output "</";
      output tag;
      output' '>';
      if newl then output' '\n';
    | PCData text ->
      buffer_pcdata tmp text;
      if newl then output' '\n';
  in
  loop "" x;
  Buffer.contents tmp

let print t xml =
  let tmp, flush = match t with
    | TChannel oc ->
      let b = Buffer.create 200 in
      b, (fun () -> Buffer.output_buffer oc b; flush oc)
    | TBuffer b ->
      b, (fun () -> ())
  in
  to_buffer tmp xml;
  flush ()
