(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Xml_datatype

type xml = Xml_datatype.xml

type target = TChannel of out_channel | TBuffer of Buffer.t

type t = target

let make x = x

let buffer_pcdata tmp text =
  let puts = Buffer.add_string tmp in
  let putc = Buffer.add_char tmp in
  let l = String.length text in
  for p = 0 to l-1 do
    match text.[p] with
      | ' ' -> puts "&nbsp;";
      | '>' -> puts "&gt;"
      | '<' -> puts "&lt;"
      | '&' ->
        if p < l - 1 && text.[p + 1] = '#' then
          putc '&'
        else
          puts "&amp;"
      | '\'' -> puts "&apos;"
      | '"' -> puts "&quot;"
      | c -> putc c
  done

let buffer_attr tmp (n,v) =
  let puts = Buffer.add_string tmp in
  let putc = Buffer.add_char tmp in
  putc ' ';
  puts n;
  puts "=\"";
  let l = String.length v in
  for p = 0 to l - 1 do
    match v.[p] with
      | '\\' -> puts "\\\\"
      | '"' -> puts "\\\""
      | '<' -> puts "&lt;"
      | '&' -> puts "&amp;"
      | c -> putc c
  done;
  putc '"'

let to_buffer tmp x =
  let pcdata = ref false in
  let puts = Buffer.add_string tmp in
  let putc = Buffer.add_char tmp in
  let rec loop = function
    | Element (tag,alist,[]) ->
      putc '<';
      puts tag;
      List.iter (buffer_attr tmp) alist;
      puts "/>";
      pcdata := false;
    | Element (tag,alist,l) ->
      putc '<';
      puts tag;
      List.iter (buffer_attr tmp) alist;
      putc '>';
      pcdata := false;
      List.iter loop l;
      puts "</";
      puts tag;
      putc '>';
      pcdata := false;
    | PCData text ->
      if !pcdata then putc ' ';
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
  let puts = Buffer.add_string tmp in
  let putc = Buffer.add_char tmp in
  let rec loop ?(newl=false) tab = function
    | Element (tag, alist, []) ->
      puts tab;
      putc '<';
      puts tag;
      List.iter (buffer_attr tmp) alist;
      puts "/>";
      if newl then putc '\n';
    | Element (tag, alist, [PCData text]) ->
      puts tab;
      putc '<';
      puts tag;
      List.iter (buffer_attr tmp) alist;
      puts ">";
      buffer_pcdata tmp text;
      puts "</";
      puts tag;
      putc '>';
      if newl then putc '\n';
    | Element (tag, alist, l) ->
      puts tab;
      putc '<';
      puts tag;
      List.iter (buffer_attr tmp) alist;
      puts ">\n";
      List.iter (loop ~newl:true (tab^"  ")) l;
      puts tab;
      puts "</";
      puts tag;
      putc '>';
      if newl then putc '\n';
    | PCData text ->
      buffer_pcdata tmp text;
      if newl then putc '\n';
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
