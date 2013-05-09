(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

type xml = Xml_datatype.xml =
        | Element of (string * (string * string) list * xml list)
        | PCData of string

type target = TChannel of out_channel | TBuffer of Buffer.t

type t = target

let make x = x

let buffer_pcdata tmp text =
	let l = String.length text in
	for p = 0 to l-1 do 
		match text.[p] with
		| '>' -> Buffer.add_string tmp "&gt;"
		| '<' -> Buffer.add_string tmp "&lt;"
		| '&' ->
			if p < l-1 && text.[p+1] = '#' then
				Buffer.add_char tmp '&'
			else
				Buffer.add_string tmp "&amp;"
		| '\'' -> Buffer.add_string tmp "&apos;"
		| '"' -> Buffer.add_string tmp "&quot;"
		| c -> Buffer.add_char tmp c
	done

let buffer_attr tmp (n,v) =
	Buffer.add_char tmp ' ';
	Buffer.add_string tmp n;
	Buffer.add_string tmp "=\"";
	let l = String.length v in
	for p = 0 to l-1 do
		match v.[p] with
		| '\\' -> Buffer.add_string tmp "\\\\"
		| '"' -> Buffer.add_string tmp "\\\""
		| c -> Buffer.add_char tmp c
	done;
	Buffer.add_char tmp '"'

let to_buffer tmp x = 
	let pcdata = ref false in
	let rec loop = function
		| Element (tag,alist,[]) ->
			Buffer.add_char tmp '<';
			Buffer.add_string tmp tag;
			List.iter (buffer_attr tmp) alist;
			Buffer.add_string tmp "/>";
			pcdata := false;
		| Element (tag,alist,l) ->
			Buffer.add_char tmp '<';
			Buffer.add_string tmp tag;
			List.iter (buffer_attr tmp) alist;
			Buffer.add_char tmp '>';
			pcdata := false;
			List.iter loop l;
			Buffer.add_string tmp "</";
			Buffer.add_string tmp tag;
			Buffer.add_char tmp '>';
			pcdata := false;
		| PCData text ->
			if !pcdata then Buffer.add_char tmp ' ';
			buffer_pcdata tmp text;
			pcdata := true;
	in
	loop x

let to_string x =
  let b = Buffer.create 200 in
  to_buffer b x;
  Buffer.contents b

let to_string_fmt x =
        let tmp = Buffer.create 200 in
	let rec loop ?(newl=false) tab = function
		| Element (tag,alist,[]) ->
			Buffer.add_string tmp tab;
			Buffer.add_char tmp '<';
			Buffer.add_string tmp tag;
			List.iter (buffer_attr tmp) alist;
			Buffer.add_string tmp "/>";
			if newl then Buffer.add_char tmp '\n';
		| Element (tag,alist,[PCData text]) ->
			Buffer.add_string tmp tab;
			Buffer.add_char tmp '<';
			Buffer.add_string tmp tag;
			List.iter (buffer_attr tmp) alist;
			Buffer.add_string tmp ">";
			buffer_pcdata tmp text;
			Buffer.add_string tmp "</";
			Buffer.add_string tmp tag;
			Buffer.add_char tmp '>';
			if newl then Buffer.add_char tmp '\n';
		| Element (tag,alist,l) ->
			Buffer.add_string tmp tab;
			Buffer.add_char tmp '<';
			Buffer.add_string tmp tag;
			List.iter (buffer_attr tmp) alist;
			Buffer.add_string tmp ">\n";
			List.iter (loop ~newl:true (tab^"  ")) l;
			Buffer.add_string tmp tab;
			Buffer.add_string tmp "</";
			Buffer.add_string tmp tag;
			Buffer.add_char tmp '>';
			if newl then Buffer.add_char tmp '\n';
		| PCData text ->
			buffer_pcdata tmp text;
			if newl then Buffer.add_char tmp '\n';
	in
	loop "" x;
	Buffer.contents tmp

let print t xml =
  let tmp, flush = match t with
    | TChannel oc ->
        let b = Buffer.create 200 in
        b, (fun () -> Buffer.output_buffer oc b; flush oc)
    | TBuffer b -> b, (fun () -> ()) in
  to_buffer tmp xml;
  flush ()
;;
