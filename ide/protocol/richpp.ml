(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Xml_datatype

type 'annotation located = {
  annotation : 'annotation option;
  startpos   : int;
  endpos     : int
}

type 'a stack =
| Leaf
| Node of string * 'a located gxml list * int * 'a stack

type 'a context = {
  mutable stack : 'a stack;
  (** Pending opened nodes *)
  mutable offset : int;
  (** Quantity of characters printed so far *)
}

(** We use Format to introduce tags inside the pretty-printed document.
    Each inserted tag is a fresh index that we keep in sync with the contents
    of annotations.

    We build an XML tree on the fly, by plugging ourselves in Format tag
    marking functions. As those functions are called when actually writing to
    the device, the resulting tree is correct.
*)
let rich_pp width ppcmds =

  let context = {
    stack = Leaf;
    offset = 0;
  } in

  let pp_buffer = Buffer.create 180 in

  let push_pcdata () =
    (** Push the optional PCData on the above node *)
    let len = Buffer.length pp_buffer in
    if len = 0 then ()
    else match context.stack with
    | Leaf -> assert false
    | Node (node, child, pos, ctx) ->
      let data = Buffer.contents pp_buffer in
      let () = Buffer.clear pp_buffer in
      let () = context.stack <- Node (node, PCData data :: child, pos, ctx) in
      context.offset <- context.offset + len
  in

  let open_xml_tag tag =
    let () = push_pcdata () in
    context.stack <- Node (tag, [], context.offset, context.stack)
  in

  let close_xml_tag tag =
    let () = push_pcdata () in
    match context.stack with
    | Leaf -> assert false
    | Node (node, child, pos, ctx) ->
      let () = assert (String.equal tag node) in
      let annotation = {
        annotation = Some tag;
        startpos = pos;
        endpos = context.offset;
      } in
      let xml = Element (node, annotation, List.rev child) in
      match ctx with
      | Leaf ->
        (** Final node: we keep the result in a dummy context *)
        context.stack <- Node ("", [xml], 0, Leaf)
      | Node (node, child, pos, ctx) ->
        context.stack <- Node (node, xml :: child, pos, ctx)
  in

  let open Format in

  let ft = formatter_of_buffer pp_buffer in

  let tag_functions = {
    mark_open_tag = (fun tag -> let () = open_xml_tag tag in "");
    mark_close_tag = (fun tag -> let () = close_xml_tag tag in "");
    print_open_tag = ignore;
    print_close_tag = ignore;
  } in

  pp_set_formatter_tag_functions ft tag_functions;
  pp_set_mark_tags ft true;

  (* Setting the formatter *)
  pp_set_margin ft width;
  let m = max (64 * width / 100) (width-30) in
  pp_set_max_indent ft m;
  pp_set_max_boxes ft 50 ;
  pp_set_ellipsis_text ft "...";

  (** The whole output must be a valid document. To that
      end, we nest the document inside <pp> tags. *)
  pp_open_box ft 0;
  pp_open_tag ft "pp";
  Pp.(pp_with ft ppcmds);
  pp_close_tag ft ();
  pp_close_box ft ();

  (** Get the resulting XML tree. *)
  let () = pp_print_flush ft () in
  let () = assert (Buffer.length pp_buffer = 0) in
  match context.stack with
  | Node ("", [xml], 0, Leaf) -> xml
  | _ -> assert false


let annotations_positions xml =
  let rec node accu = function
    | Element (_, { annotation = Some annotation; startpos; endpos }, cs) ->
      children ((annotation, (startpos, endpos)) :: accu) cs
    | Element (_, _, cs) ->
      children accu cs
    | _ ->
      accu
  and children accu cs =
    List.fold_left node accu cs
  in
  node [] xml

let xml_of_rich_pp tag_of_annotation attributes_of_annotation xml =
  let rec node = function
    | Element (index, { annotation; startpos; endpos }, cs) ->
      let attributes =
        [ "startpos", string_of_int startpos;
          "endpos", string_of_int endpos
        ]
        @ (match annotation with
          | None -> []
          | Some annotation -> attributes_of_annotation annotation
        )
      in
      let tag =
        match annotation with
          | None -> index
          | Some annotation -> tag_of_annotation annotation
      in
      Element (tag, attributes, List.map node cs)
    | PCData s ->
      PCData s
  in
  node xml

type richpp = xml

let richpp_of_pp width pp =
  let rec drop = function
  | PCData s -> [PCData s]
  | Element (_, annotation, cs) ->
    let cs = List.concat (List.map drop cs) in
    match annotation.annotation with
    | None -> cs
    | Some s -> [Element (s, [], cs)]
  in
  let xml = rich_pp width pp in
  Element ("_", [], drop xml)
