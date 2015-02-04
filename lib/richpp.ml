(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util
open Xml_datatype

type 'annotation located = {
  annotation : 'annotation option;
  startpos   : int;
  endpos     : int
}

type context =
| Leaf
| Node of string * xml list * context

let rich_pp annotate ppcmds =
  (** First, we use Format to introduce tags inside the pretty-printed document.
      Each inserted tag is a fresh index that we keep in sync with the contents
      of annotations.

      We build an XML tree on the fly, by plugging ourselves in Format tag
      marking functions. As those functions are called when actually writing to
      the device, the resulting tree is correct.
  *)
  let annotations = ref [] in
  let index = ref (-1) in
  let pp_tag obj =
    let () = incr index in
    let () = annotations := obj :: !annotations in
    string_of_int !index
  in

  let pp_buffer = Buffer.create 13 in

  let push_pcdata context =
    (** Push the optional PCData on the above node *)
    if (Buffer.length pp_buffer = 0) then ()
    else match !context with
    | Leaf -> assert false
    | Node (node, child, ctx) ->
      let data = Buffer.contents pp_buffer in
      let () = Buffer.clear pp_buffer in
      context := Node (node, PCData data :: child, ctx)
  in

  let open_xml_tag context tag =
    let () = push_pcdata context in
    context := Node (tag, [], !context)
  in

  let close_xml_tag context tag =
    let () = push_pcdata context in
    match !context with
    | Leaf -> assert false
    | Node (node, child, ctx) ->
      let () = assert (String.equal tag node) in
      let xml = Element (node, [], List.rev child) in
      match ctx with
      | Leaf ->
        (** Final node: we keep the result in a dummy context *)
        context := Node ("", [xml], Leaf)
      | Node (node, child, ctx) ->
        context := Node (node, xml :: child, ctx)
  in

  let xml_pp = Format.(

    let ft = formatter_of_buffer pp_buffer in

    let context = ref Leaf in

    let tag_functions = {
      mark_open_tag = (fun tag -> let () = open_xml_tag context tag in "");
      mark_close_tag = (fun tag -> let () = close_xml_tag context tag in "");
      print_open_tag = ignore;
      print_close_tag = ignore;
    } in

    pp_set_formatter_tag_functions ft tag_functions;
    pp_set_mark_tags ft true;

    (** The whole output must be a valid document. To that
        end, we nest the document inside <pp> tags. *)
    pp_open_tag ft "pp";
    Pp.(pp_with ~pp_tag ft ppcmds);
    pp_close_tag ft ();

    (** Get the resulting XML tree. *)
    let () = pp_print_flush ft () in
    let () = assert (Buffer.length pp_buffer = 0) in
    match !context with
    | Node ("", [xml], Leaf) -> xml
    | _ -> assert false
  )
  in
  (** Second, we retrieve the final function that relates
      each tag to an annotation. *)
  let objs = CArray.rev_of_list !annotations in
  let get index = annotate objs.(index) in

  (** Third, the low-level XML is turned into a high-level
      semi-structured document that contains a located annotation in
      every node. During the traversal of the low-level XML document,
      we build a raw string representation of the pretty-print. *)
  let rec node buffer = function
    | Element (index, [], cs) ->
      let startpos, endpos, cs = children buffer cs in
      let annotation = try get (int_of_string index) with _ -> None in
      (Element (index, { annotation; startpos; endpos }, cs), endpos)

    | PCData s ->
      Buffer.add_string buffer s;
      (PCData s, Buffer.length buffer)

    | _ ->
      assert false (* Because of the form of XML produced by Format. *)

  and children buffer cs =
    let startpos   = Buffer.length buffer in
    let cs, endpos =
      List.fold_left (fun (cs, endpos) c ->
        let c, endpos = node buffer c in
        (c :: cs, endpos)
      ) ([], startpos) cs
    in
    (startpos, endpos, List.rev cs)
  in
  let xml, _ = node pp_buffer xml_pp in

  (** We return the raw pretty-printing and its annotations tree. *)
  (Buffer.contents pp_buffer, xml)

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


