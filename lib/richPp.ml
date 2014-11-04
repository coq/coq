(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2014     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Xml_datatype

type index = Format.tag

type 'annotation located = {
  annotation : 'annotation option;
  startpos   : int;
  endpos     : int
}

module Indexer (Annotation : sig type t end) = struct

  let annotations : Annotation.t list ref = ref []

  let index =
    let count = ref (-1) in
    fun annotation ->
      incr count;
      annotations := annotation :: !annotations;
      string_of_int !count

  let get_annotations () =
    let annotations = Array.of_list (List.rev !annotations) in
    fun index -> annotations.(int_of_string index)

end

let rich_pp get_annotations ppcmds =
  (** First, we use Format to introduce tags inside
      the pretty-printed document.

      Each inserted tag is an index to an annotation.
  *)
  let tagged_pp = Format.(
    (** Warning: The following instructions are valid only if
        [str_formatter] is not used for another purpose in
        Pp.pp_with. *)
    let ft = str_formatter in
    pp_set_tags ft true;
    pp_open_tag ft "pp";
    let fof = pp_get_formatter_out_functions ft () in
    pp_set_formatter_out_functions ft { fof with
      out_spaces = fun k ->
        for i = 0 to k - 1 do
          Buffer.add_string stdbuf "&nbsp;"
        done
    };
    Pp.(pp_with ft (rewrite Xml_printer.pcdata_to_string (ppcmds ())));
    pp_close_tag ft ();
    let output = flush_str_formatter () in
    pp_set_formatter_out_functions ft fof;
    pp_set_tags ft false;
    output
  )
  in
  (** Second, we retrieve the final function that relates
      each tag to an annotation. *)
  let get = get_annotations () in

  (** Third, we parse the resulting string. It is a valid XML
      document (in the sense of Xml_parser). As blanks are
      meaningful we deactivate canonicalization in the XML
      parser. *)
  let xml_pp =
    try
      Xml_parser.(parse ~do_not_canonicalize:true (make (SString tagged_pp)))
    with Xml_parser.Error e ->
      Printf.eprintf
        "Broken invariant (RichPp): \n\
         The output semi-structured pretty-printing is ill-formed.\n\
         Please report.\n\
         %s"
        (Xml_parser.error e);
      exit 1
  in

  (** Fourth, the low-level XML is turned into a high-level
      semi-structured document that contains a located annotation in
      every node. During the traversal of the low-level XML document,
      we build a raw string representation of the pretty-print. *)
  let rec node buffer = function
    | Element (index, [], cs) ->
      let startpos, endpos, cs = children buffer cs in
      let annotation = try Some (get index) with _ -> None in
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
  let pp_buffer = Buffer.create 13 in
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


