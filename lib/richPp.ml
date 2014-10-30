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
  annotation : 'annotation;
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
  let tagged_pp =
    let b = Buffer.create 13 in
    Buffer.add_string b "<pp>";
    Format.set_tags true;
    Pp.pp_with (Format.formatter_of_buffer b) ppcmds;
    Format.set_tags false;
    Buffer.add_string b "</pp>";
    Buffer.contents b
  in

  (** Second, we retrieve the final function that relates
      each tag to an annotation. *)
  let get = get_annotations () in

  (** Third, we parse the resulting string. It is a valid XML
      document (in the sense of Xml_parser). *)
  let xml_pp = Xml_parser.(parse (make (SString tagged_pp))) in

  (** Fourth, the low-level XML is turned into a high-level
      semi-structured document that contains a located annotation in
      every node. During the traversal of the low-level XML document,
      we build a raw string representation of the pretty-print. *)
  let rec node buffer = function
    | Element (index, [], cs) ->
      let startpos, endpos, cs = children buffer cs in
      let annotation = get index in
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

  (** That's it. We return the raw pretty-printing and its annotations
      tree. *)
  (Buffer.contents pp_buffer, xml)

let annotations_positions xml =
  let rec node accu = function
    | Element (_, { annotation; startpos; endpos }, cs) ->
      children ((annotation, (startpos, endpos)) :: accu) cs
    | _ ->
      accu
  and children accu cs =
    List.fold_left node accu cs
  in
  node [] xml

let xml_of_rich_pp tag_of_annotation attributes_of_annotation xml =
  let rec node = function
    | Element (_, { annotation; startpos; endpos }, cs) ->
      let attributes =
        [ "startpos", string_of_int startpos;
          "endpos", string_of_int endpos
        ]
        @ attributes_of_annotation annotation
      in
      Element (tag_of_annotation annotation,
               attributes,
               List.map node cs)
    | PCData s ->
      PCData s
  in
  node xml


