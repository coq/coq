(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Xml_datatype

type 'annotation located = {
  annotation : 'annotation option;
  startpos   : int;
  endpos     : int
}

let rich_pp annotate ppcmds =
  (** First, we use Format to introduce tags inside
      the pretty-printed document.

      Each inserted tag is a fresh index that we keep in sync with the contents
      of annotations.
  *)
  let annotations = ref [] in
  let index = ref (-1) in
  let pp_tag obj =
    let () = incr index in
    let () = annotations := obj :: !annotations in
    string_of_int !index
  in

  let tagged_pp = Format.(

    (** Warning: The following instructions are valid only if
        [str_formatter] is not used for another purpose in
        Pp.pp_with. *)

    let ft = str_formatter in

    (** We reuse {!Format} standard way of producing tags
        inside pretty-printing. *)
    pp_set_tags ft true;

    (** The whole output must be a valid document. To that
        end, we nest the document inside a tag named <pp>. *)
    pp_open_tag ft "pp";

    (** XML ignores spaces. The problem is that our pretty-printings
        are based on spaces to indent. To solve that problem, we
        systematically output non-breakable spaces, which are properly
        honored by XML.

        To do so, we reconfigure the [str_formatter] temporarily by
        hijacking the function that output spaces. *)
    let out, flush, newline, std_spaces =
      pp_get_all_formatter_output_functions ft ()
    in
    let set = pp_set_all_formatter_output_functions ft ~out ~flush ~newline in
    set ~spaces:(fun k ->
      for i = 0 to k - 1 do
        Buffer.add_string stdbuf "&nbsp;"
      done
    );

    (** Some characters must be escaped in XML. This is done by the
        following rewriting of the strings held by pretty-printing
        commands. *)
    Pp.(pp_with ~pp_tag ft (rewrite Xml_printer.pcdata_to_string ppcmds));

    (** Insert </pp>. *)
    pp_close_tag ft ();

    (** Get the final string. *)
    let output = flush_str_formatter () in

    (** Finalize by restoring the state of the [str_formatter] and the
        default behavior of Format. By the way, there may be a bug here:
        there is no {!Format.pp_get_tags} and therefore if the tags flags
        was already set to true before executing this piece of code, the
        state of Format is not restored. *)
    set ~spaces:std_spaces;
    pp_set_tags ft false;
    output
  )
  in
  (** Second, we retrieve the final function that relates
      each tag to an annotation. *)
  let objs = CArray.rev_of_list !annotations in
  let get index = annotate objs.(index) in

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


