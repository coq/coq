(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open CErrors
open Vernacexpr

type deprecation = { since : string option ; note : string option }

let mk_deprecation ?(since=None) ?(note=None) () =
  { since ; note }

type t = {
  locality : bool option;
  polymorphic : bool;
  template : bool option;
  program : bool;
  deprecated : deprecation option;
}

let mk_atts ?(locality=None) ?(polymorphic=false) ?(template=None) ?(program=false) ?(deprecated=None) () =
  { locality ; polymorphic ; program ; deprecated; template }

let attributes_of_flags f atts =
  let assert_empty k v =
    if v <> VernacFlagEmpty
    then user_err Pp.(str "Attribute " ++ str k ++ str " does not accept arguments")
  in
  List.fold_left
    (fun (polymorphism, atts) (k, v) ->
       match k with
       | "program" when not atts.program ->
         assert_empty k v;
         (polymorphism, { atts with program = true })
       | "program" ->
         user_err Pp.(str "Program mode specified twice")
       | "polymorphic" when polymorphism = None ->
         assert_empty k v;
         (Some true, atts)
       | "monomorphic" when polymorphism = None ->
         assert_empty k v;
         (Some false, atts)
       | ("polymorphic" | "monomorphic") ->
         user_err Pp.(str "Polymorphism specified twice")
       | "template" when atts.template = None ->
         assert_empty k v;
         polymorphism, { atts with template = Some true }
       | "notemplate" when atts.template = None ->
         assert_empty k v;
         polymorphism, { atts with template = Some false }
       | "template" | "notemplate" ->
         user_err Pp.(str "Templateness specified twice")
       | "local" when Option.is_empty atts.locality ->
         assert_empty k v;
         (polymorphism, { atts with locality = Some true })
       | "global" when Option.is_empty atts.locality ->
         assert_empty k v;
         (polymorphism, { atts with locality = Some false })
       | ("local" | "global") ->
         user_err Pp.(str "Locality specified twice")
       | "deprecated" when Option.is_empty atts.deprecated ->
           begin match v with
             | VernacFlagList [ "since", VernacFlagLeaf since ; "note", VernacFlagLeaf note ]
             | VernacFlagList [ "note", VernacFlagLeaf note ; "since", VernacFlagLeaf since ] ->
               let since = Some since and note = Some note in
               (polymorphism, { atts with deprecated = Some (mk_deprecation ~since ~note ()) })
             | VernacFlagList [ "since", VernacFlagLeaf since ] ->
               let since = Some since in
               (polymorphism, { atts with deprecated = Some (mk_deprecation ~since ()) })
             | VernacFlagList [ "note", VernacFlagLeaf note ] ->
               let note = Some note in
               (polymorphism, { atts with deprecated = Some (mk_deprecation ~note ()) })
             |  _ -> CErrors.user_err (Pp.str "Ill formed “deprecated” attribute")
           end
       | "deprecated" ->
         user_err Pp.(str "Deprecation specified twice")
       | _ -> user_err Pp.(str "Unknown attribute " ++ str k)
    )
    (None, atts)
    f
