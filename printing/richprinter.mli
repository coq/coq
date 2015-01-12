(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** This module provides an entry point to "rich" pretty-printers that
    produce pretty-printing as done by {!Printer} but with additional
    annotations represented as a semi-structured document.

    To understand what are these annotations and how they are represented
    as standard XML attributes, please refer to {!Ppannotation}.

    In addition to these annotations, each node of the semi-structured
    document contains a [startpos] and an [endpos] attribute that
    relate this node to the raw pretty-printing.
    Please refer to {!Richpp} for more details. *)

(** A rich pretty-print is composed of: *)
type rich_pp =
    (** - a raw pretty-print ; *)
    string

    (** - a generalized semi-structured document whose attributes are
        annotations ; *)
    * Ppannotation.t Richpp.located Xml_datatype.gxml

    (** - an XML document, representing annotations as usual textual
        XML attributes. *)
    * Xml_datatype.xml

(** [richpp_vernac phrase] produces a rich pretty-printing of [phrase]. *)
val richpp_vernac : Vernacexpr.vernac_expr -> rich_pp

(** [richpp_constr constr] produces a rich pretty-printing of [constr]. *)
val richpp_constr : Constrexpr.constr_expr -> rich_pp

(** [richpp_tactic constr] produces a rich pretty-printing of [tactic]. *)
val richpp_tactic : Environ.env -> Tacexpr.tactic_expr -> rich_pp
