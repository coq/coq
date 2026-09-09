(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Support for the [Printing Reversible Up To ...] flags: when one of
    them is set, terms are printed in a form whose reparsing is checked
    to produce a term equal to the original one, up to the equivalence
    selected by the flag. If the check fails, printing options
    (coercions, implicit arguments, notations off, universes,
    parentheses, and finally all raw printing options) are
    progressively turned on until the printed form passes the check;
    if no form does, the most explicit form is printed and a
    [reversible-printing] warning is emitted. *)

(** Whether the printed expression stands for a term or a type, which
    determines how its reparsing is elaborated. *)
type kind = Term | Type

(** [checked_extern ~flags ~extern ~kind env sigma c] returns the
    externalization of [c] ([extern] is expected to externalize [c]
    with the printing flags it receives), together with the printing
    flags that were used to produce it, to be used for printing it.
    When no [Printing Reversible] flag is set, this is just
    [flags, extern ~flags]. *)
val checked_extern :
  flags:PrintingFlags.t ->
  extern:(flags:PrintingFlags.t -> Constrexpr.constr_expr) ->
  kind:kind -> Environ.env -> Evd.evar_map -> EConstr.constr ->
  PrintingFlags.t * Constrexpr.constr_expr
