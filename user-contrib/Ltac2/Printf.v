(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Ltac2.Message.

(** This file defines a printf notation for easiness of writing messages *)

(**

  The built-in "format" notation scope can be used to create well-typed variadic
  printing commands following a printf-like syntax. The "format" scope parses
  quoted strings which contain either raw string data or printing
  specifications. Raw strings will be output verbatim as if they were passed
  to Ltac2.Message.of_string.

  Printing specifications are of the form

  << '%' type >>

  where the type value defines which kind of arguments will be accepted and
  how they will be printed. They can take the following values.

  - << i >>: takes an argument of type int and behaves as Message.of_int
  - << I >>: takes an argument of type ident and behaves as Message.of_ident
  - << s >>: takes an argument of type string and behaves as Message.of_string
  - << t >>: takes an argument of type constr and behaves as Message.of_constr
  - << a >>: takes two arguments << f >> of type << (unit -> 'a -> message) >>
             and << x >> of type << 'a >> and behaves as << f () x >>
  - << % >>: outputs << % >> verbatim

  TODO: add printing modifiers.

*)

Ltac2 printf fmt := Format.kfprintf print fmt.
Ltac2 fprintf fmt := Format.kfprintf (fun x => x) fmt.

(** The two following notations are made available when this module is imported.

    - printf will parse a format and generate a function taking the
      corresponding arguments ant printing the resulting message as per
      Message.print. In particular when fully applied it has type unit.
    - fprintf behaves similarly but return the message as a value instead of
      printing it.

*)

Ltac2 Notation "printf" fmt(format) := printf fmt.
Ltac2 Notation "fprintf" fmt(format) := fprintf fmt.
