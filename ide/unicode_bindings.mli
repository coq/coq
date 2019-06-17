(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)


(** Latex to unicode bindings.
    See also the documentation in doc/sphinx/practical-tools/coqide.rst.

    Text description of the unicode bindings, in a file with one item per line,
    each item consists of:
    - a leading backslahs
    - a ascii word next to it
    - a unicode word (or possibly a full sentence in-between doube-quotes,
     the sentence may include spaces and \n tokens),
    - optionally, an integer indicating the "priority" (lower is higher priority),
      technically the length of the prefix that suffices to obtain this word.
      Ex. if "\lambda" has priority 3, then "\lam" always decodes as "\lambda".

      \pi π
      \lambda λ 3
      \lambdas λs 4
      \lake Ο 2
      \lemma "Lemma foo : x. Proof. Qed." 1  ---currently not supported by the parser

    - In case of equality between two candidates (same ascii word, or same
      priorities for two words with similar prefix), the first binding is considered.

    - Note that if a same token is bound in several bindings file,
      the one with the lowest priority number will be considered.
      In case of same priority, the binding from the first file loaded
      is considered.
*)


(** [load_files] takes a list of filenames and load them as binding files.
    Filenames may include "default" and "local" as items. *)

val load_files : string list -> unit

(** [lookup] takes a prefix and returns the corresponding unicode value *)

val lookup : string -> string option
