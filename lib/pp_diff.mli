(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(**
Computes the differences between 2 Pp's and adds additional tags to a Pp
to highlight them.  Strings are split into tokens using the Coq lexer,
then the lists of tokens are diffed using the Myers algorithm.  A fixup routine,
shorten_diff_span, shortens the span of the diff result in some cases.

Highlights use 4 tags to specify the color and underline/strikeout.  These are
"diffs.added", "diffs.removed", "diffs.added.bg" and "diffs.removed.bg".  The
first two are for added or removed text; the last two are for unmodified parts
of a modified item.  Diffs that span multiple strings in the Pp are tagged with
"start.diff.*" and "end.diff.*", but only on the first and last strings of the span.

If the inputs are not acceptable to the lexer, break the strings into
lists of tokens and call diff_strs, then add_diff_tags with a Pp.t that matches
the input lists of strings.  Tokens that the lexer doesn't return exactly as they
appeared in the input will raise an exception in add_diff_tags (e.g. comments
and quoted strings).  Fixing that requires tweaking the lexer.

Limitations/Possible enhancements:

- Make diff_pp immune to unlexable strings by adding a flag to the lexer.
*)

(** Compute the diff between two Pp.t structures and return
versions of each with diffs highlighted as (old, new) *)
val diff_pp : ?tokenize_string:(string -> string list) -> Pp.t -> Pp.t -> Pp.t * Pp.t

(** Compute the diff between two Pp.t structures and return
a highlighted Pp.t.  If [show_removed] is true, show separate lines for
removals and additions, otherwise only show additions *)
val diff_pp_combined : ?tokenize_string:(string -> string list) -> ?show_removed:bool -> Pp.t -> Pp.t -> Pp.t

(** Raised if the diff fails *)
exception Diff_Failure of string

module StringDiff :
sig
  type elem = String.t
  type t = elem array
end

type diff_type =
  [ `Removed
  | `Added
  | `Common
  ]

type diff_list = StringDiff.elem Diff2.edit list

(** Compute the difference between 2 strings in terms of tokens, using the
lexer to identify tokens.

If the strings are not lexable, this routine will raise Diff_Failure.
(I expect to modify the lexer soon so this won't happen.)

Therefore you should catch any exceptions.  The workaround for now is for the
caller to tokenize the strings itself and then call diff_strs.
*)
val diff_str : ?tokenize_string:(string -> string list) -> string -> string -> StringDiff.elem Diff2.edit list

(** Compute the differences between 2 lists of strings, treating the strings
in the lists as indivisible units.
*)
val diff_strs : StringDiff.t -> StringDiff.t -> StringDiff.elem Diff2.edit list

(** Generate a new Pp that adds tags marking diffs to a Pp structure:
which: either `Added or `Removed, indicates which type of diffs to add
pp: the original structure. For `Added, must be the new pp passed to diff_pp
  For `Removed, must be the old pp passed to diff_pp.  Passing the wrong one
  will likely raise Diff_Failure.
diffs: the diff list returned by diff_pp

Diffs of single strings in the Pp are tagged with "diff.added" or "diff.removed".
Diffs that span multiple strings in the Pp are tagged with "start.diff.*" or
"end.diff.*", but only on the first and last strings of the span.

Ppcmd_strings will be split into multiple Ppcmd_strings if a diff starts or ends
in the middle of the string.  Whitespace just before or just after a diff will
not be part of the highlight.

Prexisting tags in pp may contain only a single Ppcmd_string.  Those tags will be
placed inside the diff tags to ensure proper nesting of tags within spans of
"start.diff.*" ... "end.diff.*".

Under some  "impossible" conditions, this routine may raise Diff_Failure.
If you want to make your call especially bulletproof, catch this
exception, print a user-visible message, then recall this routine with
the first argument set to None, which will skip the diff.
*)
val add_diff_tags : diff_type -> Pp.t -> StringDiff.elem Diff2.edit list -> Pp.t

(** Returns a boolean pair (added, removed) for [diffs] where a true value
indicates that something was added/removed in the diffs.
*)
val has_changes : diff_list -> bool * bool

val get_dinfo : StringDiff.elem Diff2.edit -> diff_type * string

(** Returns a modified [pp] with the background highlighted with
"start.<diff_tag>.bg" and "end.<diff_tag>.bg" tags at the beginning
and end of the returned Pp.t
*)
val wrap_in_bg : string -> Pp.t -> Pp.t

(** Displays the diffs to a printable format for debugging *)
val string_of_diffs : diff_list -> string
