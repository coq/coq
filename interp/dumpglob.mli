(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** This file implements the Coq's [.glob] file format, which
   provides information about the objects that are defined and referenced
   from a Coq file.

   The [.glob] file format is notably used by [coqdoc] and [coq2html]
   to generate links and other documentation meta-data.

   Note that we consider this format a legacy one, and no stability
   guarantees are provided as of today, as we search to replace this
   format with a more structured and strongly-typed API.

   However, we do provide up to date documentation about the format of
   [.glob] files below.

*)

(** {2 The [.glob] file format}

   [.glob] files contain a header, and then a list of entries, with
  one line per entry.

  {3 [.glob] header }

  The header consists of two lines:

[DIGEST: %md5sum_of_file]
[F%modpath]

  where %modpath is the fully-qualified module name of the library that the
  [.glob] file refers to. [%md5sum_of_file] may be NO if [-dump-glob file] was used.

 {3 [.glob] entries }

  There are 2 kinds of [.glob] entries:

  - *definitions*: these entries correspond to definitions of inductives,
    functions, binders, notations. They are written as:

    [%kind %bc:%ec %secpath %name]

    where [%kind] is one of
    [{ax,def,coe,subclass,canonstruc,ex,scheme,proj,inst,meth,defax,prfax,thm,prim,class,var,indrec,rec,corec,ind,variant,coind,constr,not,binder,lib,mod,modtype}],
    meaning:
    + [ax] Axiom, Parameter or Variable(s), Hypothes{i,e}s, Context outside any section
    + [def] Definition
    + [coe] Coertion
    + [thm] Theorem
    + [subclass] Sub Class
    + [canonstruc] Canonical Declaration
    + [ex] Example
    + [scheme] Scheme
    + [class] Class declaration
    + [proj] Projection from a structure
    + [inst] Instance
    + [meth] Class Method
    + [defax] Definitional assumption
    + [prfax] Logical assumption
    + [prim] Primitive
    + [var] section Variable reference (Variable{,s}, Hypothes{i,e}s, Context)
    + [indrec] Inductive
    + [rec] Inductive  (variant)
    + [corec] Coinductive
    + [ind] Record
    + [variant] Record (variant)
    + [coind] Coinductive Record
    + [constr] Constructor
    + [not] Notation
    + [binder] Binder
    + [lib] Require
    + [mod] Module Reference (Import, Module start / end)
    + [modtype] Module Type

    [%bc] and [%ec] are respectively the start and end byte locations in the file (0-indexed), multiple entries can share the same [%bc] and [%ec]
    [%secpath] the section path (or [<>] if no section path) and [%name] the name of the
    defined object, or also [<>] in where no name applies.

    Section paths are ...

    + In the case of notations, [%name] is encoded as [:entry:scope:notation_key] where [_] is used to replace
      spaces in the notation key, [%entry] is left empty if the notation entry is [constr],
      and similarly [%scope] is empty if the corresponding notation has no associated scope.

    + For binding variables, [:number] is added to distinguish uniquely different binding variables of the same name in a file.

  - *references*: which identify the object a particular document piece of text points to;
    their format is:

    [R%bc:%ec %filepath %secpath %name %kind]

    where [%bc], [%ec], [%name], and [%kind] are as the above; [%filepath] contains the
    file module path the object that the references lives in, whereas [%name] may contain
    non-file non-directory module names.

*)

val start_dump_glob : vfile:string -> vofile:string -> unit
val end_dump_glob : unit -> unit

val dump : unit -> bool

type glob_output =
  | NoGlob
  | Feedback
  | MultFiles                   (* one glob file per .v file *)
  | File of string              (* Single file for all coqc arguments *)

(** [push_output o] temporarily overrides the output location to [o].
    The original output can be restored using [pop_output] *)
val push_output : glob_output -> unit

(** Restores the original output that was overridden by [push_output] *)
val pop_output : unit -> unit

(** Alias for [push_output NoGlob] *)
val pause : unit -> unit

(** Deprecated alias for [pop_output] *)
val continue : unit -> unit
[@@ocaml.deprecated "(8.13) Use pop_output"]

val with_glob_output : glob_output -> (unit -> 'a) -> unit -> 'a

val add_glob : ?loc:Loc.t -> Names.GlobRef.t -> unit
val add_glob_kn : ?loc:Loc.t -> Names.KerName.t -> unit

val dump_definition : Names.lident -> bool -> string -> unit
val dump_moddef : ?loc:Loc.t -> Names.ModPath.t -> string -> unit
val dump_modref  : ?loc:Loc.t -> Names.ModPath.t -> string -> unit
val dump_reference  : ?loc:Loc.t -> string -> string -> string -> unit
val dump_secvar : ?loc:Loc.t -> Names.Id.t -> unit
val dump_libref : ?loc:Loc.t -> Names.DirPath.t -> string -> unit
val dump_notation_location : (int * int) list -> Constrexpr.notation ->
  (Notation.notation_location * Notation_term.scope_name option) -> unit
val dump_binding : ?loc:Loc.t -> string -> unit
val dump_notation :
  Constrexpr.notation CAst.t ->
  Notation_term.scope_name option -> bool -> unit

val dump_constraint : Names.lname -> bool -> string -> unit

val dump_string : string -> unit

val type_of_global_ref : Names.GlobRef.t -> string

(** Registration of constant information *)
val add_constant_kind : Names.Constant.t -> Decls.logical_kind -> unit
val constant_kind : Names.Constant.t -> Decls.logical_kind
