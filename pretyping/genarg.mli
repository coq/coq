(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Generic arguments used by the extension mechanisms of several Rocq ASTs. *)

(** Generic arguments must be registered according to their usage:

    (raw level printers are always useful for clearer [-time] output, for beautify,
    and some other debug prints)

    - extensible constr syntax beyond notations (eg [ltac:()], [ltac2:()] and ltac2 [$x]).
      Such genargs appear in glob_term GGenarg and constrexpr CGenarg.
      They must be registered with [Genintern.register_intern0]
      and [GlobEnv.register_constr_interp0].

      The glob level may be kept through notations and other operations like Ltac definitions
      (eg [Ltac foo := exact ltac2:(foo)]) in which case [Gensubst.register_subst0]
      and a glob level printer are useful.

      Other useful registrations are
      - [Genintern.register_intern_pat] and [Patternops.register_interp_pat]
        to be used in tactic patterns.
      - [Genintern.register_ntn_subst0] to be used in notations
        (eg [Notation "foo" := ltac2:(foo)]).

      NB: only the base [ExtraArg] is allowed here.

    - tactic arguments to commands defined without depending on ltac_plugin
      (VernacProof, HintsExtern, Hint Rewrite, etc).

      Must be registered with [Genintern.register_intern0] and
      [Genintern.register_interp0].

      The glob level can be kept (currently with Hint Extern and Hint
      Rewrite) so [Gensubst.register_subst0] is also needed.

      Currently AFAICT this is just [Tacarg.wit_ltac].

      NB: only the base [ExtraArg] is allowed here.

    - vernac arguments, used by vernac extend. Usually declared in mlg
      using VERNAC ARGUMENT EXTEND then used in VERNAC EXTEND.

      With VERNAC ARGUMENT EXTEND the raw level printer is registered
      by including PRINTED BY.

      Must be registered with [Procq.register_grammar] (handled by
      VERNAC ARGUMENT EXTEND when declared that way) as vernac extend
      only gets the genarg as argument so must get the grammar from
      the registration.

      Unless combined with some other use, the glob and top levels will be empty
      (as in [vernac_genarg_type]).

    - Ltac tactic_extend arguments. Usually declared in mlg using ARGUMENT EXTEND
      then used in TACTIC EXTEND.

      Must be registered with [Genintern.register_intern0],
      [Gensubst.register_subst0] and [Genintern.register_interp0].

      Must be registered with [Procq.register_grammar] as tactic extend
      only gets the genarg as argument so must get the grammar from
      the registration.

      They must be associated with a [Geninterp.Val.tag] using [Geninterp.register_val0]
      (which creates a fresh tag if passed [None]).
      Note: although [Genintern.register_interp0] registers a producer
      of arbitrary [Geninterp.Val.t], tactic_extend requires them to be of the tag
      registered by [Geninterp.register_val0] to work properly.

      They should also have all printer levels registered with [Genprint.register_print0].

      All registrations are handled by the arguments to ARGUMENT EXTEND when declared that way.

      All of them can also be used as vernac_extend arguments since
      vernac_extend uses a subset of the registrations needed for tactic_extend.

    - some hack in Tacentries.ml_val_tactic_extend and its variant in
      Tac2core_ltac1 for Ltac1.lambda.
*)

(** The route of a generic argument, from parsing to evaluation.
In the following diagram, "object" can be ltac_expr, constr, tactic_value, etc.

{% \begin{verbatim} %}
             parsing          in_raw                            out_raw
   char stream ---> raw_object ---> raw_object generic_argument -------+
                          encapsulation                          decaps|
                                                                       |
                                                                       V
                                                                   raw_object
                                                                       |
                                                         globalization |
                                                                       V
                                                                   glob_object
                                                                       |
                                                                encaps |
                                                               in_glob |
                                                                       V
                                                           glob_object generic_argument
                                                                       |
          out                          in                     out_glob |
  object <--- object generic_argument <--- object <--- glob_object <---+
    |   decaps                       encaps      interp           decaps
    |
    V
effective use
{% \end{verbatim} %}

To distinguish between the uninterpreted, globalized and
interpreted worlds, we annotate the type [generic_argument] by a
phantom argument.

*)

(** {5 Generic types} *)

module ArgT :
sig
  type ('a, 'b, 'c) tag
  val eq : ('a1, 'b1, 'c1) tag -> ('a2, 'b2, 'c2) tag -> ('a1 * 'b1 * 'c1, 'a2 * 'b2 * 'c2) CSig.eq option
  val repr : ('a, 'b, 'c) tag -> string
  type any = Any : ('a, 'b, 'c) tag -> any
  val name : string -> any option
  val dump : unit -> (int * string) list
end

(** Generic types. The first parameter is the OCaml lowest level, the second one
    is the globalized level, and third one the internalized level. *)
type (_, _, _) genarg_type =
| ExtraArg : ('a, 'b, 'c) ArgT.tag -> ('a, 'b, 'c) genarg_type
| ListArg : ('a, 'b, 'c) genarg_type -> ('a list, 'b list, 'c list) genarg_type
| OptArg : ('a, 'b, 'c) genarg_type -> ('a option, 'b option, 'c option) genarg_type
| PairArg : ('a1, 'b1, 'c1) genarg_type * ('a2, 'b2, 'c2) genarg_type ->
  ('a1 * 'a2, 'b1 * 'b2, 'c1 * 'c2) genarg_type

type 'a uniform_genarg_type = ('a, 'a, 'a) genarg_type
(** Alias for concision when the three types agree. *)

type 'a vernac_genarg_type = ('a, Util.Empty.t, Util.Empty.t) genarg_type
(** Produced  by VERNAC ARGUMENT EXTEND *)

val make0 : string -> ('raw, 'glob, 'top) genarg_type
(** Create a new generic type of argument: force to associate
    unique ML types at each of the three levels. *)

val create_arg : string -> ('raw, 'glob, 'top) genarg_type
(** Alias for [make0]. *)

(** {5 Specialized types} *)

(** All of [rlevel], [glevel] and [tlevel] must be non convertible
    to ensure the injectivity of the GADT type inference. *)

type rlevel = [ `rlevel ]
type glevel = [ `glevel ]
type tlevel = [ `tlevel ]

(** Generic types at a fixed level. The first parameter embeds the OCaml type
    and the second one the level. *)
type (_, _) abstract_argument_type =
| Rawwit : ('a, 'b, 'c) genarg_type -> ('a, rlevel) abstract_argument_type
| Glbwit : ('a, 'b, 'c) genarg_type -> ('b, glevel) abstract_argument_type
| Topwit : ('a, 'b, 'c) genarg_type -> ('c, tlevel) abstract_argument_type

type 'a raw_abstract_argument_type = ('a, rlevel) abstract_argument_type
(** Specialized type at raw level. *)

type 'a glob_abstract_argument_type = ('a, glevel) abstract_argument_type
(** Specialized type at globalized level. *)

type 'a typed_abstract_argument_type = ('a, tlevel) abstract_argument_type
(** Specialized type at internalized level. *)

(** {6 Projections} *)

val rawwit : ('a, 'b, 'c) genarg_type -> ('a, rlevel) abstract_argument_type
(** Projection on the raw type constructor. *)

val glbwit : ('a, 'b, 'c) genarg_type -> ('b, glevel) abstract_argument_type
(** Projection on the globalized type constructor. *)

val topwit : ('a, 'b, 'c) genarg_type -> ('c, tlevel) abstract_argument_type
(** Projection on the internalized type constructor. *)

(** {5 Generic arguments} *)

type 'l generic_argument = GenArg : ('a, 'l) abstract_argument_type * 'a -> 'l generic_argument
(** A inhabitant of ['level generic_argument] is a inhabitant of some type at
    level ['level], together with the representation of this type. *)

type raw_generic_argument = rlevel generic_argument
type glob_generic_argument = glevel generic_argument
type typed_generic_argument = tlevel generic_argument

(** {6 Constructors} *)

val in_gen : ('a, 'co) abstract_argument_type -> 'a -> 'co generic_argument
(** [in_gen t x] embeds an argument of type [t] into a generic argument. *)

val out_gen : ('a, 'co) abstract_argument_type -> 'co generic_argument -> 'a
(** [out_gen t x] recovers an argument of type [t] from a generic argument. It
    fails if [x] has not the right dynamic type. *)

val has_type : 'co generic_argument -> ('a, 'co) abstract_argument_type -> bool
(** [has_type v t] tells whether [v] has type [t]. If true, it ensures that
    [out_gen t v] will not raise a dynamic type exception. *)

(** {6 Type reification} *)

type argument_type = ArgumentType : ('a, 'b, 'c) genarg_type -> argument_type

(** {6 Equalities} *)

val argument_type_eq : argument_type -> argument_type -> bool
val genarg_type_eq :
  ('a1, 'b1, 'c1) genarg_type ->
  ('a2, 'b2, 'c2) genarg_type ->
  ('a1 * 'b1 * 'c1, 'a2 * 'b2 * 'c2) CSig.eq option
val abstract_argument_type_eq :
  ('a, 'l) abstract_argument_type -> ('b, 'l) abstract_argument_type ->
  ('a, 'b) CSig.eq option

val pr_argument_type : argument_type -> Pp.t
(** Print a human-readable representation for a given type. *)

val genarg_tag : 'a generic_argument -> argument_type

val unquote : ('a, 'co) abstract_argument_type -> argument_type

(** {6 Registering genarg-manipulating functions}

  This is boilerplate code used here and there in the code of Rocq. *)

val get_arg_tag : ('a, 'b, 'c) genarg_type -> ('a, 'b, 'c) ArgT.tag
(** Works only on base objects (ExtraArg), otherwise fails badly. *)

module type GenObj =
sig
  type ('raw, 'glb, 'top) obj
  (** An object manipulating generic arguments. *)

  val name : string
  (** A name for such kind of manipulation, e.g. [interp]. *)

  val default : ('raw, 'glb, 'top) ArgT.tag -> ('raw, 'glb, 'top) obj option
  (** A generic object when there is no registered object for this type. *)
end

module Register (M : GenObj) :
sig
  (** Warning: although the following APIs use [genarg_type] the
      values must always be [ExtraArg some_tag]. *)

  val register0 : ('raw, 'glb, 'top) genarg_type ->
    ('raw, 'glb, 'top) M.obj -> unit
  (** Register a ground type manipulation function. Must be [ExtraArg]. *)

  val obj : ('raw, 'glb, 'top) genarg_type -> ('raw, 'glb, 'top) M.obj
  (** Recover a manipulation function at a given type. Must be [ExtraArg]. *)

  val mem : _ genarg_type -> bool
  (** Is this type registered? (must be [ExtraArg]) *)

  val fold_keys : (ArgT.any -> 'acc -> 'acc) -> 'acc -> 'acc
  (** Fold over the registered keys. *)

end

(** {5 Compatibility layer}

The functions below are aliases for generic_type constructors.

*)

val wit_list : ('a, 'b, 'c) genarg_type -> ('a list, 'b list, 'c list) genarg_type
val wit_opt : ('a, 'b, 'c) genarg_type -> ('a option, 'b option, 'c option) genarg_type
val wit_pair : ('a1, 'b1, 'c1) genarg_type -> ('a2, 'b2, 'c2) genarg_type ->
  ('a1 * 'a2, 'b1 * 'b2, 'c1 * 'c2) genarg_type
