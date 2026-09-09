(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** {6 [Mod_subst] } *)

open Names
open Constr

(** {6 Delta resolver} *)

(** A delta resolver is a renaming of kernames and modpaths.
    Objects on which the resolver acts non-trivially must share a common modpath
    prefix called the root of the resolver.

    Resolvers come in three flavours, statically distinguished by their
    parameter. All of them map names to other names; they differ in the
    inlining information they may carry.

    - Resolvers from module bodies. They contains no inlining data.
    - Resolvers from module types. They may contain inlining declarations, i.e.
      the level of a [Parameter Inline]. Only a module type may declare
      parameters, hence only a module type resolver may carry such information.
    - Resolvers from module substitutions. They may contain inlining payloads,
      which are terms inserted in lieu of the original constant when
      applying the substitution. *)
type 'a delta_resolver

type mod_body = [ `ModBody ]
type mod_type = [ `ModType ]
type mod_subst = [ `ModSubst ]

(** Turn a resolver of any kind into a resolver of any other kind by dropping
    all inlining information. *)
val forget_inline_delta_resolver : 'a delta_resolver -> 'b delta_resolver

(** A module body's resolver carries no inlining information by construction,
    so it can be read at any other kind without losing anything. *)
val of_body_delta_resolver : mod_body delta_resolver -> 'a delta_resolver

(** Given a root, build a resolver. *)
val empty_delta_resolver : ModPath.t -> 'a delta_resolver

val has_root_delta_resolver : ModPath.t -> 'a delta_resolver -> bool

(** [add_mp_delta_resolver mp v reso] assumes that root(reso) ⊆ mp and mp ≠ v. *)
val add_mp_delta_resolver :
  ModPath.t -> ModPath.t -> 'a delta_resolver -> 'a delta_resolver

(** [lift_mp_delta_resolver mp reso] marks [mp] as being a bound name that must
    be left untouched by substitution. This is the semantics of delayed
    resolvers for functors and module types. Assumes that root(reso) ⊆ mp. *)
val lift_mp_delta_resolver :
  ModPath.t -> 'a delta_resolver -> 'a delta_resolver

(** [add_kn_delta_resolver kn v reso] assumes that root(reso) ⊆ modpath(kn). *)
val add_kn_delta_resolver :
  KerName.t -> KerName.t -> 'a delta_resolver -> 'a delta_resolver

(** [add_inline_delta_resolver kn v reso] assumes that root(reso) ⊆ modpath(kn). *)
val add_inline_delta_resolver :
  KerName.t -> int -> mod_type delta_resolver -> mod_type delta_resolver

(** [add_inline_body_delta_resolver kn v reso] assumes that root(reso) ⊆ modpath(kn). *)
val add_inline_body_delta_resolver :
  KerName.t -> constr UVars.univ_abstracted ->
  mod_subst delta_resolver -> mod_subst delta_resolver

(** [add_delta_resolver reso1 reso2] merges two renamings, assuming that
    root(reso2) ⊆ root(reso1). Note that this is asymmetrical. The root of the
    result is root(reso2). *)
val add_delta_resolver : 'a delta_resolver -> 'a delta_resolver -> 'a delta_resolver

(** Assuming mp ⊆ root(delta), [upcast_delta_resolver mp delta] allows seeing
    [delta] as a resolver with root = mp. *)
val upcast_delta_resolver : ModPath.t -> 'a delta_resolver -> 'a delta_resolver

(** Effect of a [delta_resolver] on a module path, on a kernel name *)

val mp_of_delta : 'a delta_resolver -> ModPath.t -> ModPath.t
val kn_of_delta : 'a delta_resolver -> KerName.t -> KerName.t

(** [mp_is_alias reso mp] tells whether [reso] makes [mp] equivalent to some
    other modpath. Note that both this and [mp_of_delta] take prefixes into
    account: a module is equivalent to another one as soon as one of its
    ancestors is. *)
val mp_is_alias : 'a delta_resolver -> ModPath.t -> bool

(** Build a constant whose canonical part is obtained via a resolver *)

val constant_of_delta_kn : 'a delta_resolver -> KerName.t -> Constant.t

(** Same for inductive names *)

val mind_of_delta_kn : 'a delta_resolver -> KerName.t -> MutInd.t

val fold_inline_body_delta_resolver :
  (KerName.t -> constr UVars.univ_abstracted -> 'b -> 'b) ->
  mod_subst delta_resolver -> 'b -> 'b

(** The fields the resolver declared inlinable, up to the given level *)
val inline_of_delta : int option -> mod_type delta_resolver -> KerName.t list

(** {6 Substitution} *)

type substitution

val empty_subst : substitution

val is_empty_subst : substitution -> bool

(** add_* add [arg2/arg1]\{arg3\} to the substitution with no sequential
   composition. Most often this is not what you want. For sequential
   composition, try [join (map_mbid mp delta) subs] **)
val add_mbid :
  MBId.t -> ModPath.t -> mod_subst delta_resolver -> substitution -> substitution
val add_mp :
  ModPath.t -> ModPath.t -> mod_subst delta_resolver -> substitution -> substitution

(** map_* create a new substitution [arg2/arg1]\{arg3\} *)
val map_mbid :
  MBId.t -> ModPath.t -> mod_subst delta_resolver -> substitution
val map_mp :
  ModPath.t -> ModPath.t -> mod_subst delta_resolver -> substitution

(** sequential composition:
   [substitute (join sub1 sub2) t = substitute sub2 (substitute sub1 t)]
*)
val join : substitution -> substitution -> substitution


(** [subst_dom_delta_resolver mpfrom mpto delta] substitutes the root of the
    resolver [delta] from [mpfrom] to [mpto], i.e. performs α-equivalence. *)
val subst_dom_delta_resolver :
  ModPath.t -> ModPath.t -> 'a delta_resolver -> 'a delta_resolver

(** Apply the substitution on the codomain of the resolver  *)
val subst_codom_delta_resolver :
  substitution -> 'a delta_resolver -> 'a delta_resolver

val subst_dom_codom_delta_resolver :
  substitution -> 'a delta_resolver -> 'a delta_resolver


(**/**)
(* debugging *)
val debug_string_of_subst : substitution -> string
val debug_pr_subst : substitution -> Pp.t
val debug_string_of_delta : 'a delta_resolver -> string
val debug_pr_delta :
  (Constr.constr UVars.univ_abstracted -> Pp.t) -> 'a delta_resolver -> Pp.t
(**/**)

(** [subst_mp sub mp] guarantees that whenever the result of the
   substitution is structutally equal [mp], it is equal by pointers
   as well [==] *)

val subst_mp :
  substitution -> ModPath.t -> ModPath.t

val subst_mind :
  substitution -> MutInd.t -> MutInd.t

val subst_ind :
  substitution -> inductive -> inductive

val subst_constructor :
  substitution -> constructor -> constructor

val subst_pind : substitution -> pinductive -> pinductive

val subst_kn :
  substitution -> KerName.t -> KerName.t

val subst_con :
  substitution -> Constant.t -> Constant.t * constr UVars.univ_abstracted option

val subst_pcon :
  substitution -> pconstant -> pconstant

val subst_constant :
  substitution -> Constant.t -> Constant.t

val subst_proj_repr : substitution -> Projection.Repr.t -> Projection.Repr.t
val subst_proj : substitution -> Projection.t -> Projection.t

val subst_retro_action : substitution -> Retroknowledge.action -> Retroknowledge.action

(** [replace_mp_in_con mp mp' con] replaces [mp] with [mp'] in [con] *)
val replace_mp_in_kn : ModPath.t -> ModPath.t -> KerName.t -> KerName.t

(** [subst_mps sub c] performs the substitution [sub] on all kernel
   names appearing in [c] *)
val subst_mps : substitution -> constr -> constr
val subst_mps_list : substitution list -> constr -> constr
