(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Names
open Declarations
open Declareops

type structure_field_body =
  (module_body, module_type_body) Declarations.structure_field_body

and structure_body =
  (module_body, module_type_body) Declarations.structure_body

(** A module signature is a structure, with possibly functors on top of it *)

and module_signature = (module_type_body,structure_body) functorize

and module_implementation =
  | Abstract (** no accessible implementation *)
  | Algebraic of module_expression (** non-interactive algebraic expression *)
  | Struct of structure_body (** interactive body living in the parameter context of [mod_type] *)
  | FullStruct (** special case of [Struct] : the body is exactly [mod_type] *)

and 'a generic_module_body =
  { mod_mp : ModPath.t; (** absolute path of the module *)
    mod_expr : ('a, module_implementation) when_mod_body; (** implementation *)
    mod_type : module_signature; (** expanded type *)
    mod_type_alg : module_expression option; (** algebraic type *)
    mod_delta : Mod_subst.delta_resolver; (**
      quotiented set of equivalent constants and inductive names *)
    mod_retroknowledge : ('a, Retroknowledge.action list) when_mod_body }

(** For a module, there are five possible situations:
    - [Declare Module M : T] then [mod_expr = Abstract; mod_type_alg = Some T]
    - [Module M := E] then [mod_expr = Algebraic E; mod_type_alg = None]
    - [Module M : T := E] then [mod_expr = Algebraic E; mod_type_alg = Some T]
    - [Module M. ... End M] then [mod_expr = FullStruct; mod_type_alg = None]
    - [Module M : T. ... End M] then [mod_expr = Struct; mod_type_alg = Some T]
    And of course, all these situations may be functors or not. *)

and module_body = mod_body generic_module_body

(** A [module_type_body] is just a [module_body] with no implementation and
    also an empty [mod_retroknowledge]. Its [mod_type_alg] contains
    the algebraic definition of this module type, or [None]
    if it has been built interactively. *)

and module_type_body = mod_type generic_module_body

type 'a module_retroknowledge = ('a, Retroknowledge.action list) when_mod_body

(** Extra invariants :

    - No [MEwith] inside a [mod_expr] implementation : the 'with' syntax
      is only supported for module types

    - A module application is atomic, for instance ((M N) P) :
      * the head of [MEapply] can only be another [MEapply] or a [MEident]
      * the argument of [MEapply] is now directly forced to be a [ModPath.t].
*)

let mod_expr { mod_expr = ModBodyVal v; _ } = v

(** Hashconsing of modules *)

let hcons_when_mod_body (type a b) (f : b -> b) : (a, b) when_mod_body -> (a, b) when_mod_body = function
| ModBodyVal v as arg ->
  let v' = f v in
  if v == v' then arg else ModBodyVal v'
| ModTypeNul -> ModTypeNul

let hcons_functorize hty he hself f = match f with
| NoFunctor e ->
  let e' = he e in
  if e == e' then f else NoFunctor e'
| MoreFunctor (mid, ty, nf) ->
  (** FIXME *)
  let mid' = mid in
  let ty' = hty ty in
  let nf' = hself nf in
  if mid == mid' && ty == ty' && nf == nf' then f
  else MoreFunctor (mid, ty', nf')

let hcons_module_alg_expr me = me

let rec hcons_module_expression me = match me with
| MENoFunctor malg ->
  let malg' = hcons_module_alg_expr malg in
  if malg == malg' then me else MENoFunctor malg'
| MEMoreFunctor mf ->
  let mf' = hcons_module_expression mf in
  if mf' == mf then me else MEMoreFunctor mf'

let rec hcons_structure_field_body sb = match sb with
| SFBconst cb ->
  let cb' = hcons_const_body cb in
  if cb == cb' then sb else SFBconst cb'
| SFBmind mib ->
  let mib' = hcons_mind mib in
  if mib == mib' then sb else SFBmind mib'
| SFBmodule mb ->
  let mb' = hcons_generic_module_body mb in
  if mb == mb' then sb else SFBmodule mb'
| SFBmodtype mb ->
  let mb' = hcons_generic_module_body mb in
  if mb == mb' then sb else SFBmodtype mb'
| SFBrules _ -> sb (* TODO? *)

and hcons_structure_body sb =
  (** FIXME *)
  let map (l, sfb as fb) =
    let l' = Names.Label.hcons l in
    let sfb' = hcons_structure_field_body sfb in
    if l == l' && sfb == sfb' then fb else (l', sfb')
  in
  List.Smart.map map sb

and hcons_module_signature ms =
  hcons_functorize hcons_generic_module_body hcons_structure_body hcons_module_signature ms

and hcons_module_implementation mip = match mip with
| Abstract -> Abstract
| Algebraic me ->
  let me' = hcons_module_expression me in
  if me == me' then mip else Algebraic me'
| Struct ms ->
  let ms' = hcons_structure_body ms in
  if ms == ms' then mip else Struct ms
| FullStruct -> FullStruct

and hcons_generic_module_body :
  'a. 'a generic_module_body -> 'a generic_module_body =
  fun mb ->
  let mp' = mb.mod_mp in
  let expr' = hcons_when_mod_body hcons_module_implementation mb.mod_expr in
  let type' = hcons_module_signature mb.mod_type in
  let type_alg' = mb.mod_type_alg in
  let delta' = mb.mod_delta in
  let retroknowledge' = mb.mod_retroknowledge in

  if
    mb.mod_mp == mp' &&
    mb.mod_expr == expr' &&
    mb.mod_type == type' &&
    mb.mod_type_alg == type_alg' &&
    mb.mod_delta == delta' &&
    mb.mod_retroknowledge == retroknowledge'
  then mb
  else {
    mod_mp = mp';
    mod_expr = expr';
    mod_type = type';
    mod_type_alg = type_alg';
    mod_delta = delta';
    mod_retroknowledge = retroknowledge';
  }

let hcons_module_body =
  hcons_generic_module_body

let hcons_module_type =
  hcons_generic_module_body
