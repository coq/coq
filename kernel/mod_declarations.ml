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
open Mod_subst

type (_, 'v) when_mod_body =
| ModBodyVal : 'v -> (mod_body, 'v) when_mod_body
| ModTypeNul : (mod_type, 'v) when_mod_body

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
  { mod_expr : ('a, module_implementation) when_mod_body; (** implementation *)
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

(** Builders *)

let make_module_body typ delta retro = {
  mod_expr = ModBodyVal FullStruct;
  mod_type = typ;
  mod_type_alg = None;
  mod_delta = delta;
  mod_retroknowledge = ModBodyVal retro;
}

let make_module_type typ delta = {
  mod_expr = ModTypeNul;
  mod_type = typ;
  mod_type_alg = None;
  mod_delta = delta;
  mod_retroknowledge = ModTypeNul;
}

let strengthen_module_body ~src typ delta mb =
  { mb with
    mod_expr = ModBodyVal (Algebraic (MENoFunctor (MEident src)));
    mod_type = typ;
    mod_delta = delta; }

let strengthen_module_type struc delta mtb =
  { mtb with
    mod_type = NoFunctor struc;
    mod_delta = delta }

let replace_module_body struc delta mb =
  (* This is only used by "with Module", we should try to inherit the algebraic type *)
  let () = match mb.mod_expr with ModBodyVal Abstract -> () | _ -> assert false in
  let () = match mb.mod_type with NoFunctor _ -> () | MoreFunctor _ -> assert false in
  { mb with
    mod_type = NoFunctor struc;
    mod_type_alg = None;
    mod_delta = delta }

let module_type_of_module mb =
  { mb with mod_expr = ModTypeNul; mod_type_alg = None;
    mod_retroknowledge = ModTypeNul; }

let module_body_of_type mtb =
  { mtb with mod_expr = ModBodyVal Abstract;
      mod_retroknowledge = ModBodyVal []; }

(** Setters *)

let set_implementation e mb =
  { mb with mod_expr = ModBodyVal e }

let set_algebraic_type mb alg =
  { mb with mod_type_alg = Some alg }

let set_retroknowledge mb rk =
  { mb with mod_retroknowledge = ModBodyVal rk }

(** Accessors *)

let mod_expr { mod_expr = ModBodyVal v; _ } = v
let mod_type m = m.mod_type
let mod_type_alg m = m.mod_type_alg
let mod_delta m = m.mod_delta
let mod_retroknowledge { mod_retroknowledge = ModBodyVal rk; _ } = rk

let mod_global_delta m = match m.mod_type with
| MoreFunctor _ -> None
| NoFunctor _ -> Some m.mod_delta

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
  let expr' = hcons_when_mod_body hcons_module_implementation mb.mod_expr in
  let type' = hcons_module_signature mb.mod_type in
  let type_alg' = mb.mod_type_alg in
  let delta' = mb.mod_delta in
  let retroknowledge' = mb.mod_retroknowledge in

  if
    mb.mod_expr == expr' &&
    mb.mod_type == type' &&
    mb.mod_type_alg == type_alg' &&
    mb.mod_delta == delta' &&
    mb.mod_retroknowledge == retroknowledge'
  then mb
  else {
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

(** Operators *)

let rec functor_smart_map fty f0 funct = match funct with
  | MoreFunctor (mbid,ty,e) ->
    let ty' = fty mbid ty in
    let e' = functor_smart_map fty f0 e in
    if ty==ty' && e==e' then funct else MoreFunctor (mbid,ty',e')
  | NoFunctor a ->
    let a' = f0 a in if a==a' then funct else NoFunctor a'

let implem_smart_map (type a) fs fa (expr : (a, _) when_mod_body) : (a, _) when_mod_body =
  match expr with
  | ModTypeNul -> ModTypeNul
  | ModBodyVal impl ->
    match impl with
    | Struct e -> let e' = fs e in if e==e' then expr else ModBodyVal (Struct e')
    | Algebraic a -> let a' = fa a in if a==a' then expr else ModBodyVal (Algebraic a')
    | Abstract | FullStruct -> expr

let functorize params init =
  List.fold_left (fun e (mbid,mt) -> MoreFunctor(mbid,mt,e)) init params

let functorize_module params mb =
  let f x = functorize params x in
  let fe x = iterate (fun e -> MEMoreFunctor e) (List.length params) x in
  { mb with
    mod_expr = implem_smart_map (fun x -> x) fe mb.mod_expr;
    mod_type = f mb.mod_type;
    mod_type_alg = Option.map fe mb.mod_type_alg }

(** Substitutions of modular structures *)

type subst_kind = Dom | Codom | Both | Neither | Shallow of Mod_subst.substitution

let subst_dom = Dom
let subst_codom = Codom
let subst_dom_codom = Both
let subst_shallow_dom_codom s = Shallow s

let apply_subst skind subst delta = match skind with
| Dom -> subst_dom_delta_resolver subst delta
| Codom -> subst_codom_delta_resolver subst delta
| Both -> subst_dom_codom_delta_resolver subst delta
| Neither -> delta
| Shallow subst' -> subst_dom_codom_delta_resolver subst' delta (* ignore subst *)

let is_functor = function
  | NoFunctor _ -> false
  | MoreFunctor _ -> true

let subst_with_body subst = function
  | WithMod(id,mp) as orig ->
    let mp' = subst_mp subst mp in
    if mp==mp' then orig else WithMod(id,mp')
  | WithDef(id,(c,ctx)) as orig ->
    let c' = subst_mps subst c in
    if c==c' then orig else WithDef(id,(c',ctx))

let subst_retro : type a. Mod_subst.substitution -> a module_retroknowledge -> a module_retroknowledge =
  fun subst retro ->
    match retro with
    | ModTypeNul as r -> r
    | ModBodyVal l as r ->
      let l' = List.Smart.map (subst_retro_action subst) l in
      if l == l' then r else ModBodyVal l

let rec subst_structure skind subst mp sign =
  let subst_field ((l,body) as orig) = match body with
    | SFBconst cb ->
      let cb' = subst_const_body subst cb in
      if cb==cb' then orig else (l,SFBconst cb')
    | SFBmind mib ->
      let mib' = subst_mind_body subst mib in
      if mib==mib' then orig else (l,SFBmind mib')
    | SFBrules rrb ->
      let rrb' = subst_rewrite_rules subst rrb in
      if rrb==rrb' then orig else (l,SFBrules rrb')
    | SFBmodule mb ->
      let mb' = subst_module skind subst (MPdot (mp, l)) mb in
      if mb==mb' then orig else (l,SFBmodule mb')
    | SFBmodtype mtb ->
      let mtb' = subst_modtype skind subst (MPdot (mp, l)) mtb in
      if mtb==mtb' then orig else (l,SFBmodtype mtb')
  in
  List.Smart.map subst_field sign

and subst_module_body : type a. _ -> _ -> _ -> _ -> a generic_module_body -> a generic_module_body =
  fun is_mod skind subst mp mb ->
    let { mod_expr=me; mod_type=ty; mod_type_alg=aty;
          mod_retroknowledge=retro; _ } = mb in
  let mp' = subst_mp subst mp in
  let subst =
    if ModPath.equal mp mp' then subst
    else if is_mod && not (is_functor ty) then subst
    else add_mp mp mp' (empty_delta_resolver mp') subst
  in
  let ty' = subst_signature skind subst mp ty in
  let me' = subst_impl subst mp me in
  let aty' = Option.Smart.map (subst_expression subst) aty in
  let retro' = subst_retro subst retro in
  let delta' = apply_subst skind subst mb.mod_delta in
  if mp==mp' && me==me' && ty==ty' && aty==aty'
     && retro==retro' && delta'==mb.mod_delta
  then mb
  else
    { mod_expr = me';
      mod_type = ty';
      mod_type_alg = aty';
      mod_retroknowledge = retro';
      mod_delta = delta';
    }

and subst_module skind subst mp mb =
  subst_module_body true skind subst mp mb

and subst_impl : type a. _ -> _ -> (a, _) when_mod_body -> (a, _) when_mod_body =
  fun subst mp me ->
  implem_smart_map
    (fun sign -> subst_structure Neither subst mp sign) (subst_expression subst) me

and subst_modtype skind subst mp mtb = subst_module_body false skind subst mp mtb

and subst_expr subst seb = match seb with
  | MEident mp ->
    let mp' = subst_mp subst mp in
    if mp==mp' then seb else MEident mp'
  | MEapply (meb1,mp2) ->
    let meb1' = subst_expr subst meb1 in
    let mp2' = subst_mp subst mp2 in
    if meb1==meb1' && mp2==mp2' then seb else MEapply(meb1',mp2')
  | MEwith (meb,wdb) ->
    let meb' = subst_expr subst meb in
    let wdb' = subst_with_body subst wdb in
    if meb==meb' && wdb==wdb' then seb else MEwith(meb',wdb')

and subst_expression subst me = match me with
| MENoFunctor malg ->
  let malg' = subst_expr subst malg in
  if malg == malg' then me else MENoFunctor malg'
| MEMoreFunctor mf ->
  let mf' = subst_expression subst mf in
  if mf == mf' then me else MEMoreFunctor mf'

and subst_signature skind subst mp =
  functor_smart_map
    (fun mbid mtb -> subst_modtype skind subst (MPbound mbid) mtb)
    (fun sign -> subst_structure skind subst mp sign)

(** Cleaning a module expression from bounded parts

     For instance:
       functor(X:T)->struct module M:=X end)
     becomes:
       functor(X:T)->struct module M:=<content of T> end)
*)

type 'a mod_expr = ('a, module_implementation) when_mod_body

let rec is_bounded_expr l = function
  | MEident (MPbound mbid) -> MBIset.mem mbid l
  | MEapply (fexpr,mp) ->
      is_bounded_expr l (MEident mp) || is_bounded_expr l fexpr
  | _ -> false

let rec clean_module_body : type a. _ -> a generic_module_body -> a generic_module_body =
  fun l mb ->
  let typ = mb.mod_type in
  let typ' = clean_signature l typ in
  let expr' = clean_mod_expr l mb.mod_expr in
  if typ==typ' && mb.mod_expr==expr' then mb
  else { mb with mod_type=typ'; mod_expr = expr' }

and clean_field l field = match field with
  | (lab,SFBmodule mb) ->
    let mb' = clean_module_body l mb in
    if mb==mb' then field else (lab,SFBmodule mb')
  | _ -> field

and clean_structure l = List.Smart.map (clean_field l)

and clean_signature l =
  functor_smart_map (fun _ mb -> clean_module_body l mb) (clean_structure l)

and clean_expression _ me = me

and clean_mod_expr : type a. _ -> a mod_expr -> a mod_expr =
  fun l me -> match me with
  | ModBodyVal (Algebraic (MENoFunctor m)) when is_bounded_expr l m ->
    ModBodyVal FullStruct
  | _ ->
    let me' = implem_smart_map (clean_structure l) (clean_expression l) me in
    if me == me' then me else me'
