(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Collective work; includes changes by (and thus parts copyright ©)
   by Lionel Elie Mamane <lionel@mamane.lu> on May-June 2006 for
   implementation of abstraction of pretty-printing of objects. *)

open Pp
open CErrors
open Util
open CAst
open Names
open Termops
open Declarations
open Environ
open Impargs
open Libobject
open Libnames
open Globnames
open Printer
open Context.Rel.Declaration

module RelDecl = Context.Rel.Declaration
module NamedDecl = Context.Named.Declaration

let print_module mp = Printmod.print_module ~with_body:true mp
let print_modtype = Printmod.print_modtype

(**************)
(** Utilities *)

let print_closed_sections = ref false

let pr_infos_list l = v 0 (prlist_with_sep cut (fun x -> x) l)

let with_line_skip l = if List.is_empty l then mt() else fnl() ++ fnl () ++ pr_infos_list l

let blankline = mt() (* add a blank sentence in the list of infos *)

let add_colon prefix = if ismt prefix then mt () else prefix ++ str ": "

let int_or_no n = if Int.equal n 0 then str "no" else int n

(*******************)
(** Basic printing *)

let print_basename cst = pr_global (GlobRef.ConstRef cst)

let print_ref env reduce ref udecl =
  let typ, univs = Typeops.type_of_global_in_context env ref in
  let inst = UVars.make_abstract_instance univs in
  let udecl = Option.map (fun x -> ref, x) udecl in
  let bl = Printer.universe_binders_with_opt_names (Environ.universes_of_global env ref) udecl in
  let sigma = Evd.from_ctx (UState.of_names bl) in
  let typ =
    if reduce then
      let ctx,ccl = Reductionops.whd_decompose_prod_decls env sigma (EConstr.of_constr typ)
      in EConstr.to_constr sigma (EConstr.it_mkProd_or_LetIn ccl ctx)
    else typ in
  let typ = Arguments_renaming.rename_type typ ref in
  let impargs = select_stronger_impargs (implicits_of_global ref) in
  let impargs = List.map binding_kind_of_status impargs in
  let variance = let open GlobRef in match ref with
    | VarRef _ | ConstRef _ -> None
    | IndRef (ind,_) | ConstructRef ((ind,_),_) ->
      let mind = Environ.lookup_mind ind env in
      mind.Declarations.mind_variance
  in
  let inst =
    if Environ.is_polymorphic env ref
    then Printer.pr_universe_instance_binder sigma inst Univ.Constraints.empty
    else mt ()
  in
  let priv = None in (* We deliberately don't print private univs in About. *)
  hov 0 (pr_global ref ++ inst ++ str " :" ++ spc () ++ pr_ltype_env env sigma ~impargs typ ++
         Printer.pr_abstract_universe_ctx sigma ?variance univs ?priv)

(** Command [Print Implicit], somehow subsumed by [About] *)

let pr_impl_name imp = Id.print (name_of_implicit imp)

let print_impargs_by_name max = function
  | []  -> []
  | impls ->
     let n = List.length impls in
     [hov 0 (str (String.plural n "Argument") ++ spc() ++
      prlist_with_sep pr_comma pr_impl_name impls ++ spc() ++
      str (String.conjugate_verb_to_be n) ++ str" implicit" ++
      (if max then strbrk " and maximally inserted" else mt()))]

let print_one_impargs_list l =
  let imps = List.filter is_status_implicit l in
  let maximps = List.filter Impargs.maximal_insertion_of imps in
  let nonmaximps = List.subtract (=) imps maximps in (* FIXME *)
  print_impargs_by_name false nonmaximps @
  print_impargs_by_name true maximps

let print_impargs_list prefix l =
  let l = extract_impargs_data l in
  List.flatten (List.map (fun (cond,imps) ->
    match cond with
    | None ->
        List.map (fun pp -> add_colon prefix ++ pp)
          (print_one_impargs_list imps)
    | Some (n1,n2) ->
       [v 2 (prlist_with_sep cut (fun x -> x)
         [(if ismt prefix then str "When" else prefix ++ str ", when") ++
           str " applied to " ++
           (if Int.equal n1 n2 then int_or_no n2 else
            if Int.equal n1 0 then str "no more than " ++ int n2
            else int n1 ++ str " to " ++ int_or_no n2) ++
            str (String.plural n2 " argument") ++ str ":";
          v 0 (prlist_with_sep cut (fun x -> x)
            (if List.exists is_status_implicit imps
            then print_one_impargs_list imps
            else [str "No implicit arguments"]))])]) l)

let need_expansion env impl ref =
  let typ, _ = Typeops.type_of_global_in_context env ref in
  let ctx = Term.prod_decls typ in
  let nprods = List.count is_local_assum ctx in
  not (List.is_empty impl) && List.length impl >= nprods &&
    let _,lastimpl = List.chop nprods impl in
      List.exists is_status_implicit lastimpl

let print_impargs env ref =
  let impl = implicits_of_global ref in
  let has_impl = not (List.is_empty impl) in
  (* Need to reduce since implicits are computed with products flattened *)
  pr_infos_list
    ([ print_ref env (need_expansion env (select_impargs_size 0 impl) ref) ref None;
       blankline ] @
    (if has_impl then print_impargs_list (mt()) impl
     else [str "No implicit arguments"]))

(** Printing reduction behavior *)

let print_reduction_behaviour = function
  | GlobRef.ConstRef ref -> let p = Reductionops.ReductionBehaviour.print ref in if Pp.ismt p then [] else [p]
  | _ -> []

(** Printing opacity status *)

type opacity =
  | FullyOpaque
  | TransparentMaybeOpacified of Conv_oracle.level

let opacity env =
  function
  | GlobRef.VarRef v when NamedDecl.is_local_def (Environ.lookup_named v env) ->
      Some(TransparentMaybeOpacified
        (Conv_oracle.get_strategy (Environ.oracle env) (Conv_oracle.EvalVarRef v)))
  | GlobRef.ConstRef cst ->
      let cb = Environ.lookup_constant cst env in
      (match cb.const_body with
        | Undef _ | Primitive _ | Symbol _ -> None
        | OpaqueDef _ -> Some FullyOpaque
        | Def _ -> Some
          (TransparentMaybeOpacified
            (Conv_oracle.get_strategy (Environ.oracle env) (Conv_oracle.EvalConstRef cst))))
  | _ -> None

let print_opacity env ref =
  match opacity env ref with
    | None -> []
    | Some s ->
       [pr_global ref ++ str " is " ++
        match s with
          | FullyOpaque -> str "opaque"
          | TransparentMaybeOpacified Conv_oracle.Opaque ->
              str "opaque but may be made transparent"
          | TransparentMaybeOpacified lev when Conv_oracle.is_transparent lev ->
              str "transparent"
          | TransparentMaybeOpacified (Conv_oracle.Level n) ->
              str "transparent (level " ++ int n ++ str ")"
          | TransparentMaybeOpacified Conv_oracle.Expand ->
              str "transparent (expand)"]

(** Printing coercion status *)

let print_if_is_coercion ref =
  if Coercionops.coercion_exists ref then
    let i = Coercionops.coercion_info ref in
    let r = if i.Coercionops.coe_reversible then " reversible" else "" in
    [pr_global ref ++ str " is a" ++ str r ++ str " coercion"]
  else []

(** Printing polymorphic status *)

(* XXX TODO print based on the actual binders not from the monomorphic data *)
let template_poly_variables env ind =
  let mib, mip = Inductive.lookup_mind_specif env ind in
  match mib.mind_template with
  | None -> assert false
  | Some { template_defaults; template_concl } ->
    let pseudo_poly = match template_concl with
      | QSort (q, _) when Option.has_some (Sorts.QVar.var_index q) -> true
      | _ -> false
    in
    let _, vars = UVars.Instance.levels template_defaults in
    Univ.Level.Set.elements vars, pseudo_poly

let get_template_poly_variables env = function
  | GlobRef.IndRef ind | ConstructRef (ind,_) -> template_poly_variables env ind
  | VarRef _ | ConstRef _ -> assert false

let pr_template_variables env ref =
  let vars, pseudo_sort_poly = get_template_poly_variables env ref in
  str " on " ++ prlist_with_sep spc UnivNames.pr_level_with_global_universes vars
  ++ spc() ++
  (if pseudo_sort_poly
   then str "(can be instantiated to Prop)"
   else str "(cannot be instantiated to Prop)")

let print_polymorphism env ref =
  let poly = Environ.is_polymorphic env ref in
  let template_poly = Environ.is_template_polymorphic env ref in
  [ pr_global ref ++ str " is " ++
      (if poly then str "universe polymorphic"
       else if template_poly then
         str "template universe polymorphic"
         ++ if !Detyping.print_universes then h (pr_template_variables env ref) else mt()
       else str "not universe polymorphic") ]

let print_squash env ref udecl = match ref with
  | GlobRef.IndRef ind ->
    let _, mip = Inductive.lookup_mind_specif env ind in
    begin match mip.mind_squashed with
    | None -> []
    | Some squash ->
      let univs = Environ.universes_of_global env ref in
      let udecl = Option.map (fun x -> ref, x) udecl in
      let bl = Printer.universe_binders_with_opt_names univs udecl in
      let sigma = Evd.from_ctx (UState.of_names bl) in
      let inst = if fst @@ UVars.AbstractContext.size univs = 0 then mt()
        else Printer.pr_universe_instance sigma (UVars.make_abstract_instance univs)
      in
      let inds = mip.mind_sort in
      let target = match inds with
          | SProp -> str "SProp"
          | Prop -> str "SProp or Prop"
          | Set -> str "SProp, Prop or Set"
          | Type _ -> str "not in a variable sort quality"
          | QSort (q,_) -> str "in sort quality " ++ Termops.pr_evd_qvar sigma q
      in
      let unless = match squash with
        | AlwaysSquashed -> str "."
        | SometimesSquashed qs ->
          let target = match inds with
            | SProp | Prop | Set -> target
            | Type _ -> str "instantiated to constant qualities"
            | QSort (q,_) ->
              let ppq = Termops.pr_evd_qvar sigma q in
              str "equal to the instantiation of " ++ ppq ++ pr_comma() ++
              str "or to qualities smaller" ++ spc() ++
              str "(SProp <= Prop <= Type, and all variables <= Type)" ++ spc() ++
              str "than the instantiation of " ++ ppq
          in
          let qs = Sorts.Quality.Set.elements qs in
          let quality_s, is_s = match qs with
            | [_] -> "quality", "is"
            | _ -> "qualities", "are"
          in
          (* this reads kinda weird when qs is singleton of a constant quality, we get eg
             "quality Prop is equal to the instantiation of q" *)
          pr_comma () ++
          hov 0 (str "unless instantiated such that the " ++ str quality_s ++ str " " ++
                 pr_enum (Sorts.Quality.pr (Termops.pr_evd_qvar sigma)) qs ++
                 spc() ++ str is_s ++ str " " ++ target ++ str ".")
      in
      [hv 2 (hov 1 (pr_global ref ++ inst) ++ str " may only be eliminated to produce values whose type is " ++
             target ++ unless)]
    end
  | _ -> []

let print_prop_but_default_dep_elim ref =
  match ref with
  | GlobRef.IndRef ind ->
    if Indrec.is_prop_but_default_dependent_elim ind
    then [pr_global ref ++ str " is in Prop but its eliminators are declared dependent by default"]
    else []
  | _ -> []

(** Print projection status *)

let print_projection env ref =
  match ref with
  | GlobRef.ConstRef cst ->
    begin
      match Structures.PrimitiveProjections.find_opt cst with
      | Some p -> [pr_global ref ++ str " is a primitive projection of " ++ pr_global (IndRef (Projection.Repr.inductive p))]
      | None ->
      try
        let ind = (Structures.Structure.find_from_projection cst).name in
        [pr_global ref ++ str " is a projection of " ++ pr_global (IndRef ind)]
      with Not_found -> []
    end
  | _ -> []

(** Printing type-in-type status *)

let print_type_in_type env ref =
  let unsafe = Environ.is_type_in_type env ref in
  if unsafe then
    [ pr_global ref ++ str " relies on an unsafe universe hierarchy"]
  else []

(** Printing primitive projection status *)

let print_primitive_record recflag mipv = function
  | PrimRecord _ ->
    let eta = match recflag with
    | CoFinite | Finite -> str" without eta conversion"
    | BiFinite -> str " with eta conversion"
    in
    [Id.print mipv.(0).mind_typename ++ str" has primitive projections" ++ eta ++ str"."]
  | FakeRecord | NotRecord -> []

let print_primitive env ref =
  match ref with
  | GlobRef.IndRef ind ->
    let mib = Environ.lookup_mind (fst ind) env in
      print_primitive_record mib.mind_finite mib.mind_packets mib.mind_record
  | _ -> []

(** Printing arguments status (scopes, implicit, names) *)

let needs_extra_scopes env ref scopes =
  let open Constr in
  let rec aux env t = function
    | [] -> false
    | _::scopes -> match kind (Reduction.whd_all env t) with
      | Prod (na,dom,codom) -> aux (push_rel (RelDecl.LocalAssum (na,dom)) env) codom scopes
      | _ -> true
  in
  let ty, _ctx = Typeops.type_of_global_in_context env ref in
  aux env ty scopes

let implicit_kind_of_status = function
  | None -> Anonymous, Glob_term.Explicit
  | Some imp -> pi1 imp.impl_pos, if imp.impl_max then Glob_term.MaxImplicit else Glob_term.NonMaxImplicit

let extra_implicit_kind_of_status imp =
  let _,imp = implicit_kind_of_status imp in
  (Anonymous, imp)

let dummy = {
  Vernacexpr.implicit_status = Glob_term.Explicit;
   name = Anonymous;
   recarg_like = false;
   notation_scope = [];
 }

let is_dummy = function
  | Vernacexpr.(RealArg {implicit_status; name; recarg_like; notation_scope}) ->
    name = Anonymous && not recarg_like && notation_scope = [] && implicit_status = Glob_term.Explicit
  | _ -> false

let rec main_implicits i renames recargs scopes impls =
  if renames = [] && recargs = [] && scopes = [] && impls = [] then []
  else
    let recarg_like, recargs = match recargs with
      | j :: recargs when i = j -> true, recargs
      | _ -> false, recargs
    in
    let (name, implicit_status) =
      match renames, impls with
      | _, (Some _ as i) :: _ -> implicit_kind_of_status i
      | name::_, _ -> (name,Glob_term.Explicit)
      | [], (None::_ | []) -> (Anonymous, Glob_term.Explicit)
    in
    let notation_scope = match scopes with
      | scope :: _ -> List.map (fun s -> CAst.make (Constrexpr.DelimOnlyTmpScope, s)) scope
      | [] -> []
    in
    let status = {Vernacexpr.implicit_status; name; recarg_like; notation_scope} in
    let tl = function [] -> [] | _::tl -> tl in
    (* recargs is special -> tl handled above *)
    let rest = main_implicits (i+1) (tl renames) recargs (tl scopes) (tl impls) in
    status :: rest

let rec insert_fake_args volatile bidi impls =
  let open Vernacexpr in
  match volatile, bidi with
  | Some 0, _ -> VolatileArg :: insert_fake_args None bidi impls
  | _, Some 0 -> BidiArg :: insert_fake_args volatile None impls
  | None, None -> List.map (fun a -> RealArg a) impls
  | _, _ ->
    let hd, tl = match impls with
      | impl :: impls -> impl, impls
      | [] -> dummy, []
    in
    let f = Option.map pred in
    RealArg hd :: insert_fake_args (f volatile) (f bidi) tl

let print_arguments env ref =
  let qid = Nametab.shortest_qualid_of_global Id.Set.empty ref in
  let flags, recargs, nargs_for_red =
    match ref with
    | ConstRef ref ->
      begin match Reductionops.ReductionBehaviour.get ref with
      | None -> [], [], None
      | Some NeverUnfold -> [`SimplNeverUnfold], [], None
      | Some (UnfoldWhen { nargs; recargs }) -> [], recargs, nargs
      | Some (UnfoldWhenNoMatch { nargs; recargs }) -> [`SimplDontExposeCase], recargs, nargs
      end
    | _ -> [], [], None
  in
  let names, not_renamed =
    try Arguments_renaming.arguments_names ref, false
    with Not_found ->
      let ty, _ = Typeops.type_of_global_in_context env ref in
      List.map pi1 (Impargs.compute_implicits_names env (Evd.from_env env) (EConstr.of_constr ty)), true in
  let scopes = Notation.find_arguments_scope ref in
  let flags = if needs_extra_scopes env ref scopes then `ExtraScopes::flags else flags in
  let impls = Impargs.extract_impargs_data (Impargs.implicits_of_global ref) in
  let impls, moreimpls = match impls with
    | (_, impls) :: rest -> impls, rest
    | [] -> assert false
  in
  let impls = main_implicits 0 names recargs scopes impls in
  let moreimpls = List.map (fun (_,i) -> List.map extra_implicit_kind_of_status i) moreimpls in
  let bidi = Pretyping.get_bidirectionality_hint ref in
  let impls = insert_fake_args nargs_for_red bidi impls in
  if List.for_all is_dummy impls && moreimpls = [] && flags = [] then []
  else
    let open Constrexpr in
    let open Vernacexpr in
    [Ppvernac.pr_vernac_expr
       (VernacSynPure (VernacArguments (CAst.make (AN qid), impls, moreimpls, flags))) ++
     (if not_renamed then mt () else
      fnl () ++ str "  (where some original arguments have been renamed)")]

(** Printing dependencies in section variables *)

let print_section_deps env ref =
  let hyps = let open GlobRef in match ref with
  | VarRef _ -> None
  | ConstRef c ->
    let bd = Environ.lookup_constant c env in
    Some bd.const_hyps
  | IndRef (mind,_) | ConstructRef ((mind,_),_) ->
    let mb = Environ.lookup_mind mind env in
    Some mb.mind_hyps
  in
  let hyps = Option.map (List.filter NamedDecl.is_local_assum) hyps in
  match hyps with
  | None | Some [] -> []
  | Some hyps ->
    [hov 0 (pr_global ref ++ str (String.plural (List.length hyps) " uses section variable") ++ spc () ++
            hv 1 (prlist_with_sep spc (fun d -> Id.print (NamedDecl.get_id d)) (List.rev hyps)) ++ str ".")]

(** Printing bidirectionality status *)

let print_bidi_hints gr =
  match Pretyping.get_bidirectionality_hint gr with
  | None -> []
  | Some nargs ->
    [str "Using typing information from context after typing the " ++ int nargs ++ str " first arguments"]

(** Printing basic information about references (common to Print and About) *)

let print_name_infos env ref =
  let type_info_for_implicit =
    if need_expansion env (select_impargs_size 0 (implicits_of_global ref)) ref then
      (* Need to reduce since implicits are computed with products flattened *)
      [str "Expanded type for implicit arguments";
       print_ref env true ref None; blankline]
    else
      [] in
  print_type_in_type env ref @
  print_prop_but_default_dep_elim ref @
  print_projection env ref @
  print_primitive env ref @
  type_info_for_implicit @
  print_arguments env ref @
  print_section_deps env ref @
  print_if_is_coercion ref

(******************************************)
(**** Printing declarations and judgments *)
(****  Gallina layer                  *****)

let print_typed_value_in_env env sigma (trm,typ) =
  (pr_leconstr_env ~inctx:true env sigma trm ++ fnl () ++
     str "     : " ++ pr_letype_env env sigma typ)

(* To be improved; the type should be used to provide the types in the
   abstractions. This should be done recursively inside pr_lconstr, so that
   the pretty-print of a proposition (P:(nat->nat)->Prop)(P [u]u)
   synthesizes the type nat of the abstraction on u *)

let print_named_def env sigma ~impargs name body typ =
  let pbody = pr_lconstr_env ~inctx:true env sigma body in
  let ptyp = pr_ltype_env env sigma ~impargs typ in
  let pbody = if Constr.isCast body then surround pbody else pbody in
  (str "*** [" ++ str name ++ str " " ++
     hov 0 (str ":=" ++ brk (1,2) ++ pbody ++ spc () ++
              str ":" ++ brk (1,2) ++ ptyp) ++
           str "]")

let print_named_assum env sigma ~impargs name typ =
  str "*** [" ++ str name ++ str " : " ++ pr_ltype_env env sigma ~impargs typ ++ str "]"

let print_named_decl env sigma with_implicit id =
  let open Context.Named.Declaration in
  let impargs = if with_implicit then select_stronger_impargs (implicits_of_global (VarRef id)) else [] in
  let impargs = List.map binding_kind_of_status impargs in
  match lookup_named id env with
  | LocalAssum (id, typ) ->
     print_named_assum env sigma ~impargs (Id.to_string id.Context.binder_name) typ
  | LocalDef (id, body, typ) ->
     print_named_def env sigma ~impargs (Id.to_string id.Context.binder_name) body typ

let assumptions_for_print lna =
  List.fold_right (fun na env -> add_name na env) lna empty_names_context

(*********************)
(* *)

let print_inductive_args env mind mib =
  let flatmapi f v = List.flatten (Array.to_list (Array.mapi f v)) in
  let mips =
    (* We don't use the PrimRecord field as it misses the projections corresponding to local definition *)
    try
      Array.mapi (fun i mip ->
          let projs = Option.List.flatten (Structures.Structure.find_projections (mind,i)) in
          (mip.mind_consnames, Array.of_list projs)) mib.mind_packets
    with
      Not_found (* find_projections *) ->
      Array.map (fun mip -> (mip.mind_consnames,[||])) mib.mind_packets in
  flatmapi
    (fun i (constructs, projs) ->
       print_arguments env (GlobRef.IndRef (mind,i)) @
       flatmapi (fun j _ -> print_arguments env (GlobRef.ConstructRef ((mind,i),j+1))) constructs @
       flatmapi (fun _ cst -> print_arguments env (GlobRef.ConstRef cst)) projs)
    mips

let print_inductive env mind udecl =
  let mib = Environ.lookup_mind mind env in
  Printmod.pr_mutual_inductive_body env mind mib udecl

let print_inductive_with_infos env mind udecl =
  let mib = Environ.lookup_mind mind env in
  let mipv = mib.mind_packets in
  Printmod.pr_mutual_inductive_body env mind mib udecl ++
  with_line_skip
    (print_primitive_record mib.mind_finite mipv mib.mind_record @
     print_inductive_args env mind mib)

let print_section_variable_with_infos env sigma id =
  print_named_decl env sigma true id ++
  with_line_skip (print_name_infos env (GlobRef.VarRef id))

let print_typed_body env evd ~impargs (val_0,typ) =
  (pr_lconstr_env ~inctx:true env evd val_0 ++ fnl () ++ str "     : " ++ pr_ltype_env env evd ~impargs typ)

let print_instance sigma cb =
  if Declareops.constant_is_polymorphic cb then
    let univs = Declareops.constant_polymorphic_context cb in
    let inst = UVars.make_abstract_instance univs in
    pr_universe_instance_binder sigma inst Univ.Constraints.empty
  else mt()

let print_constant env ~with_values with_implicit cst udecl =
  let cb = Environ.lookup_constant cst env in
  let typ = cb.const_type in
  let univs = cb.const_universes in
  let udecl = Option.map (fun x -> GlobRef.ConstRef cst, x) udecl in
  let uctx =
    UState.of_names
      (Printer.universe_binders_with_opt_names (Declareops.constant_polymorphic_context cb) udecl)
  in
  let val_0 = match cb.const_body with
    (* XXX print something for primitives? for symbols? *)
      | Undef _ | Symbol _ | Primitive _ -> None
      | Def c -> Some ((if Option.has_some with_values then Some c else None), None)
      | OpaqueDef o ->
        match with_values with
        | None -> Some (None, None)
        | Some access ->
          let c, priv = Global.force_proof access o in
          let priv = match priv with
            | PrivateMonomorphic () -> None
            | PrivatePolymorphic priv -> Some priv
          in
          Some (Some c, priv)
  in
  let sigma = Evd.from_ctx uctx in
  let impargs = if with_implicit then select_stronger_impargs (implicits_of_global (ConstRef cst)) else [] in
  let impargs = List.map binding_kind_of_status impargs in
  let pr_ltype = pr_ltype_env env sigma in
  hov 0 (
    match val_0 with
    | None ->
        str"*** [ " ++
        print_basename cst ++ print_instance sigma cb ++ str " :" ++ spc () ++ pr_ltype ~impargs typ ++
        str" ]" ++
        Printer.pr_universes sigma univs
    | Some (optbody, priv) ->
      print_basename cst ++ print_instance sigma cb ++
      str (if Option.has_some optbody then " =" else " :") ++ spc() ++
      (match optbody with Some c-> print_typed_body env sigma ~impargs (c,typ) | None -> pr_ltype ~impargs typ)++
      Printer.pr_universes sigma univs ?priv)

let print_constant_with_infos env access cst udecl =
  print_constant env ~with_values:(Some access) true cst udecl ++
  with_line_skip (print_name_infos env (GlobRef.ConstRef cst))

let print_global_reference access env sigma gref udecl =
  let open GlobRef in
  match gref with
  | ConstRef cst ->
    (match Structures.PrimitiveProjections.find_opt cst with
     | Some p -> print_inductive_with_infos env (fst (Projection.Repr.inductive p)) udecl
     | None -> print_constant_with_infos env access cst udecl)
  | IndRef (mind,_) -> print_inductive_with_infos env mind udecl
  | ConstructRef ((mind,_),_) -> print_inductive_with_infos env mind udecl
  | VarRef id -> print_section_variable_with_infos env sigma id

let glob_constr_of_abbreviation kn =
  let (vars,a) = Abbreviation.search_abbreviation kn in
  (List.map fst vars, Notation_ops.glob_constr_of_notation_constr a)

let print_abbreviation_body env kn (vars,c) =
  let qid = Nametab.shortest_qualid_of_abbreviation Id.Set.empty kn in
  hov 2
    (hov 4
       (str "Notation " ++ pr_qualid qid ++
        prlist (fun id -> spc () ++ Id.print id) vars ++
        spc () ++ str ":=") ++
     spc () ++
     Vernacstate.System.protect (fun () ->
         Abbreviation.toggle_abbreviation ~on:false ~use:ParsingAndPrinting kn;
         pr_glob_constr_env env (Evd.from_env env) c) ())

let print_abbreviation access env sigma kn =
  let (vars,c) = glob_constr_of_abbreviation kn in
  let pp = match DAst.get c with
  | GRef (gref,_udecl) -> (* TODO: don't drop universes? *) [print_global_reference access env sigma gref None]
  | _ -> [] in
  print_abbreviation_body env kn (vars,c) ++
  with_line_skip pp

(** Unused outside? *)

let pr_prefix_name prefix = Id.print (snd (split_dirpath prefix.Nametab.obj_dir))

let print_library_node = function
  | Lib.OpenedSection (prefix, _) ->
    str " >>>>>>> Section " ++ pr_prefix_name prefix
  | Lib.OpenedModule (_,_,prefix,_) ->
    str " >>>>>>> Module " ++ pr_prefix_name prefix
  | Lib.CompilingLibrary { Nametab.obj_dir; _ } ->
    str " >>>>>>> Library " ++ DirPath.print obj_dir

(** Printing part of command [Check] *)

let print_judgment env sigma {uj_val=trm;uj_type=typ} =
  print_typed_value_in_env env sigma (trm, typ)

let print_safe_judgment {Safe_typing.jdg_env=senv; jdg_val=trm; jdg_type=typ} =
  let env = Safe_typing.env_of_safe_env senv in
  let sigma = Evd.from_env env in
  let trm = EConstr.of_constr trm in
  let typ = EConstr.of_constr typ in
  print_typed_value_in_env env sigma (trm, typ)

(** Command [Print All] *)

module DynHandle = Libobject.Dyn.Map(struct type 'a t = 'a -> Pp.t option end)

let handle h (Libobject.Dyn.Dyn (tag, o)) = match DynHandle.find tag h with
  | f -> f o
  | exception Not_found -> None

(* TODO: this kind of feature should not rely on the Libobject stack. There is
   no reason that an object in the stack corresponds to a user-facing
   declaration. It may have been so at the time this was written, but this
   needs to be done in a more principled way. *)
let print_library_leaf env sigma ~with_values mp lobj =
  match lobj with
  | AtomicObject o ->
    let handler =
      DynHandle.add Declare.Internal.objVariable begin fun id ->
          (* Outside sections, VARIABLES still exist but only with universes
             constraints *)
          (try Some(print_named_decl env sigma false id) with Not_found -> None)
      end @@
      DynHandle.add Declare.Internal.Constant.tag begin fun (id,_) ->
        let kn = Constant.make2 mp (Label.of_id id) in
        Some (print_constant env ~with_values false kn None)
      end @@
      DynHandle.add DeclareInd.Internal.objInductive begin fun (id,_) ->
        let kn = MutInd.make2 mp (Label.of_id id) in
        Some (print_inductive env kn None)
      end @@
      DynHandle.empty
    in
    handle handler o
  | ModuleObject (id,_) ->
    Some (Printmod.print_module ~with_body:(Option.has_some with_values) (MPdot (mp,Label.of_id id)))
  | ModuleTypeObject (id,_) ->
    Some (print_modtype (MPdot (mp, Label.of_id id)))
  | IncludeObject _ | KeepObject _ | EscapeObject _ | ExportObject _ -> None

let decr = Option.map ((+) (-1))

let is_done = Option.equal Int.equal (Some 0)

let print_leaves env sigma ~with_values mp n leaves =
  let rec prec n = function
    | [] -> n, []
    | o :: rest ->
      if is_done n then n, []
      else begin match print_library_leaf env sigma ~with_values mp o with
        | Some pp ->
          let n, prest = prec (decr n) rest in
          n, pp :: prest
        | None -> prec n rest
      end
  in
  let n, l = prec n leaves in
  n, v 0 (pr_sequence (fun x -> x) (List.rev l))

let print_context env sigma ~with_values =
  let rec prec n = function
    | [] -> mt()
    | (node, leaves) :: rest ->
      if is_done n then mt()
      else
        let mp = (Lib.node_prefix node).Nametab.obj_mp in
        let n, pleaves = print_leaves env sigma ~with_values mp n leaves in
        if is_done n then pleaves
        else prec n rest ++ pleaves
  in
  prec

let print_full_context access env sigma =
  print_context env sigma ~with_values:(Some access) None (Lib.contents ())
let print_full_context_typ env sigma = (* Command [Print All] *)
  print_context env sigma ~with_values:None None (Lib.contents ())

(** Command line [-output-context] *)

module DynHandleF = Libobject.Dyn.Map(struct type 'a t = 'a -> Pp.t end)

let handleF h (Libobject.Dyn.Dyn (tag, o)) = match DynHandleF.find tag h with
  | f -> f o
  | exception Not_found -> mt ()

(* TODO: see the comment for {!print_leaf_entry} *)
let print_full_pure_atomic access env sigma mp lobj =
  let handler =
    DynHandleF.add Declare.Internal.Constant.tag begin fun (id,_) ->
      let kn = KerName.make mp (Label.of_id id) in
      let con = Global.constant_of_delta_kn kn in
      let cb = Global.lookup_constant con in
      let typ = cb.const_type in
      hov 0 (
        match cb.const_body with
        | Undef _ ->
          str "Parameter " ++
          print_basename con ++ str " :" ++ spc () ++ pr_ltype_env env sigma typ
        | OpaqueDef lc ->
          str "Theorem " ++ print_basename con ++ cut () ++
          str " : " ++ pr_ltype_env env sigma typ ++ str "." ++ fnl () ++
          str "Proof " ++ pr_lconstr_env env sigma
            (fst (Global.force_proof access lc))
        | Def c ->
          str "Definition " ++ print_basename con ++ cut () ++
          str "  : " ++ pr_ltype_env env sigma typ ++ cut () ++ str " := " ++
          pr_lconstr_env env sigma c
        | Primitive _ ->
          str "Primitive " ++
          print_basename con ++ str " :" ++ spc () ++ pr_ltype_env env sigma typ
        | Symbol _ ->
          str "Symbol " ++
          print_basename con ++ str " :" ++ spc () ++ pr_ltype_env env sigma typ)
      ++ str "." ++ fnl () ++ fnl ()
    end @@
    DynHandleF.add DeclareInd.Internal.objInductive begin fun (id,_) ->
      let kn = KerName.make mp (Label.of_id id) in
      let mind = Global.mind_of_delta_kn kn in
      let mib = Global.lookup_mind mind in
      Printmod.pr_mutual_inductive_body (Global.env()) mind mib None ++
      str "." ++ fnl () ++ fnl ()
    end @@
    DynHandleF.empty
  in
  handleF handler lobj

let print_full_pure_leaf access env sigma mp = function
  | AtomicObject lobj -> print_full_pure_atomic access env sigma mp lobj
  | ModuleObject (id, _) ->
    (* TODO: make it reparsable *)
    print_module (MPdot (mp,Label.of_id id)) ++ str "." ++ fnl () ++ fnl ()
  | ModuleTypeObject (id, _) ->
    (* TODO: make it reparsable *)
    print_modtype (MPdot (mp,Label.of_id id)) ++ str "." ++ fnl () ++ fnl ()
  | _ -> mt()

let print_full_pure_context access env sigma =
  let rec prec = function
    | (node,leaves)::rest ->
      let mp = (Lib.node_prefix node).Nametab.obj_mp in
      let pp = Pp.prlist (print_full_pure_leaf access env sigma mp) leaves in
      prec rest ++ pp
  | [] -> mt ()
  in
  prec (Lib.contents ())

(** Command [Print Section] *)

(* For printing an inductive definition with
   its constructors and elimination,
   assume that the declaration of constructors and eliminations
   follows the definition of the inductive type *)

(* This is designed to print the contents of an opened section *)
let read_sec_context qid =
  let dir =
    try Nametab.locate_section qid
    with Not_found ->
      user_err ?loc:qid.loc (str "Unknown section.") in
  let rec get_cxt in_cxt = function
    | (Lib.OpenedSection ({Nametab.obj_dir;_},_), _ as hd)::rest ->
        if DirPath.equal dir obj_dir then (hd::in_cxt) else get_cxt (hd::in_cxt) rest
    | [] -> []
    | hd::rest -> get_cxt (hd::in_cxt) rest
  in
  let cxt = Lib.contents () in
  List.rev (get_cxt [] cxt)

let print_sec_context access env sigma sec =
  print_context env sigma ~with_values:(Some access) None (read_sec_context sec)

let print_sec_context_typ env sigma sec =
  print_context env sigma ~with_values:None None (read_sec_context sec)

(** Command [Print] *)

type 'a locatable_info = {
  locate : qualid -> 'a option;
  locate_all : qualid -> 'a list;
  shortest_qualid : 'a -> qualid;
  name : 'a -> Pp.t;
  print : 'a -> Pp.t;
  about : 'a -> Pp.t;
}

type logical_name =
  | Term of GlobRef.t
  | Dir of Nametab.GlobDirRef.t
  | Abbreviation of abbreviation
  | Module of ModPath.t
  | ModuleType of ModPath.t
  | Other : 'a * 'a locatable_info -> logical_name
  | Undefined of qualid

type locatable = Locatable : 'a locatable_info -> locatable

(** Generic table for objects that are accessible through a name. *)
let locatable_map : locatable String.Map.t ref = ref String.Map.empty

let register_locatable name f =
  locatable_map := String.Map.add name (Locatable f) !locatable_map

exception ObjFound of logical_name

let locate_any_name qid =
  try Term (Nametab.locate qid)
  with Not_found ->
  try Abbreviation (Nametab.locate_abbreviation qid)
  with Not_found ->
  try Dir (Nametab.locate_dir qid)
  with Not_found ->
  try Module (Nametab.locate_module qid)
  with Not_found ->
  try ModuleType (Nametab.locate_modtype qid)
  with Not_found ->
    let iter _ (Locatable info) = match info.locate qid with
    | None -> ()
    | Some ans -> raise (ObjFound (Other (ans, info)))
    in
    try String.Map.iter iter !locatable_map; Undefined qid
    with ObjFound obj -> obj

let canonical_info env ref =
  let cref = QGlobRef.canonize env ref in
  if GlobRef.UserOrd.equal ref cref then mt ()
  else match Nametab.path_of_global cref with
    | path -> spc() ++ str "(syntactically equal to" ++ spc() ++ pr_path path ++ str ")"
    | exception Not_found -> spc() ++ str "(missing canonical, bug?)"

let pr_loc_use_dp loc = match loc.Loc.fname with
  | Loc.ToplevelInput ->
    (* NB emacs mangles the message if it contains the capitalized "Toplevel input" of [Loc.pr] *)
    str "toplevel input, characters " ++ int loc.bp ++ str "-" ++ int loc.ep
  | InFile  { dirpath = None } -> Loc.pr loc
  | InFile { dirpath = Some dp } ->
    let f = str "library " ++ str dp in
    (f ++
     str", line " ++ int loc.line_nb ++ str", characters " ++
     int (loc.bp-loc.bol_pos) ++ str"-" ++ int (loc.ep-loc.bol_pos))


let loc_info gr =
  match Nametab.cci_src_loc gr with
  | None -> mt()
  | Some loc -> cut() ++ hov 0 (str "Declared in" ++ spc() ++ pr_loc_use_dp loc)

let pr_located_qualid env = function
  | Term ref ->
      let ref_str = let open GlobRef in match ref with
          ConstRef _ -> "Constant"
        | IndRef _ -> "Inductive"
        | ConstructRef _ -> "Constructor"
        | VarRef _ -> "Variable"
      in
      let extra = canonical_info env ref in
      v 0 (hov 0 (str ref_str ++ spc () ++ pr_path (Nametab.path_of_global ref) ++ extra))
  | Abbreviation kn ->
    str "Notation" ++ spc () ++ pr_path (Nametab.path_of_abbreviation kn)
  | Dir dir ->
      let s,mp =
        let open Nametab in
        let open GlobDirRef in match dir with
        | DirOpenModule mp -> "Open Module", ModPath.print mp
        | DirOpenModtype mp -> "Open Module Type", ModPath.print mp
        | DirOpenSection dir -> "Open Section", DirPath.print dir
      in
      str s ++ spc () ++ mp
  | Module mp ->
    str "Module" ++ spc () ++ DirPath.print (Nametab.dirpath_of_module mp)
  | ModuleType mp ->
      str "Module Type" ++ spc () ++ pr_path (Nametab.path_of_modtype mp)
  | Other (obj, info) -> info.name obj
  | Undefined qid ->
      pr_qualid qid ++ spc () ++ str "not a defined object."

let maybe_error_reject_univ_decl na udecl =
  let open GlobRef in
  match na, udecl with
  | _, None | Term (ConstRef _ | IndRef _ | ConstructRef _), Some _ -> ()
  | (Term (VarRef _) | Abbreviation _ | Dir _ | Module _ | ModuleType _ | Other _ | Undefined _), Some udecl ->
    (* TODO Print na somehow *)
    user_err (str "This object does not support universe names.")

let print_any_name access env sigma na udecl =
  maybe_error_reject_univ_decl na udecl;
  match na with
  | Term gref -> print_global_reference access env sigma gref udecl
  | Abbreviation kn -> print_abbreviation access env sigma kn
  | Module mp -> print_module mp
  | Dir _ -> mt ()
  | ModuleType mp -> print_modtype mp
  | Other (obj, info) -> info.print obj
  | Undefined qid ->
  try  (* A goal variable which is not a section variable *)
    let dir,str = repr_qualid qid in
    if not (DirPath.is_empty dir) then raise Not_found;
    print_named_decl env sigma true str
  with Not_found -> user_err ?loc:qid.loc (pr_qualid qid ++ spc () ++ str "not a defined object.")

let print_notation_interpretation env sigma (entry,ntn) df sc c =
  let filter = Notation.{
    notation_entry_pattern = [entry];
    interp_rule_key_pattern = Some (Inl ntn);
    use_pattern = OnlyPrinting;
    scope_pattern = sc;
    interpretation_pattern = Some c;
  } in
  Vernacstate.System.protect (fun () ->
      Notation.toggle_notations ~on:false ~all:false ~verbose:false (pr_glob_constr_env env sigma) filter;
      hov 0 (str "Notation" ++ spc () ++ Notation_ops.pr_notation_info (pr_glob_constr_env env sigma) df (snd c))) ()

let print_name access env sigma na udecl =
  match na with
  | {loc; v=Constrexpr.ByNotation (ntn,sc)} ->
    let ntn, df, sc, c, ref = Notation.interp_notation_as_global_reference_expanded ?loc ~head:false (fun _ -> true) ntn sc in
    print_notation_interpretation env sigma ntn df (Some sc) c ++ fnl () ++ fnl () ++
    print_any_name access env sigma (Term ref) udecl
  | {loc; v=Constrexpr.AN ref} ->
    print_any_name access env sigma (locate_any_name ref) udecl

(** Command [Print Notation] *)

let print_notation_grammar env sigma ntn =
  let ng = List.hd (Notgram_ops.grammar_of_notation ntn) in
  let assoc = ng.Notation_gram.notgram_assoc in
  let prdf () = Pp.str "no associativity" in
  Pp.(pr_opt_no_spc_default prdf Gramlib.Gramext.pr_assoc assoc)

exception PrintNotationNotFound of Constrexpr.notation_entry * string

let () = CErrors.register_handler @@ function
  | PrintNotationNotFound (entry, ntn_str) ->
      let entry_string = match entry with
      | Constrexpr.InConstrEntry -> "."
      | Constrexpr.InCustomEntry e -> " in " ^ e ^ " entry."
      in
      Some Pp.(str "\"" ++ str ntn_str ++ str "\"" ++ spc ()
        ++ str "cannot be interpreted as a known notation" ++ str entry_string ++ spc ()
        ++ strbrk "Make sure that symbols are surrounded by spaces and that holes are explicitly denoted by \"_\".")
  | _ -> None

let error_print_notation_not_found e s =
  raise @@ PrintNotationNotFound (e, s)

let print_notation env sigma entry raw_ntn =
  (* make sure entry exists *)
  let () =
    match entry with
    | Constrexpr.InConstrEntry -> ()
    | Constrexpr.InCustomEntry e -> Metasyntax.check_custom_entry e
  in
  (* convert notation string to key. eg. "x + y" to "_ + _" *)
  let interp_ntn = Notation.interpret_notation_string raw_ntn in
  let ntn = (entry, interp_ntn) in
  try
    let lvl = Notation.level_of_notation ntn in
    let args = Notgram_ops.non_terminals_of_notation ntn in
    let pplvl = Metasyntax.pr_level ntn lvl args in
    Pp.(str "Notation \"" ++ str interp_ntn ++ str "\"" ++ spc ()
      ++ pplvl ++ pr_comma () ++ print_notation_grammar env sigma ntn
      ++ str ".")
  with Not_found -> error_print_notation_not_found entry raw_ntn

(** Command [About] *)

let print_about_global_reference ?loc env ref udecl =
  pr_infos_list
   (print_ref env false ref udecl :: blankline ::
    print_polymorphism env ref @
    print_squash env ref udecl @
    print_name_infos env ref @
    print_reduction_behaviour ref @
    print_opacity env ref @
    print_bidi_hints ref @
    [hov 0 (str "Expands to: " ++ pr_located_qualid env (Term ref)) ++
    loc_info (TrueGlobal ref)])

let print_about_abbreviation env sigma kn =
  let (vars,c) = glob_constr_of_abbreviation kn in
  let pp = match DAst.get c with
  | GRef (gref,_udecl) -> (* TODO: don't drop universes? *) [print_about_global_reference env gref None]
  | _ -> [] in
  print_abbreviation_body env kn (vars,c) ++ fnl () ++
  hov 0 (str "Expands to: " ++ pr_located_qualid env (Abbreviation kn)) ++
  loc_info (Abbrev kn) ++
  with_line_skip pp

let print_about_any ?loc env sigma k udecl =
  maybe_error_reject_univ_decl k udecl;
  match k with
  | Term ref -> Dumpglob.add_glob ?loc ref; print_about_global_reference env ref udecl
  | Abbreviation kn -> v 0 (print_about_abbreviation env sigma kn)
  | Dir _ | Module _ | ModuleType _ | Undefined _ -> hov 0 (pr_located_qualid env k)
  | Other (obj, info) -> hov 0 (info.about obj)

let print_about env sigma na udecl =
  match na with
  | {loc;v=Constrexpr.ByNotation (ntn,sc)} ->
    let ntn, df, sc, c, ref = Notation.interp_notation_as_global_reference_expanded ?loc ~head:false (fun _ -> true) ntn sc in
    print_notation_interpretation env sigma ntn df (Some sc) c ++ fnl () ++ fnl () ++
    print_about_any ?loc env sigma (Term ref) udecl
  | {loc;v=Constrexpr.AN ref} ->
      print_about_any ?loc env sigma (locate_any_name ref) udecl

(* Command [Inspect], for debug *)

let inspect env sigma depth =
  print_context env sigma ~with_values:None (Some depth) (Lib.contents ())

(*************************************************************************)
(* Pretty-printing functions coming from classops.ml                     *)

(** Command [Print Classes] *)

open Coercionops

let print_coercion_value v = Printer.pr_global v.coe_value

let print_path ((i,j),p) =
  hov 2 (
    str"[" ++ hov 0 (prlist_with_sep pr_semicolon print_coercion_value p) ++
    str"] : ") ++
  pr_class i ++ str" >-> " ++ pr_class j ++
  str (if path_is_reversible p then " (reversible)" else "")

let _ = Coercionops.install_path_printer print_path

let print_graph () =
  prlist_with_sep fnl print_path (inheritance_graph())

(** Command [Print Classes] *)

let print_classes () =
  pr_sequence pr_class (classes())

(** Command [Print Coercions] *)

let print_coercions () =
  pr_sequence print_coercion_value (coercions())

(** Command [Print Coercion Paths] *)

let print_coercion_paths cls clt =
  let p =
    try
      lookup_path_between_class (cls, clt)
    with Not_found ->
      user_err
        (str"No path between " ++ pr_class cls ++ str" and " ++ pr_class clt
         ++ str ".")
  in
  print_path ((cls, clt), p)

(** Command [Print Canonical Projections] *)

let print_canonical_projections env sigma grefs =
  let open Structures in
  let match_proj_gref { CSTable.projection; value; solution } gr =
    QGlobRef.equal env projection gr ||
    begin match value with
      | ValuePattern.Const_cs y -> QGlobRef.equal env y gr
      | _ -> false
    end ||
    QGlobRef.equal env solution gr
  in
  let projs =
    List.filter (fun p -> List.for_all (match_proj_gref p) grefs)
      (CSTable.entries ())
  in
  prlist_with_sep fnl
    (fun { CSTable.projection; value; solution } ->
    ValuePattern.print value ++
    str " <- " ++
    pr_global projection ++ str " ( " ++ pr_global solution ++ str " )")
    projs

(***********************************************)
(** Pretty-printing functions for type classes *)

(** Command [Print Typeclasses] *)

open Typeclasses

let pr_typeclass env t =
  print_ref env false t.cl_impl None

let print_typeclasses () =
  let env = Global.env () in
    prlist_with_sep fnl (pr_typeclass env) (typeclasses ())

(** Command [Print Instances] *)

let pr_instance env i =
  (*   print_constant_with_infos i.is_impl *)
  (* lighter *)
  print_ref env false (instance_impl i) None ++
  begin match hint_priority i with
  | None -> mt ()
  | Some i -> spc () ++ str "|" ++ spc () ++ int i
  end

let print_all_instances () =
  let env = Global.env () in
  let inst = all_instances () in
    prlist_with_sep fnl (pr_instance env) inst

let print_instances r =
  let env = Global.env () in
  let inst = instances_exn env (Evd.from_env env) r in
  prlist_with_sep fnl (pr_instance env) inst

(*********************)
(* Commands [Locate] *)

let canonize_ref = let open GlobRef in function
  | ConstRef c ->
    let kn = Constant.canonical c in
    if KerName.equal (Constant.user c) kn then None
    else Some (ConstRef (Constant.make1 kn))
  | IndRef (ind,i) ->
    let kn = MutInd.canonical ind in
    if KerName.equal (MutInd.user ind) kn then None
    else Some (IndRef (MutInd.make1 kn, i))
  | ConstructRef ((ind,i),j) ->
    let kn = MutInd.canonical ind in
    if KerName.equal (MutInd.user ind) kn then None
    else Some (ConstructRef ((MutInd.make1 kn, i),j))
  | VarRef _ -> None

let display_alias = function
  | Term r ->
    begin match canonize_ref r with
    | None -> mt ()
    | Some r' ->
      let q' = Nametab.shortest_qualid_of_global Id.Set.empty r' in
      spc () ++ str "(alias of " ++ pr_qualid q' ++ str ")"
    end
  | _ -> mt ()

let locate_term qid =
  let expand = function
    | TrueGlobal ref ->
        Term ref, Nametab.shortest_qualid_of_global Id.Set.empty ref
    | Abbrev kn ->
        Abbreviation kn, Nametab.shortest_qualid_of_abbreviation Id.Set.empty kn
  in
  List.map expand (Nametab.locate_extended_all qid)

let locate_module qid =
  let all = Nametab.locate_extended_all_module qid in
  let map mp = Module mp, Nametab.shortest_qualid_of_module mp in
  let mods = List.map map all in
  (* Don't forget the opened modules: they are not part of the same name tab. *)
  let all = Nametab.locate_extended_all_dir qid in
  let map dir = let open Nametab.GlobDirRef in match dir with
  | DirOpenModule _ -> Some (Dir dir, qid)
  | _ -> None
  in
  mods @ List.map_filter map all

let locate_modtype qid =
  let all = Nametab.locate_extended_all_modtype qid in
  let map mp = ModuleType mp, Nametab.shortest_qualid_of_modtype mp in
  let modtypes = List.map map all in
  (* Don't forget the opened module types: they are not part of the same name tab. *)
  let all = Nametab.locate_extended_all_dir qid in
  let map dir = let open Nametab.GlobDirRef in match dir with
  | DirOpenModtype _ -> Some (Dir dir, qid)
  | _ -> None
  in
  modtypes @ List.map_filter map all

let locate_other s qid =
  let Locatable info = String.Map.find s !locatable_map in
  let ans = info.locate_all qid in
  let map obj = (Other (obj, info), info.shortest_qualid obj) in
  List.map map ans

type locatable_kind =
  | LocTerm
  | LocModule
  | LocOther of string
  | LocAny

let print_located_qualid env name flags qid =
  let located = match flags with
  | LocTerm -> locate_term qid
  | LocModule -> locate_modtype qid @ locate_module qid
  | LocOther s -> locate_other s qid
  | LocAny ->
    locate_term qid @
    locate_modtype qid @
    locate_module qid @
    String.Map.fold (fun s _ accu -> locate_other s qid @ accu) !locatable_map []
  in
  match located with
    | [] ->
        let (dir,id) = repr_qualid qid in
        if DirPath.is_empty dir then
          str "No " ++ str name ++ str " of basename" ++ spc () ++ Id.print id
        else
          str "No " ++ str name ++ str " of suffix" ++ spc () ++ pr_qualid qid
    | l ->
        prlist_with_sep fnl
        (fun (o,oqid) ->
          hov 2 (pr_located_qualid env o ++
          (if not (qualid_eq oqid qid) then
            spc() ++ str "(shorter name to refer to it in current context is "
            ++ pr_qualid oqid ++ str")"
           else mt ()) ++
          display_alias o)) l

let print_located_term env ref = print_located_qualid env "term" LocTerm ref
let print_located_other env s ref = print_located_qualid env s (LocOther s) ref
let print_located_module env ref = print_located_qualid env "module" LocModule ref
let print_located_qualid env ref = print_located_qualid env "object" LocAny ref
