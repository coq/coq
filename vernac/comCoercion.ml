(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open CErrors
open Util
open Pp
open Names
open Term
open Constr
open Context
open Vars
open Environ
open Coercionops
open Declare
open Libobject

let strength_min l = if List.mem `LOCAL l then `LOCAL else `GLOBAL

let loc_of_bool b = if b then `LOCAL else `GLOBAL

(* Errors *)

type coercion_error_kind =
  | AlreadyExists
  | NotAFunction
  | NoSource of cl_typ option
  | ForbiddenSourceClass of cl_typ
  | NoTarget
  | WrongTarget of cl_typ * cl_typ
  | NotAClass of GlobRef.t

exception CoercionError of coercion_error_kind

let explain_coercion_error g = function
  | AlreadyExists ->
      (Printer.pr_global g ++ str" is already a coercion")
  | NotAFunction ->
      (Printer.pr_global g ++ str" is not a function")
  | NoSource (Some cl) ->
      (str "Cannot recognize " ++ pr_class cl ++ str " as a source class of "
       ++ Printer.pr_global g)
  | NoSource None ->
      (str ": cannot find the source class of " ++ Printer.pr_global g)
  | ForbiddenSourceClass cl ->
      pr_class cl ++ str " cannot be a source class"
  | NoTarget ->
      (str"Cannot find the target class")
  | WrongTarget (clt,cl) ->
      (str"Found target class " ++ pr_class cl ++
       str " instead of " ++ pr_class clt)
  | NotAClass ref ->
      (str "Type of " ++ Printer.pr_global ref ++
         str " does not end with a sort")

(* Verifications pour l'ajout d'une classe *)

let check_reference_arity ref =
  let env = Global.env () in
  let c, _ = Typeops.type_of_global_in_context env ref in
  if not (Reductionops.is_arity env (Evd.from_env env) (EConstr.of_constr c)) (* FIXME *) then
    raise (CoercionError (NotAClass ref))

let check_arity = function
  | CL_FUN | CL_SORT -> ()
  | CL_CONST cst -> check_reference_arity (GlobRef.ConstRef cst)
  | CL_PROJ p -> check_reference_arity (GlobRef.ConstRef (Projection.Repr.constant p))
  | CL_SECVAR id -> check_reference_arity (GlobRef.VarRef id)
  | CL_IND kn -> check_reference_arity (GlobRef.IndRef kn)

(* Coercions *)

(* check that the computed target is the provided one *)
let check_target clt = function
  | Some cl when not (cl_typ_eq cl clt) -> raise (CoercionError (WrongTarget(clt,cl)))
  | _ -> ()

(* condition d'heritage uniforme *)

let uniform_cond sigma ctx lt =
  List.for_all2eq (EConstr.eq_constr sigma)
    lt (Context.Rel.instance_list EConstr.mkRel 0 ctx)

let class_of_global = function
  | GlobRef.ConstRef sp ->
    (match Structures.PrimitiveProjections.find_opt sp with
     | Some p -> CL_PROJ p | None -> CL_CONST sp)
  | GlobRef.IndRef sp -> CL_IND sp
  | GlobRef.VarRef id -> CL_SECVAR id
  | GlobRef.ConstructRef _ as c ->
      user_err
        (str "Constructors, such as " ++ Printer.pr_global c ++
           str ", cannot be used as a class.")

(*
lp est la liste (inverse'e) des arguments de la coercion
ids est le nom de la classe source
sps_opt est le sp de la classe source dans le cas des structures
retourne:
la classe source
nbre d'arguments de la classe
le constr de la class
la liste des variables dont depend la classe source
l'indice de la classe source dans la liste lp
*)

let get_source env lp source =
  let open Context.Rel.Declaration in
  match source with
    | None ->
       (* Take the latest non let-in argument *)
       let rec aux = function
         | [] -> raise Not_found
         | LocalDef _ :: lt -> aux lt
         | LocalAssum (_,t1) :: lt ->
            let cl1,u1,lv1 = find_class_type (push_rel_context lt env) Evd.empty (EConstr.of_constr t1) in
            cl1,lt,lv1,1
       in aux lp
    | Some cl ->
       (* Take the first argument that matches *)
       let rec aux env acc = function
         | [] -> raise Not_found
         | LocalDef _ as decl :: lt -> aux (push_rel decl env) (decl::acc) lt
         | LocalAssum (_,t1) as decl :: lt ->
            try
              let cl1,u1,lv1 = find_class_type env Evd.empty (EConstr.of_constr t1) in
              if cl_typ_eq cl cl1 then cl1,acc,lv1,Context.Rel.nhyps lt+1
              else raise Not_found
            with Not_found -> aux (push_rel decl env) (decl::acc) lt
       in aux env [] (List.rev lp)

let get_target env lp t ind =
  if (ind > 1) then
    CL_FUN
  else
    match pi1 (find_class_type (push_rel_context lp env) Evd.empty (EConstr.of_constr t)) with
    | CL_CONST p when Structures.PrimitiveProjections.mem p ->
      CL_PROJ (Option.get @@ Structures.PrimitiveProjections.find_opt p)
    | x -> x

let strength_of_cl = function
  | CL_CONST kn -> `GLOBAL
  | CL_SECVAR id -> `LOCAL
  | _ -> `GLOBAL

let strength_of_global = function
  | GlobRef.VarRef _ -> `LOCAL
  | _ -> `GLOBAL

let get_strength stre ref cls clt =
  let stres = strength_of_cl cls in
  let stret = strength_of_cl clt in
  let stref = strength_of_global ref in
  strength_min [stre;stres;stret;stref]

let ident_key_of_class = function
  | CL_FUN -> "Funclass"
  | CL_SORT -> "Sortclass"
  | CL_CONST sp -> Label.to_string (Constant.label sp)
  | CL_PROJ sp -> Label.to_string (Projection.Repr.label sp)
  | CL_IND (sp,_) -> Label.to_string (MutInd.label sp)
  | CL_SECVAR id -> Id.to_string id

(* Identity coercion *)

let error_not_transparent source =
  user_err
    (pr_class source ++ str " must be a transparent constant.")

let build_id_coercion idf_opt source poly =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let sigma, vs = match source with
    | CL_CONST sp -> Evd.fresh_global env sigma (GlobRef.ConstRef sp)
    | _ -> error_not_transparent source in
  let vs = EConstr.Unsafe.to_constr vs in
  let c = match constant_opt_value_in env (destConst vs) with
    | Some c -> c
    | None -> error_not_transparent source in
  let lams,t = decompose_lambda_decls c in
  let val_f =
    Term.it_mkLambda_or_LetIn
      (mkLambda (make_annot (Name Namegen.default_dependent_ident) Sorts.Relevant,
                 applistc vs (Context.Rel.instance_list mkRel 0 lams),
                 mkRel 1))
       lams
  in
  let typ_f =
    List.fold_left (fun d c -> Term.mkProd_wo_LetIn c d)
      (mkProd (make_annot Anonymous Sorts.Relevant, applistc vs (Context.Rel.instance_list mkRel 0 lams), lift 1 t))
      lams
  in
  (* juste pour verification *)
  let sigma, val_t = Typing.type_of env sigma (EConstr.of_constr val_f) in
  let () =
    if not (Reductionops.is_conv_leq env sigma val_t (EConstr.of_constr typ_f))
    then
      user_err  (strbrk
        "Cannot be defined as coercion (maybe a bad number of arguments).")
  in
  let name =
    match idf_opt with
      | Some idf -> idf
      | None ->
          let cl,u,_ = find_class_type env sigma (EConstr.of_constr t) in
          Id.of_string ("Id_"^(ident_key_of_class source)^"_"^
                        (ident_key_of_class cl))
  in
  let univs = Evd.univ_entry ~poly sigma in
  let constr_entry = (* Cast is necessary to express [val_f] is identity *)
    DefinitionEntry
      (definition_entry ~types:typ_f ~univs
         ~inline:true (mkCast (val_f, DEFAULTcast, typ_f)))
  in
  let kind = Decls.(IsDefinition IdentityCoercion) in
  let kn = declare_constant ~name ~kind constr_entry in
  GlobRef.ConstRef kn

let check_source = function
| Some (CL_FUN as s) -> raise (CoercionError (ForbiddenSourceClass s))
| _ -> ()

let cache_coercion ?(update=false) c =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  Coercionops.declare_coercion env sigma ~update c

let open_coercion i o =
  if Int.equal i 1 then
    cache_coercion o

let discharge_coercion c =
  if c.coe_local then None
  else
    let n =
      try Array.length (Lib.section_instance c.coe_value)
      with Not_found -> 0
    in
    let nc = { c with
      coe_param = n + c.coe_param;
      coe_is_projection = Option.map Lib.discharge_proj_repr c.coe_is_projection;
    } in
    Some nc

let classify_coercion obj =
  if obj.coe_local then Dispose else Substitute

let coe_cat = create_category "coercions"

let inCoercion : coe_info_typ -> obj =
  declare_object {(default_object "COERCION") with
    open_function = simple_open ~cat:coe_cat open_coercion;
    cache_function = cache_coercion;
    subst_function = (fun (subst,c) -> subst_coercion subst c);
    classify_function = classify_coercion;
    discharge_function = discharge_coercion;
  }

let declare_coercion coef ?(local = false) ~reversible ~isid ~src:cls ~target:clt ~params:ps () =
  let isproj =
    match coef with
    | GlobRef.ConstRef c -> Structures.PrimitiveProjections.find_opt c
    | _ -> None
  in
  let c = {
    coe_value = coef;
    coe_local = local;
    coe_reversible = reversible;
    coe_is_identity = isid;
    coe_is_projection = isproj;
    coe_source = cls;
    coe_target = clt;
    coe_param = ps;
  } in
  Lib.add_leaf (inCoercion c)

(*
nom de la fonction coercion
strength de f
nom de la classe source (optionnel)
sp de la classe source (dans le cas des structures)
nom de la classe target (optionnel)
booleen "coercion identite'?"

lorque source est None alors target est None aussi.
*)

let warn_uniform_inheritance =
  CWarnings.create ~name:"uniform-inheritance" ~category:CWarnings.CoreCategories.coercions
         (fun g ->
          Printer.pr_global g ++
            strbrk" does not respect the uniform inheritance condition.")

let add_new_coercion_core coef stre ~reversible source target isid : unit =
  check_source source;
  let env = Global.env () in
  let t, _ = Typeops.type_of_global_in_context env coef in
  if coercion_exists coef then raise (CoercionError AlreadyExists);
  let lp,tg = decompose_prod_decls t in
  let llp = List.length lp in
  if Int.equal llp 0 then raise (CoercionError NotAFunction);
  let (cls,ctx,lvs,ind) =
    try
      get_source env lp source
    with Not_found ->
      raise (CoercionError (NoSource source))
  in
  check_source (Some cls);
  if not (uniform_cond Evd.empty (* FIXME - for when possibly called with unresolved evars in the future *)
                          ctx lvs) then
    warn_uniform_inheritance coef;
  let clt =
    try
      get_target env lp tg ind
    with Not_found ->
      raise (CoercionError NoTarget)
  in
  check_target clt target;
  check_arity cls;
  check_arity clt;
  let local = match get_strength stre coef cls clt with
  | `LOCAL -> true
  | `GLOBAL -> false
  in
  let params = List.length (Context.Rel.instance_list EConstr.mkRel 0 ctx) in
  declare_coercion coef ~local ~reversible ~isid ~src:cls ~target:clt ~params ()

let try_add_new_coercion_core ref ~local c ~reversible d e =
  try add_new_coercion_core ref (loc_of_bool local) c ~reversible d e
  with CoercionError e ->
      user_err
        (explain_coercion_error ref e ++ str ".")

let try_add_new_coercion ref ~local ~reversible =
  try_add_new_coercion_core ref ~local ~reversible None None false

let try_add_new_coercion_subclass cl ~local ~poly ~reversible =
  let coe_ref = build_id_coercion None cl poly in
  try_add_new_coercion_core coe_ref ~local ~reversible (Some cl) None true

let try_add_new_coercion_with_target ref ~local ~reversible ~source ~target =
  try_add_new_coercion_core ref ~local ~reversible
    (Some source) (Some target) false

let try_add_new_identity_coercion id ~local ~poly ~source ~target =
  let ref = build_id_coercion (Some id) source poly in
  try_add_new_coercion_core ref ~local ~reversible:true
    (Some source) (Some target) true

let try_add_new_coercion_with_source ref ~local ~reversible ~source =
  try_add_new_coercion_core ref ~local ~reversible (Some source) None false

let add_coercion_hook reversible { Declare.Hook.S.scope; dref; _ } =
  let open Locality in
  let local = match scope with
  | Discharge -> assert false (* Local Coercion in section behaves like Local Definition *)
  | Global ImportNeedQualified -> true
  | Global ImportDefaultBehavior -> false
  in
  let () = try_add_new_coercion dref ~local ~reversible in
  let msg = Nametab.pr_global_env Id.Set.empty dref ++ str " is now a coercion" in
  Flags.if_verbose Feedback.msg_info msg

let add_coercion_hook ~reversible =
  Declare.Hook.make (add_coercion_hook reversible)

let add_subclass_hook ~poly { Declare.Hook.S.scope; dref; _ } =
  let open Locality in
  let stre = match scope with
  | Discharge -> assert false (* Local Subclass in section behaves like Local Definition *)
  | Global ImportNeedQualified -> true
  | Global ImportDefaultBehavior -> false
  in
  let cl = class_of_global dref in
  try_add_new_coercion_subclass cl ~local:stre ~poly

let nonuniform = Attributes.bool_attribute ~name:"nonuniform"

let add_subclass_hook ~poly ~reversible =
  Declare.Hook.make (add_subclass_hook ~poly ~reversible)

let warn_reverse_no_change =
  CWarnings.create ~name:"reversible-no-change" ~category:CWarnings.CoreCategories.coercions
    (fun () -> str "The reversible attribute is unchanged.")

let change_reverse ref ~reversible =
  if not (coercion_exists ref) then
    user_err (Printer.pr_global ref ++ str" is not a coercion.");
  let coe_info = coercion_info ref in
  if reversible = coe_info.coe_reversible then warn_reverse_no_change ()
  else cache_coercion ~update:true { coe_info with coe_reversible = reversible }
