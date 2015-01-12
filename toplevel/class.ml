(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Errors
open Util
open Pp
open Names
open Term
open Vars
open Termops
open Entries
open Environ
open Classops
open Declare
open Globnames
open Nametab
open Decl_kinds

let strength_min l = if List.mem `LOCAL l then `LOCAL else `GLOBAL

let loc_of_bool b = if b then `LOCAL else `GLOBAL

(* Errors *)

type coercion_error_kind =
  | AlreadyExists
  | NotAFunction
  | NoSource of cl_typ option
  | ForbiddenSourceClass of cl_typ
  | NotUniform
  | NoTarget
  | WrongTarget of cl_typ * cl_typ
  | NotAClass of global_reference

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
  | NotUniform ->
      (Printer.pr_global g ++
         str" does not respect the uniform inheritance condition");
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
  if not (Reductionops.is_arity (Global.env()) Evd.empty (Global.type_of_global_unsafe ref)) then
    raise (CoercionError (NotAClass ref))

let check_arity = function
  | CL_FUN | CL_SORT -> ()
  | CL_CONST cst -> check_reference_arity (ConstRef cst)
  | CL_PROJ cst -> check_reference_arity (ConstRef cst)
  | CL_SECVAR id -> check_reference_arity (VarRef id)
  | CL_IND kn -> check_reference_arity (IndRef kn)

(* Coercions *)

(* check that the computed target is the provided one *)
let check_target clt = function
  | Some cl when not (cl_typ_eq cl clt) -> raise (CoercionError (WrongTarget(clt,cl)))
  | _ -> ()

(* condition d'heritage uniforme *)

let uniform_cond nargs lt =
  let rec aux = function
    | (0,[]) -> true
    | (n,t::l) ->
      let t = strip_outer_cast t in
      isRel t && Int.equal (destRel t) n && aux ((n-1),l)
    | _ -> false
  in
  aux (nargs,lt)

let class_of_global = function
  | ConstRef sp -> 
    if Environ.is_projection sp (Global.env ()) 
    then CL_PROJ sp else CL_CONST sp
  | IndRef sp -> CL_IND sp
  | VarRef id -> CL_SECVAR id
  | ConstructRef _ as c ->
      errorlabstrm "class_of_global"
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

let get_source lp source =
  match source with
    | None ->
	let (cl1,u1,lv1) =
          match lp with
	    | [] -> raise Not_found
            | t1::_ -> find_class_type Evd.empty t1
        in
	(cl1,u1,lv1,1)
    | Some cl ->
	let rec aux = function
	  | [] -> raise Not_found
	  | t1::lt ->
	      try
		let cl1,u1,lv1 = find_class_type Evd.empty t1 in
		if cl_typ_eq cl cl1 then cl1,u1,lv1,(List.length lt+1)
		else raise Not_found
              with Not_found -> aux lt
	in aux (List.rev lp)

let get_target t ind =
  if (ind > 1) then
    CL_FUN
  else
    match pi1 (find_class_type Evd.empty t) with
    | CL_CONST p when Environ.is_projection p (Global.env ()) -> 
      CL_PROJ p
    | x -> x
      

let prods_of t =
  let rec aux acc d = match kind_of_term d with
    | Prod (_,c1,c2) -> aux (c1::acc) c2
    | Cast (c,_,_) -> aux acc c
    | _ -> (d,acc)
  in
  aux [] t

let strength_of_cl = function
  | CL_CONST kn -> `GLOBAL
  | CL_SECVAR id -> `LOCAL
  | _ -> `GLOBAL

let strength_of_global = function
  | VarRef _ -> `LOCAL
  | _ -> `GLOBAL

let get_strength stre ref cls clt =
  let stres = strength_of_cl cls in
  let stret = strength_of_cl clt in
  let stref = strength_of_global ref in
  strength_min [stre;stres;stret;stref]

let ident_key_of_class = function
  | CL_FUN -> "Funclass"
  | CL_SORT -> "Sortclass"
  | CL_CONST sp | CL_PROJ sp -> Label.to_string (con_label sp)
  | CL_IND (sp,_) -> Label.to_string (mind_label sp)
  | CL_SECVAR id -> Id.to_string id

(* Identity coercion *)

let error_not_transparent source =
  errorlabstrm "build_id_coercion"
    (pr_class source ++ str " must be a transparent constant.")

let build_id_coercion idf_opt source poly =
  let env = Global.env () in
  let vs, ctx = match source with
    | CL_CONST sp -> Universes.fresh_global_instance env (ConstRef sp)
    | _ -> error_not_transparent source in
  let c = match constant_opt_value_in env (destConst vs) with
    | Some c -> c
    | None -> error_not_transparent source in
  let lams,t = decompose_lam_assum c in
  let val_f =
    it_mkLambda_or_LetIn
      (mkLambda (Name Namegen.default_dependent_ident,
		 applistc vs (extended_rel_list 0 lams),
		 mkRel 1))
       lams
  in
  let typ_f =
    it_mkProd_wo_LetIn
      (mkProd (Anonymous, applistc vs (extended_rel_list 0 lams), lift 1 t))
      lams
  in
  (* juste pour verification *)
  let _ =
    if not
      (Reductionops.is_conv_leq env Evd.empty
	(Typing.type_of env Evd.empty val_f) typ_f)
    then
      errorlabstrm "" (strbrk
	"Cannot be defined as coercion (maybe a bad number of arguments).")
  in
  let idf =
    match idf_opt with
      | Some idf -> idf
      | None ->
	  let cl,u,_ = find_class_type Evd.empty t in
	  Id.of_string ("Id_"^(ident_key_of_class source)^"_"^
                        (ident_key_of_class cl))
  in
  let constr_entry = (* Cast is necessary to express [val_f] is identity *)
    DefinitionEntry
      (definition_entry ~types:typ_f ~poly ~univs:(Univ.ContextSet.to_context ctx)
	 ~inline:true (mkCast (val_f, DEFAULTcast, typ_f)))
  in
  let decl = (constr_entry, IsDefinition IdentityCoercion) in
  let kn = declare_constant idf decl in
  ConstRef kn

let check_source = function
| Some (CL_FUN|CL_SORT as s) -> raise (CoercionError (ForbiddenSourceClass s))
| _ -> ()

(*
nom de la fonction coercion
strength de f
nom de la classe source (optionnel)
sp de la classe source (dans le cas des structures)
nom de la classe target (optionnel)
booleen "coercion identite'?"

lorque source est None alors target est None aussi.
*)

let add_new_coercion_core coef stre poly source target isid =
  check_source source;
  let t = Global.type_of_global_unsafe coef in
  if coercion_exists coef then raise (CoercionError AlreadyExists);
  let tg,lp = prods_of t in
  let llp = List.length lp in
  if Int.equal llp 0 then raise (CoercionError NotAFunction);
  let (cls,us,lvs,ind) =
    try
      get_source lp source
    with Not_found ->
      raise (CoercionError (NoSource source))
  in
  check_source (Some cls);
  if not (uniform_cond (llp-ind) lvs) then
    msg_warning (explain_coercion_error coef NotUniform);
  let clt =
    try
      get_target tg ind
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
  declare_coercion coef ~local ~isid ~src:cls ~target:clt ~params:(List.length lvs)


let try_add_new_coercion_core ref ~local c d e f =
  try add_new_coercion_core ref (loc_of_bool local) c d e f
  with CoercionError e ->
      errorlabstrm "try_add_new_coercion_core"
        (explain_coercion_error ref e ++ str ".")

let try_add_new_coercion ref ~local poly =
  try_add_new_coercion_core ref ~local poly None None false

let try_add_new_coercion_subclass cl ~local poly =
  let coe_ref = build_id_coercion None cl poly in
  try_add_new_coercion_core coe_ref ~local poly (Some cl) None true

let try_add_new_coercion_with_target ref ~local poly ~source ~target =
  try_add_new_coercion_core ref ~local poly (Some source) (Some target) false

let try_add_new_identity_coercion id ~local poly ~source ~target =
  let ref = build_id_coercion (Some id) source poly in
  try_add_new_coercion_core ref ~local poly (Some source) (Some target) true

let try_add_new_coercion_with_source ref ~local poly ~source =
  try_add_new_coercion_core ref ~local poly (Some source) None false

let add_coercion_hook poly local ref =
  let stre = match local with
  | Local -> true
  | Global -> false
  | Discharge -> assert false
  in
  let () = try_add_new_coercion ref stre poly in
  let msg = pr_global_env Id.Set.empty ref ++ str " is now a coercion" in
  Flags.if_verbose msg_info msg

let add_coercion_hook poly = Lemmas.mk_hook (add_coercion_hook poly)

let add_subclass_hook poly local ref =
  let stre = match local with
  | Local -> true
  | Global -> false
  | Discharge -> assert false
  in
  let cl = class_of_global ref in
  try_add_new_coercion_subclass cl stre poly

let add_subclass_hook poly = Lemmas.mk_hook (add_subclass_hook poly)
