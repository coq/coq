(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Util
open Pp
open Names
open Nameops
open Term
open Termops
open Inductive
open Declarations
open Entries
open Environ
open Inductive
open Lib
open Classops
open Declare
open Libnames
open Nametab
open Decl_kinds
open Safe_typing

let strength_min4 stre1 stre2 stre3 stre4 =
  strength_min ((strength_min (stre1,stre2)),(strength_min (stre3,stre4)))

let id_of_varid c = match kind_of_term c with
  | Var id -> id
  | _ -> anomaly "class__id_of_varid"

(* lf liste des variable dont depend la coercion f
   lc liste des variable dont depend la classe source *)

let rec stre_unif_cond = function
  | ([],[]) -> Global
  | (v::l,[]) -> variable_strength v
  | ([],v::l) -> variable_strength v
  | (v1::l1,v2::l2) ->
      if v1=v2 then 
	stre_unif_cond (l1,l2)
      else
	let stre1 = (variable_strength v1)
	and stre2 = (variable_strength v2) in 
	strength_min (stre1,stre2)

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
  | NotEnoughClassArgs of cl_typ

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
         str" does not respect the inheritance uniform condition");
  | NoTarget ->
      (str"Cannot find the target class")
  | WrongTarget (clt,cl) ->
      (str"Found target class " ++ pr_class cl ++
       str " instead of " ++ pr_class clt)
  | NotAClass ref ->
      (str "Type of " ++ Printer.pr_global ref ++
         str " does not end with a sort")
  | NotEnoughClassArgs cl ->
      (str"Wrong number of parameters for " ++ pr_class cl)

(* Verifications pour l'ajout d'une classe *)

let rec arity_sort (ctx,a) = match kind_of_term a with
  | Sort (Prop _ | Type _) -> List.length ctx
  | _ -> raise Not_found

let check_reference_arity ref =
  let t = Global.type_of_global ref in
  try arity_sort (Reductionops.splay_prod (Global.env()) Evd.empty t)
  with Not_found -> raise (CoercionError (NotAClass ref))

let check_arity = function
  | CL_FUN | CL_SORT -> 0
  | CL_CONST sp -> check_reference_arity (ConstRef sp)
  | CL_SECVAR sp -> check_reference_arity (VarRef sp)
  | CL_IND sp  -> check_reference_arity (IndRef sp)

(* try_add_class : cl_typ -> strength option -> bool -> unit *)

let strength_of_cl = function 
  | CL_CONST kn -> constant_strength (sp_of_global (ConstRef kn))
  | CL_SECVAR sp -> variable_strength sp
  | _ -> Global

let try_add_class cl streopt fail_if_exists =
  if not (class_exists cl) then
    let p = check_arity cl in
    let stre' = strength_of_cl cl in 
    let stre = match streopt with
      | Some stre -> strength_min (stre,stre')
      | None -> stre'
    in
    declare_class (cl,stre,p)
  else
    if fail_if_exists then errorlabstrm "try_add_new_class" 
      (pr_class cl ++ str " is already a class")


(* Coercions *)

(* check that the computed target is the provided one *)
let check_target clt = function
  | Some cl when cl <> clt -> raise (CoercionError (WrongTarget(clt,cl)))
  | _ -> ()

(* condition d'heritage uniforme *)

let uniform_cond nargs lt = 
  let rec aux = function
    | (0,[]) -> true
    | (n,t::l) -> (strip_outer_cast t = mkRel n) & (aux ((n-1),l))
    | _ -> false
  in 
  aux (nargs,lt)

let id_of_cl  = function
  | CL_FUN -> id_of_string "FUNCLASS"
  | CL_SORT -> id_of_string "SORTCLASS"
  | CL_CONST kn -> id_of_label (label kn)
  | CL_IND ind ->
      let (_,mip) = Global.lookup_inductive ind in
      mip.mind_typename
  | CL_SECVAR id -> id

let class_of_ref = function
  | ConstRef sp -> CL_CONST sp
  | IndRef sp -> CL_IND sp
  | VarRef id -> CL_SECVAR id
  | ConstructRef _ as c -> 
      errorlabstrm "class_of_ref"
	(str "Constructors, such as " ++ Printer.pr_global c ++ 
	   str " cannot be used as class")

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
	let (cl1,lv1) =
          match lp with
	    | [] -> raise Not_found
            | t1::_ -> find_class_type t1
        in 
	(cl1,lv1,1)
    | Some cl ->
	let rec aux = function
	  | [] -> raise Not_found
	  | t1::lt ->
	      try 
		let cl1,lv1 = find_class_type t1 in
		if cl = cl1 then cl1,lv1,(List.length lt+1)
		else raise Not_found
              with Not_found -> aux lt
	in aux (List.rev lp)

let get_target t ind =
  if (ind > 1) then 
    CL_FUN
  else 
    fst (find_class_type t)

let prods_of t = 
  let rec aux acc d = match kind_of_term d with
    | Prod (_,c1,c2) -> aux (c1::acc) c2
    | Cast (c,_) -> aux acc c
    | _ -> (d,acc)
  in 
  aux [] t

let get_strength stre ref cls clt =
  let stres = (snd (class_info cls)).cl_strength in
  let stret = (snd (class_info clt)).cl_strength in
  let stref = strength_of_global ref in
(* 01/00: Supprimé la prise en compte de la force des variables locales. Sens ?
  let streunif = stre_unif_cond (s_vardep,f_vardep) in
 *)
  let streunif = Global in
  let stre' = strength_min4 stres stret stref streunif in
  strength_min (stre,stre')

(* coercion identité *)

let error_not_transparent source =
  errorlabstrm "build_id_coercion"
    (pr_class source ++ str " must be a transparent constant")

let build_id_coercion idf_opt source =
  let env = Global.env () in
  let vs = match source with
    | CL_CONST sp -> mkConst sp
    | _ -> error_not_transparent source in
  let c = match constant_opt_value env (destConst vs) with
    | Some c -> c
    | None -> error_not_transparent source in
  let lams,t = Sign.decompose_lam_assum c in
  let val_f =
    it_mkLambda_or_LetIn
      (mkLambda (Name (id_of_string "x"),
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
      error ("cannot be defined as coercion - "^
             "maybe a bad number of arguments") 
  in
  let idf =
    match idf_opt with
      | Some idf -> idf
      | None ->
	  id_of_string ("Id_"^(string_of_class source)^"_"^
                        (string_of_class (fst (find_class_type t)))) 
  in
  let constr_entry = (* Cast is necessary to express [val_f] is identity *)
    DefinitionEntry
      { const_entry_body = mkCast (val_f, typ_f);
	const_entry_type = Some typ_f;
        const_entry_opaque = false } in
  let (_,kn) = declare_constant idf (constr_entry,Decl_kinds.IsDefinition) in
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

let add_new_coercion_core coef stre source target isid =
  check_source source;
  let env = Global.env () in
  let v = constr_of_reference coef in
  let vj = Retyping.get_judgment_of env Evd.empty v in
  if coercion_exists coef then raise (CoercionError AlreadyExists);
  let tg,lp = prods_of (vj.uj_type) in
  let llp = List.length lp in
  if llp = 0 then raise (CoercionError NotAFunction);
  let (cls,lvs,ind) =
    try 
      get_source lp source
    with Not_found ->
      raise (CoercionError (NoSource source))
  in
  check_source (Some cls);
  if not (uniform_cond (llp-ind) lvs) then
    raise (CoercionError NotUniform);
  let clt =
    try
      get_target tg ind 
    with Not_found ->
      raise (CoercionError NoTarget)
  in
  check_target clt target;
  try_add_class cls None false;
  try_add_class clt None false;
  let stre' = get_strength stre coef cls clt in
  declare_coercion coef vj stre' isid cls clt (List.length lvs)

let try_add_new_coercion_core ref b c d e =
  try add_new_coercion_core ref b c d e
  with CoercionError e ->
      errorlabstrm "try_add_new_coercion_core" (explain_coercion_error ref e)

let try_add_new_coercion ref stre =
  try_add_new_coercion_core ref stre None None false

let try_add_new_coercion_subclass cl stre =
  let coe_ref = build_id_coercion None cl in
  try_add_new_coercion_core coe_ref stre (Some cl) None true

let try_add_new_coercion_with_target ref stre ~source ~target =
  try_add_new_coercion_core ref stre (Some source) (Some target) false

let try_add_new_identity_coercion id stre ~source ~target =
  let ref = build_id_coercion (Some id) source in
  try_add_new_coercion_core ref stre (Some source) (Some target) true

let try_add_new_coercion_with_source ref stre ~source =
  try_add_new_coercion_core ref stre (Some source) None false

let add_coercion_hook stre ref = 
  try_add_new_coercion ref stre;
  Options.if_verbose message
    (string_of_qualid (shortest_qualid_of_global Idset.empty ref)
    ^ " is now a coercion")

let add_subclass_hook stre ref =
  let cl = class_of_ref ref in
  try_add_new_coercion_subclass cl stre

(* try_add_new_class : global_reference -> strength -> unit *)

let class_of_global = function
  | VarRef sp -> CL_SECVAR sp
  | ConstRef sp -> CL_CONST sp
  | IndRef sp -> CL_IND sp
  | ConstructRef _ as ref -> raise (CoercionError (NotAClass ref))

let try_add_new_class ref stre =
  try try_add_class (class_of_global ref) (Some stre) true
  with CoercionError e ->
    errorlabstrm "try_add_new_class" (explain_coercion_error ref e)

(* fonctions pour le discharge: encore un peu sale mais ça s'améliore *)

type coercion_entry = 
    global_reference * strength * bool * cl_typ * cl_typ * int

let add_new_coercion (ref,stre,isid,cls,clt,n) =
  (* Un peu lourd, tout cela pour trouver l'instance *)
  let env = Global.env () in
  let v = constr_of_reference ref in
  let vj = Retyping.get_judgment_of env Evd.empty v in
  declare_coercion ref vj stre isid cls clt n

let count_extra_abstractions hyps ids_to_discard =
  let _,n =
    List.fold_left
      (fun (hyps,n as sofar) id -> 
	 match hyps with
	   | (hyp,None,_)::rest when id = hyp ->(rest, n+1)
	   | _ -> sofar)
      (hyps,0) ids_to_discard
  in n

let defined_in_sec kn olddir = 
  let _,dir,_ = repr_kn kn in
    dir = olddir

(* This moves the global path one step below *)
let process_global olddir = function
  | VarRef _ ->
      anomaly "process_global only processes global surviving the section"
  | ConstRef kn as x ->
      if defined_in_sec kn olddir then
        let newkn = Lib.make_kn (id_of_label (label kn)) in
        ConstRef newkn
      else x
  | IndRef (kn,i) as x -> 
      if defined_in_sec kn olddir then
        let newkn = Lib.make_kn (id_of_label (label kn)) in
        IndRef (newkn,i)
      else x
  | ConstructRef ((kn,i),j) as x -> 
      if defined_in_sec kn olddir then
        let newkn = Lib.make_kn (id_of_label (label kn)) in
        ConstructRef ((newkn,i),j)
      else x

let process_class olddir ids_to_discard x =
  let (cl,{cl_strength=stre; cl_param=p}) = x in
(*  let env = Global.env () in*)
  match cl with 
    | CL_SECVAR _ -> x
    | CL_CONST kn -> 
       if defined_in_sec kn olddir then
         let newkn = Lib.make_kn (id_of_label (label kn)) in
	 let hyps = (Global.lookup_constant kn).const_hyps in
	 let n = count_extra_abstractions hyps ids_to_discard in
           (CL_CONST newkn,{cl_strength=stre;cl_param=p+n})
       else 
	 x
    | CL_IND (kn,i) ->
	if defined_in_sec kn olddir then
          let newkn = Lib.make_kn (id_of_label (label kn)) in
	  let hyps = (Global.lookup_mind kn).mind_hyps in
	  let n = count_extra_abstractions hyps ids_to_discard in
          (CL_IND (newkn,i),{cl_strength=stre;cl_param=p+n})
        else 
	  x
    | _ -> anomaly "process_class" 

let process_cl sec_sp cl =
  match cl with
    | CL_SECVAR id -> cl
    | CL_CONST kn ->
	if defined_in_sec kn sec_sp then
          let newkn = Lib.make_kn (id_of_label (label kn)) in
          CL_CONST newkn
        else 
	  cl
    | CL_IND (kn,i) ->
	if defined_in_sec kn sec_sp then
          let newkn = Lib.make_kn (id_of_label (label kn)) in
          CL_IND (newkn,i)
        else 
	  cl
    | _ -> cl

let process_coercion olddir ids_to_discard (coe,coeinfo,cls,clt) =
  let hyps = context_of_global_reference coe in
  let nargs = count_extra_abstractions hyps ids_to_discard in
  (process_global olddir coe,
   coercion_strength coeinfo,
   coercion_identity coeinfo,
   process_cl olddir cls,
   process_cl olddir clt,
   nargs + coercion_params coeinfo)
