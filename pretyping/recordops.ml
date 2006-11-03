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
open Libnames
open Nametab
open Term
open Termops
open Typeops
open Libobject
open Library
open Classops
open Mod_subst
open Reductionops

(*s A structure S is a non recursive inductive type with a single
   constructor (the name of which defaults to Build_S) *)

(* Table des structures: le nom de la structure (un [inductive]) donne
   le nom du constructeur, le nombre de param�tres et pour chaque
   argument r�el du constructeur, le nom de la projection
   correspondante, si valide, et un bool�en disant si c'est une vraie
   projection ou bien une fonction constante (associ�e � un LetIn) *)

type struc_typ = {
  s_CONST : identifier; 
  s_EXPECTEDPARAM : int;
  s_PROJKIND : bool list;
  s_PROJ : constant option list }

let structure_table = ref (Indmap.empty : struc_typ Indmap.t)
let projection_table = ref Cmap.empty

let option_fold_right f p e = match p with Some a -> f a e | None -> e

let load_structure i (_,(ind,id,kl,projs)) =
  let n = (fst (Global.lookup_inductive ind)).Declarations.mind_nparams in
  let struc =
    { s_CONST = id; s_EXPECTEDPARAM = n; s_PROJ = projs; s_PROJKIND = kl } in
  structure_table := Indmap.add ind struc !structure_table;
  projection_table := 
    List.fold_right (option_fold_right (fun proj -> Cmap.add proj struc))
      projs !projection_table

let cache_structure o =
  load_structure 1 o

let subst_structure (_,subst,((kn,i),id,kl,projs as obj)) = 
  let kn' = subst_kn subst kn in
  let projs' =
   (* invariant: struc.s_PROJ is an evaluable reference. Thus we can take *)
   (* the first component of subst_con.                                   *)
   list_smartmap 
     (option_smartmap (fun kn -> fst (subst_con subst kn)))
    projs
  in
    if projs' == projs && kn' == kn then obj else
      ((kn',i),id,kl,projs')

let discharge_structure (_,(ind,id,kl,projs)) =
  Some (Lib.discharge_inductive ind, id, kl,
        List.map (option_map Lib.discharge_con) projs)

let (inStruc,outStruc) =
  declare_object {(default_object "STRUCTURE") with 
    cache_function = cache_structure;
    load_function = load_structure;
    subst_function = subst_structure;
    classify_function = (fun (_,x) -> Substitute x);
    discharge_function = discharge_structure;
    export_function = (function x -> Some x) }

let declare_structure (s,c,kl,pl) = 
  Lib.add_anonymous_leaf (inStruc (s,c,kl,pl))

let lookup_structure indsp = Indmap.find indsp !structure_table

let lookup_projections indsp = (lookup_structure indsp).s_PROJ

let find_projection_nparams = function
  | ConstRef cst -> (Cmap.find cst !projection_table).s_EXPECTEDPARAM
  | _ -> raise Not_found


(************************************************************************)
(*s A canonical structure declares "canonical" conversion hints between *)
(*  the effective components of a structure and the projections of the  *)
(*  structure *)

(* Table des definitions "object" : pour chaque object c,

  c := [x1:B1]...[xk:Bk](Build_R a1...am t1...t_n)

  If ti has the form (ci ui1...uir) where ci is a global reference and
if the corresponding projection Li of the structure R is defined, one
declare a "conversion" between ci and Li

    x1:B1..xk:Bk |- (Li a1..am (c x1..xk)) =_conv (ci ui1...uir)

that maps the pair (Li,ci) to the following data

    o_DEF = c
    o_TABS = B1...Bk
    o_PARAMS = a1...am
    o_TCOMP = ui1...uir

*)

type obj_typ = {
  o_DEF : constr;
  o_TABS : constr list;    (* ordered *)
  o_TPARAMS : constr list; (* ordered *)
  o_TCOMPS : constr list } (* ordered *)

let object_table =
  (ref [] : ((global_reference * global_reference) * obj_typ) list ref)

let canonical_projections () = !object_table

let keep_true_projections projs kinds =
  map_succeed (function (p,true) -> p | _ -> failwith "")
    (List.combine projs kinds)

(* Intended to always success *)
let compute_canonical_projections (con,ind) =
  let v = mkConst con in
  let c = Environ.constant_value (Global.env()) con in
  let lt,t = Reductionops.splay_lambda (Global.env()) Evd.empty c in
  let lt = List.rev (List.map snd lt) in
  let args = snd (decompose_app t) in
  let { s_EXPECTEDPARAM = p; s_PROJ = lpj; s_PROJKIND = kl } = lookup_structure ind in
  let params, projs = list_chop p args in
  let lpj = keep_true_projections lpj kl in
  let lps = List.combine lpj projs in
  let comp =
    List.fold_left
      (fun l (spopt,t) -> (* comp=components *)
	 match spopt with
           | Some proji_sp ->
	       let c, args = decompose_app t in
	       (try (ConstRef proji_sp, global_of_constr c, args) :: l
                with Not_found -> l)
	   | _ -> l)
      [] lps in
  List.map (fun (refi,c,argj) ->
    (refi,c),{o_DEF=v; o_TABS=lt; o_TPARAMS=params; o_TCOMPS=argj})
    comp

let open_canonical_structure i (_,o) =
  if i=1 then
    let lo = compute_canonical_projections o in
    List.iter (fun (o,_ as x) ->
      if not (List.mem_assoc o !object_table) then
	object_table := x :: (!object_table)) lo

let cache_canonical_structure o =
  open_canonical_structure 1 o

let subst_canonical_structure (_,subst,(cst,ind as obj)) =
  (* invariant: cst is an evaluable reference. Thus we can take *)
  (* the first component of subst_con.                                   *)
  let cst' = fst (subst_con subst cst) in
  let ind' = Inductiveops.subst_inductive subst ind in
  if cst' == cst & ind' == ind then obj else (cst',ind')

let discharge_canonical_structure (_,(cst,ind)) =
  Some (Lib.discharge_con cst,Lib.discharge_inductive ind)

let (inCanonStruc,outCanonStruct) =
  declare_object {(default_object "CANONICAL-STRUCTURE") with 
    open_function = open_canonical_structure;
    cache_function = cache_canonical_structure;
    subst_function = subst_canonical_structure;
    classify_function = (fun (_,x) -> Substitute x);
    discharge_function = discharge_canonical_structure;
    export_function = (function x -> Some x) }

let add_canonical_structure x = Lib.add_anonymous_leaf (inCanonStruc x)

(*s High-level declaration of a canonical structure *)

let error_not_structure ref =
  errorlabstrm "object_declare"
    (Nameops.pr_id (id_of_global ref) ++ str" is not a structure object")

let check_and_decompose_canonical_structure ref =
  let sp = match ref with ConstRef sp -> sp | _ -> error_not_structure ref in
  let env = Global.env () in
  let vc = match Environ.constant_opt_value env sp with
    | Some vc -> vc
    | None -> error_not_structure ref in
  let body = snd (splay_lambda (Global.env()) Evd.empty vc) in
  let f,args = match kind_of_term body with
    | App (f,args) -> f,args
    | _ -> error_not_structure ref in
  let indsp = match kind_of_term f with
    | Construct (indsp,1) -> indsp
    | _ -> error_not_structure ref in
  let s = try lookup_structure indsp with Not_found -> error_not_structure ref in
  let ntrue_projs = List.length (List.filter (fun x -> x) s.s_PROJKIND) in
  if s.s_EXPECTEDPARAM + ntrue_projs > Array.length args then
    error_not_structure ref;
  (sp,indsp)

let declare_canonical_structure ref =
  add_canonical_structure (check_and_decompose_canonical_structure ref)

let outCanonicalStructure x = fst (outCanonStruct x)

let lookup_canonical_conversion o = List.assoc o !object_table

let freeze () =
  !structure_table, !projection_table, !object_table

let unfreeze (s,p,o) = 
  structure_table := s; projection_table := p; object_table := o

let init () =
  structure_table := Indmap.empty; projection_table := Cmap.empty;
  object_table:=[]

let _ = init()

let _ = 
  Summary.declare_summary "objdefs"
    { Summary.freeze_function = freeze;
      Summary.unfreeze_function = unfreeze;
      Summary.init_function = init;
      Summary.survive_module = false;
      Summary.survive_section = false }
