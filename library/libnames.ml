(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

open Pp
open Util
open Names
open Nameops
open Term
open Mod_subst

(*s Global reference is a kernel side type for all references together *)
type global_reference =
  | VarRef of variable
  | ConstRef of constant
  | IndRef of inductive
  | ConstructRef of constructor

let isVarRef = function VarRef _ -> true | _ -> false

let subst_global subst ref = match ref with
  | VarRef var -> ref, mkVar var
  | ConstRef kn ->
     let kn',t = subst_con subst kn in
      if kn==kn' then ref, mkConst kn else ConstRef kn', t
  | IndRef (kn,i) ->
      let kn' = subst_kn subst kn in
      if kn==kn' then ref, mkInd (kn,i) else IndRef(kn',i), mkInd (kn',i)
  | ConstructRef ((kn,i),j) ->
      let kn' = subst_kn subst kn in 
      if kn==kn' then ref, mkConstruct ((kn,i),j)
      else ConstructRef ((kn',i),j), mkConstruct ((kn',i),j)

let global_of_constr c = match kind_of_term c with
  | Const sp -> ConstRef sp
  | Ind ind_sp -> IndRef ind_sp
  | Construct cstr_cp -> ConstructRef cstr_cp
  | Var id -> VarRef id
  |  _ -> raise Not_found

let constr_of_global = function
  | VarRef id -> mkVar id
  | ConstRef sp -> mkConst sp
  | ConstructRef sp -> mkConstruct sp
  | IndRef sp -> mkInd sp

let constr_of_reference = constr_of_global
let reference_of_constr = global_of_constr

module RefOrdered =
  struct
    type t = global_reference
    let compare = Pervasives.compare
  end

module Refset = Set.Make(RefOrdered)
module Refmap = Map.Make(RefOrdered)

let inductives_table = ref Indmap.empty

(**********************************************)

let pr_dirpath sl = (str (string_of_dirpath sl))

(*s Operations on dirpaths *)

(* Pop the last n module idents *)
let extract_dirpath_prefix n dir =
  make_dirpath (list_skipn n (repr_dirpath dir))

let dirpath_prefix p = match repr_dirpath p with
  | [] -> anomaly "dirpath_prefix: empty dirpath"
  | _::l -> make_dirpath l

let is_dirpath_prefix_of d1 d2 =
  list_prefix_of (List.rev (repr_dirpath d1)) (List.rev (repr_dirpath d2))

let chop_dirpath n d =
  let d1,d2 = list_chop n (List.rev (repr_dirpath d)) in
    make_dirpath (List.rev d1), make_dirpath (List.rev d2)

let drop_dirpath_prefix d1 d2 =
  let d = Util.list_drop_prefix (List.rev (repr_dirpath d1)) (List.rev (repr_dirpath d2)) in
    make_dirpath (List.rev d)

let append_dirpath d1 d2 = make_dirpath (repr_dirpath d2 @ repr_dirpath d1)

(* To know how qualified a name should be to be understood in the current env*)
let add_dirpath_prefix id d = make_dirpath (repr_dirpath d @ [id])

let split_dirpath d =
  let l = repr_dirpath d in (make_dirpath (List.tl l), List.hd l)

let extend_dirpath p id = make_dirpath (id :: repr_dirpath p)


(*
let path_of_constructor env ((sp,tyi),ind) =
   let mib = Environ.lookup_mind sp env in
   let mip = mib.mind_packets.(tyi) in 
   let (pa,_) = repr_path sp in 
   Names.make_path pa (mip.mind_consnames.(ind-1))

let path_of_inductive env (sp,tyi) =
  if tyi = 0 then sp
  else
    let mib = Environ.lookup_mind sp env in
    let mip = mib.mind_packets.(tyi) in 
    let (pa,_) = repr_path sp in 
    Names.make_path pa (mip.mind_typename) 
*)
(* parsing *)
let parse_dir s =
  let len = String.length s in
  let rec decoupe_dirs dirs n =
    if n>=len then dirs else
    let pos =
      try
	String.index_from s n '.' 
      with Not_found -> len
    in
    let dir = String.sub s n (pos-n) in
      decoupe_dirs ((id_of_string dir)::dirs) (pos+1)	  
  in
    decoupe_dirs [] 0

let dirpath_of_string s = 
  match parse_dir s with
      [] -> invalid_arg "dirpath_of_string"
    | dir -> make_dirpath dir

module Dirset = Set.Make(struct type t = dir_path let compare = compare end)
module Dirmap = Map.Make(struct type t = dir_path let compare = compare end)

(*s Section paths are absolute names *)

type section_path = {
  dirpath : dir_path ;
  basename : identifier }

let make_path pa id = { dirpath = pa; basename = id }
let repr_path { dirpath = pa; basename = id } = (pa,id)

(* parsing and printing of section paths *)
let string_of_path sp =
  let (sl,id) = repr_path sp in
  if repr_dirpath sl = [] then string_of_id id
  else (string_of_dirpath sl) ^ "." ^ (string_of_id id)

let sp_ord sp1 sp2 =
  let (p1,id1) = repr_path sp1
  and (p2,id2) = repr_path sp2 in
  let p_bit = compare p1 p2 in
  if p_bit = 0 then id_ord id1 id2 else p_bit

module SpOrdered =
  struct
    type t = section_path
    let compare = sp_ord
  end

module Spset = Set.Make(SpOrdered)
module Sppred = Predicate.Make(SpOrdered)
module Spmap = Map.Make(SpOrdered)

let dirpath sp = let (p,_) = repr_path sp in p
let basename sp = let (_,id) = repr_path sp in id

let path_of_string s =
  try
    let dir, id = split_dirpath (dirpath_of_string s) in
    make_path dir id
  with
    | Invalid_argument _ -> invalid_arg "path_of_string"

let pr_sp sp = str (string_of_path sp) 

let restrict_path n sp =
  let dir, s = repr_path sp in
  let dir' = list_firstn n (repr_dirpath dir) in
  make_path (make_dirpath dir') s

type extended_global_reference =
  | TrueGlobal of global_reference
  | SyntacticDef of kernel_name

let encode_kn dir id = make_kn (MPfile dir) empty_dirpath (label_of_id id)

let encode_con dir id = make_con (MPfile dir) empty_dirpath (label_of_id id)

let decode_kn kn = 
  let mp,sec_dir,l = repr_kn kn in
    match mp,(repr_dirpath sec_dir) with
	MPfile dir,[] -> (dir,id_of_label l)
      | _ , [] -> anomaly "MPfile expected!"
      | _ -> anomaly "Section part should be empty!"

let decode_con kn = 
  let mp,sec_dir,l = repr_con kn in
    match mp,(repr_dirpath sec_dir) with
	MPfile dir,[] -> (dir,id_of_label l)
      | _ , [] -> anomaly "MPfile expected!"
      | _ -> anomaly "Section part should be empty!"

(*s qualified names *)
type qualid = section_path

let make_qualid = make_path
let repr_qualid = repr_path

let string_of_qualid = string_of_path
let pr_qualid = pr_sp

let qualid_of_string = path_of_string

let qualid_of_sp sp = sp
let make_short_qualid id = make_qualid empty_dirpath id
let qualid_of_dirpath dir = 
  let (l,a) = split_dirpath dir in
  make_qualid l a

type object_name = section_path * kernel_name

type object_prefix = dir_path * (module_path * dir_path)

let make_oname (dirpath,(mp,dir)) id = 
  make_path dirpath id, make_kn mp dir (label_of_id id)

(* to this type are mapped dir_path's in the nametab *)
type global_dir_reference = 
  | DirOpenModule of object_prefix
  | DirOpenModtype of object_prefix
  | DirOpenSection of object_prefix
  | DirModule of object_prefix
  | DirClosedSection of dir_path
      (* this won't last long I hope! *)

(*  | ModRef mp ->
      let mp' = subst_modpath subst mp in if mp==mp' then ref else
          ModRef mp'
  | ModTypeRef kn ->
      let kn' = subst_kernel_name subst kn in if kn==kn' then ref else
          ModTypeRef kn'
*)

type reference = 
  | Qualid of qualid located
  | Ident of identifier located

let qualid_of_reference = function
  | Qualid (loc,qid) -> loc, qid
  | Ident (loc,id) -> loc, make_short_qualid id

let string_of_reference = function
  | Qualid (loc,qid) -> string_of_qualid qid
  | Ident (loc,id) -> string_of_id id

let pr_reference = function 
  | Qualid (_,qid) -> pr_qualid qid
  | Ident (_,id) -> pr_id id

let loc_of_reference = function
  | Qualid (loc,qid) -> loc
  | Ident (loc,id) -> loc

(* popping one level of section in global names *)

let pop_con con =
  let (mp,dir,l) = repr_con con in
  Names.make_con mp (dirpath_prefix dir) l

let pop_kn kn =
  let (mp,dir,l) = repr_kn kn in
  Names.make_kn mp (dirpath_prefix dir) l

let pop_global_reference = function
  | ConstRef con -> ConstRef (pop_con con)
  | IndRef (kn,i) -> IndRef (pop_kn kn,i)
  | ConstructRef ((kn,i),j) -> ConstructRef ((pop_kn kn,i),j)
  | VarRef id -> anomaly "VarRef not poppable"
