(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Util
open Names
open Declarations
open Nameops
open Libnames

let get_new_id locals id = 
  let rec get_id l id = 
    let dir = make_dirpath [id] in
      if not (Nametab.exists_module dir) then
	id
      else
	get_id (id::l) (Nameops.next_ident_away id l)
  in
    get_id (List.map snd locals) id

let rec print_local_modpath locals = function
  | MPbound mbid -> pr_id (List.assoc mbid locals)
  | MPdot(mp,l) ->
      print_local_modpath locals mp ++ str "." ++ pr_lab l
  | MPself _ | MPfile _ -> raise Not_found

let print_modpath locals mp = 
  try (* must be with let because streams are lazy! *)
    let qid = Nametab.shortest_qualid_of_module mp in 
      pr_qualid qid
  with
    | Not_found -> print_local_modpath locals mp

let print_kn locals kn = 
  try
    let qid = Nametab.shortest_qualid_of_modtype kn in 
      pr_qualid qid
  with
      Not_found -> 
	let (mp,_,l) = repr_kn kn in
	  print_local_modpath locals mp ++ str"." ++ pr_lab l

let rec flatten_app mexpr l = match mexpr with
  | MEBapply (mexpr,marg,_) -> flatten_app mexpr (marg::l)
  | mexpr -> mexpr::l

let rec print_module name locals with_body mb =
  let body = match mb.mod_equiv, with_body, mb.mod_expr with 
    | None, false, _ 
    | None, true, None -> mt()
    | None, true, Some mexpr -> 
	spc () ++ str ":= " ++ print_modexpr locals mexpr
    | Some mp, _, _ -> str " == " ++ print_modpath locals mp
  in
  hv 2 (str "Module " ++ name ++ spc () ++ str": " ++ 
	print_modtype locals mb.mod_type ++ body)

and print_modtype locals mty = match mty with
  | MTBident kn -> print_kn locals kn
  | MTBfunsig (mbid,mtb1,mtb2) ->
(*    let env' = Modops.add_module (MPbid mbid) (Modops.body_of_type mtb) env 
      in *) 
      let locals' = (mbid, get_new_id locals (id_of_mbid mbid))::locals in
      hov 2 (str "Funsig" ++ spc () ++ str "(" ++ 
        pr_id (id_of_mbid mbid) ++ str " : " ++ print_modtype locals mtb1 ++ 
      str ")" ++ spc() ++ print_modtype locals' mtb2)
  | MTBsig (msid,sign) -> 
      hv 2 (str "Sig" ++ spc () ++ print_sig locals msid sign ++ brk (1,-2) ++ str "End")

and print_sig locals msid sign = 
  let print_spec (l,spec) = (match spec with
    | SPBconst {const_body=Some _; const_opaque=false} -> str "Definition "
    | SPBconst {const_body=None}
    | SPBconst {const_opaque=true} -> str "Parameter "
    | SPBmind _ -> str "Inductive "
    | SPBmodule _ -> str "Module "
    | SPBmodtype _ -> str "Module Type ") ++ str (string_of_label l)
  in
    prlist_with_sep spc print_spec sign

and print_struct locals msid struc = 
  let print_body (l,body) = (match body with
    | SEBconst {const_body=Some _; const_opaque=false} -> str "Definition "
    | SEBconst {const_body=Some _; const_opaque=true} -> str "Theorem "
    | SEBconst {const_body=None} -> str "Parameter "
    | SEBmind _ -> str "Inductive "
    | SEBmodule _ -> str "Module "
    | SEBmodtype _ -> str "Module Type ") ++ str (string_of_label l)
  in
    prlist_with_sep spc print_body struc

and print_modexpr locals mexpr = match mexpr with 
  | MEBident mp -> print_modpath locals mp
  | MEBfunctor (mbid,mty,mexpr) ->
(*    let env' = Modops.add_module (MPbid mbid) (Modops.body_of_type mtb) env 
      in *)
      let locals' = (mbid, get_new_id locals (id_of_mbid mbid))::locals in
      hov 2 (str "Functor" ++ spc() ++ str"[" ++ pr_id(id_of_mbid mbid) ++ 
	     str ":" ++ print_modtype locals mty ++ 
      str "]" ++ spc () ++ print_modexpr locals' mexpr)
  | MEBstruct (msid, struc) -> 
      hv 2 (str "Struct" ++ spc () ++ print_struct locals msid struc ++ brk (1,-2) ++ str "End")
  | MEBapply (mexpr,marg,_) -> 
      let lapp = flatten_app mexpr [marg] in
	hov 3 (str"(" ++ prlist_with_sep spc (print_modexpr locals) lapp ++ str")")



let rec printable_body dir =     
  let dir = dirpath_prefix dir in
    dir = empty_dirpath || 
    try 
      match Nametab.locate_dir (qualid_of_dirpath dir) with
	  DirOpenModtype _ -> false
	| DirModule _ | DirOpenModule _ -> printable_body dir
	| _ -> true
    with 
	Not_found -> true


let print_module with_body mp = 
  let name = print_modpath [] mp in
    print_module name [] with_body (Global.lookup_module mp) ++ fnl ()

let print_modtype kn = 
  let name = print_kn [] kn in
    str "Module Type " ++ name ++ str " = " ++ 
      print_modtype [] (Global.lookup_modtype kn) ++ fnl ()
