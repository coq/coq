(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

open Pp
open Util
open Names
open Declarations
open Nameops
open Libnames

let print_modpath env mp = 
  try (* must be with let because streams are lazy! *)
    let qid = Nametab.shortest_qualid_of_module mp in pr_qualid qid
  with
    | Not_found as e -> 
	match mp with 
	  | MPbound mbid -> Nameops.pr_id (id_of_mbid mbid)
	  | _ -> raise e

let print_kn env kn = 
  let qid = Nametab.shortest_qualid_of_modtype kn in 
    pr_qualid qid

let rec flatten_app mexpr l = match mexpr with
  | MEBapply (mexpr,marg,_) -> flatten_app mexpr (marg::l)
  | mexpr -> mexpr::l

let rec print_module name env with_body mb =
  let body = match mb.mod_equiv, with_body, mb.mod_expr with 
    | None, false, _ 
    | None, true, None -> mt()
    | None, true, Some mexpr -> str " := " ++ print_modexpr env mexpr
    | Some mp, _, _ -> str " == " ++ print_modpath env mp
  in
  str "Module " ++ name ++ str" : " ++ print_modtype env mb.mod_type ++ body

and print_modtype env mty = match mty with
  | MTBident kn -> print_kn env kn
  | MTBfunsig (mbid,mtb1,mtb2) ->
(*      let env' = Modops.add_module (MPbid mbid) (Modops.body_of_type mtb) env 
      in *)
      hov 2 (str "Funsig" ++ spc () ++ str "(" ++ 
        pr_id (id_of_mbid mbid) ++ str " : " ++ print_modtype env mtb1 ++ 
      str ")" ++ spc() ++ print_modtype env mtb2)
  | MTBsig (msid,sign) -> 
      hv 2 (str "Sig" ++ spc () ++ print_sig env msid sign ++ brk (1,-2) ++ str "End")

and print_sig env msid sign = 
  let print_spec (l,spec) = (match spec with
    | SPBconst _ -> str "Definition "
    | SPBmind _ -> str "Inductive "
    | SPBmodule _ -> str "Module "
    | SPBmodtype _ -> str "Module Type ") ++ str (string_of_label l)
  in
    prlist_with_sep spc print_spec sign

and print_struct env msid struc = 
  let print_body (l,body) = (match body with
    | SEBconst _ -> str "Definition "
    | SEBmind _ -> str "Inductive "
    | SEBmodule _ -> str "Module "
    | SEBmodtype _ -> str "Module Type ") ++ str (string_of_label l)
  in
    prlist_with_sep spc print_body struc

and print_modexpr env mexpr = match mexpr with 
  | MEBident mp -> print_modpath env mp
  | MEBfunctor (mbid,mty,mexpr) ->
(*      let env' = Modops.add_module (MPbid mbid) (Modops.body_of_type mtb) env 
      in *)
      hov 2 (str "Functor" ++ spc() ++ str"[" ++ pr_id(id_of_mbid mbid) ++ 
	     str ":" ++ print_modtype env mty ++ 
      str "]" ++ spc () ++ print_modexpr env mexpr)
  | MEBstruct (msid, struc) -> 
      hv 2 (str "Struct" ++ spc () ++ print_struct env msid struc ++ brk (1,-2) ++ str "End")
  | MEBapply (mexpr,marg,_) -> 
      let lapp = flatten_app mexpr [marg] in
	hov 3 (str"(" ++ prlist_with_sep spc (print_modexpr env) lapp ++ str")")



let print_module with_body mp = 
  let env = Global.env() in
  let name = print_modpath env mp in
    print_module name env with_body (Environ.lookup_module mp env) ++ fnl ()

let print_modtype kn = 
  let env = Global.env() in
  let name = print_kn env kn in
    str "Module Type " ++ name ++ str " = " ++
    print_modtype env (Environ.lookup_modtype kn env) ++ fnl ()
