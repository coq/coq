(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names

let scheme_map = Summary.ref Indmap.empty ~name:"Schemes"

let cache_one_scheme kind (ind,const) =
  let map = try Indmap.find ind !scheme_map with Not_found -> CString.Map.empty in
  scheme_map := Indmap.add ind (CString.Map.add kind const map) !scheme_map

let cache_scheme (kind,l) =
  Array.iter (cache_one_scheme kind) l

let subst_one_scheme subst (ind,const) =
  (* Remark: const is a def: the result of substitution is a constant *)
  (Mod_subst.subst_ind subst ind, Mod_subst.subst_constant subst const)

let subst_scheme (subst,(kind,l)) =
  (kind, CArray.Smart.map (subst_one_scheme subst) l)

let discharge_scheme (kind,l) =
  Some (kind, l)

let inScheme : string * (inductive * Constant.t) array -> Libobject.obj =
  let open Libobject in
  declare_object @@ superglobal_object "SCHEME"
    ~cache:cache_scheme
    ~subst:(Some subst_scheme)
    ~discharge:discharge_scheme

let declare_scheme kind indcl =
  Lib.add_leaf (inScheme (kind,indcl))

let lookup_scheme kind ind = CString.Map.find kind (Indmap.find ind !scheme_map)

let all_schemes () = Indmap.domain !scheme_map
