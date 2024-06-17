(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Ppxlib.Ast

let is_any_pat ~default p = match p.ppat_desc with
  | Ppat_any -> Some default
  | Ppat_var s -> Some s.txt
  | _ -> None

let is_raise_f e = match e.pexp_desc with
  | Pexp_ident {txt=id} -> begin match id with
      | Lident s | Ldot (_, s) -> begin match s with
          | "raise" | "reraise" | "iraise" -> true
          | _ -> false
        end
      | Lapply _ -> false
    end
  | _ -> false

let rec always_raises e = match e.pexp_desc with
  | Pexp_apply (f, args) ->
    List.exists (fun (label, _) -> match label with
        | Nolabel -> true
        | Labelled _ | Optional _ -> false)
      args
    && is_raise_f f
  | Pexp_let (_,_,e)
  | Pexp_sequence (_,e)
  | Pexp_constraint (e,_)
  | Pexp_coerce (e,_,_)
  | Pexp_letmodule (_,_,e)
  | Pexp_letexception (_,e)
  | Pexp_open (_,e)
    -> always_raises e

  | Pexp_unreachable -> true

  | _ -> false

let allow_attribute att = att.attr_name.txt = "coqlint.allow_catchall"

let check_case ~is_try case =
  let { Parsetree.pc_lhs = pat
      ; pc_guard; pc_rhs } = case
  in
  if List.exists allow_attribute pat.ppat_attributes then ()
  else
    let is_any_exn_pat =
      if is_try then is_any_pat pat ~default:"exn"
      else match pat.ppat_desc with
        | Ppat_exception p -> is_any_pat p ~default:"exn"
        | _ -> None
    in
    begin match is_any_exn_pat, pc_guard with
    | None, _ | _, Some _ -> ()
    | Some id, None ->
      if always_raises pc_rhs then ()
      else
        let repl =
          Printf.sprintf "%s%s when CErrors.noncritical %s"
            (if is_try then "" else "exception ")
            id id
        in
        Ppxlib.Driver.register_correction ~loc:pat.ppat_loc ~repl
    end


let detect_catchall = object
  inherit Ppxlib.Ast_traverse.iter as super

  method! expression e =
    super#expression e;
    match e with
    | { pexp_desc = Pexp_match (_, cases) } ->
      cases |> List.iter (check_case~is_try:false)
    | { pexp_desc = Pexp_try (_, cases) } ->
      cases |> List.iter (check_case ~is_try:true)
    | _ -> ()
end

let impl s =
  detect_catchall#structure s; s

let () =
  Ppxlib.Driver.register_transformation
    "unprotected exception catchall"
    ~impl
