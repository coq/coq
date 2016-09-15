(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)


(*i camlp4deps: "grammar/grammar.cma" i*)
open Names
open Ascii_syntax_plugin.Ascii_syntax
open String_syntax_plugin.String_syntax
open Pcoq
open Pcoq.Prim
open Pcoq.Tactic
open Constrexpr
open Constrintern
open Constrextern
open Glob_term
open Tacexpr
open Pp

let __coq_plugin_name = "string_ident_plugin"
let () = Mltop.add_known_module __coq_plugin_name

let id_from_string_constr (idstr : constr_expr) : Tacexpr.raw_tactic_arg =
  let str_glob_constr : glob_constr =
    intern_constr Environ.empty_env idstr
  in
  match (uninterp_string str_glob_constr) with
  | Some s ->
      if not (Id.is_valid s) then
      begin
      CErrors.user_err_loc (Loc.ghost, "",
        (str "The string '" ++ str s ++ str "' is not a valid identifier."))
      end
      else
        TacExactId (Id.of_string s)
  | None -> raise Not_found

let string_constr_from_ident (id : Id.t) : raw_tactic_arg =
  let id_str_glob_constr = interp_string Loc.ghost (Id.to_string id) in
  let id_str_constr_expr = extern_glob_constr Id.Set.empty id_str_glob_constr in
  Tacexpr.TacPretype id_str_constr_expr

GEXTEND Gram tactic_arg :
  [ [IDENT "ident_of_string"; x = uconstr -> id_from_string_constr x]];
END

GEXTEND Gram tactic_arg:
  [ [IDENT "string_of_ident"; x = ident -> string_constr_from_ident x]];
END
