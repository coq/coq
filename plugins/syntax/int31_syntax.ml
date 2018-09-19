(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)


(* Poor's man DECLARE PLUGIN *)
let __coq_plugin_name = "int31_syntax_plugin"
let () = Mltop.add_known_module __coq_plugin_name

(* digit-based syntax for int31 *)

open Bigint
open Names
open Globnames
open Glob_term

(*** Constants for locating int31 constructors ***)

let make_dir l = DirPath.make (List.rev_map Id.of_string l)
let make_path dir id = Libnames.make_path (make_dir dir) (Id.of_string id)

let is_gr c gr = match DAst.get c with
| GRef (r, _) -> GlobRef.equal r gr
| _ -> false

let make_mind mp id = Names.MutInd.make2 mp (Label.make id)
let make_mind_mpfile dir id = make_mind (ModPath.MPfile (make_dir dir)) id
let make_mind_mpdot dir modname id =
  let mp = ModPath.MPdot (ModPath.MPfile (make_dir dir), Label.make modname)
  in make_mind mp id


(* int31 stuff *)
let int31_module = ["Coq"; "Numbers"; "Cyclic"; "Int31"; "Int31"]
let int31_path = make_path int31_module "int31"
let int31_id = make_mind_mpfile int31_module
let int31_scope = "int31_scope"

let int31_construct = ConstructRef ((int31_id "int31",0),1)

let int31_0 = ConstructRef ((int31_id "digits",0),1)
let int31_1 = ConstructRef ((int31_id "digits",0),2)

(*** Definition of the Non_closed exception, used in the pretty printing ***)
exception Non_closed

(*** Parsing for int31 in digital notation ***)

(* parses a *non-negative* integer (from bigint.ml) into an int31
   wraps modulo 2^31 *)
let int31_of_pos_bigint ?loc n =
  let ref_construct = DAst.make ?loc (GRef (int31_construct, None)) in
  let ref_0 = DAst.make ?loc (GRef (int31_0, None)) in
  let ref_1 = DAst.make ?loc (GRef (int31_1, None)) in
  let rec args counter n =
    if counter <= 0 then
      []
    else
      let (q,r) = div2_with_rest n in
	(if r then ref_1 else ref_0)::(args (counter-1) q)
  in
  DAst.make ?loc (GApp (ref_construct, List.rev (args 31 n)))

let error_negative ?loc =
  CErrors.user_err ?loc ~hdr:"interp_int31" (Pp.str "int31 are only non-negative numbers.")

let interp_int31 ?loc n =
  if is_pos_or_zero n then
    int31_of_pos_bigint ?loc n
  else
    error_negative ?loc

(* Pretty prints an int31 *)

let bigint_of_int31 =
  let rec args_parsing args cur =
    match args with
      | [] -> cur
      | r::l when is_gr r int31_0 -> args_parsing l (mult_2 cur)
      | r::l when is_gr r int31_1 -> args_parsing l (add_1 (mult_2 cur))
      | _ -> raise Non_closed
  in
  fun c -> match DAst.get c with
  | GApp (r, args) when is_gr r int31_construct -> args_parsing args zero
  | _ -> raise Non_closed

let uninterp_int31 (AnyGlobConstr i) =
  try
    Some (bigint_of_int31 i)
  with Non_closed ->
    None

open Notation

let at_declare_ml_module f x =
  Mltop.declare_cache_obj (fun () -> f x) __coq_plugin_name

(* Actually declares the interpreter for int31 *)

let _ =
  register_bignumeral_interpretation int31_scope (interp_int31,uninterp_int31);
  at_declare_ml_module enable_prim_token_interpretation
    { pt_local = false;
      pt_scope = int31_scope;
      pt_interp_info = Uid int31_scope;
      pt_required = (int31_path,int31_module);
      pt_refs = [int31_construct];
      pt_in_match = true }
