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
open Glob_term

(* Poor's man DECLARE PLUGIN *)
let __coq_plugin_name = "float_syntax_plugin"
let () = Mltop.add_known_module __coq_plugin_name

(*** Constants for locating float constructors ***)

let make_dir l = DirPath.make (List.rev_map Id.of_string l)
let make_path dir id = Libnames.make_path (make_dir dir) (Id.of_string id)

(*** Parsing for float in digital notation ***)

let warn_inexact_float =
  CWarnings.create ~name:"inexact-float" ~category:"parsing"
    (fun (sn, f) ->
      Pp.strbrk
        (Printf.sprintf
           "The constant %s is not a binary64 floating-point value. \
            A closest value %s will be used and unambiguously printed %s."
           sn (Float64.to_hex_string f) (Float64.to_string f)))

let interp_float ?loc n =
  let sn = NumTok.Signed.to_string n in
  let f = Float64.of_string sn in
  (* return true when f is not exactly equal to n,
     this is only used to decide whether or not to display a warning
     and does not play any actual role in the parsing *)
  let inexact () = match Float64.classify f with
    | Float64.(PInf | NInf | NaN) -> true
    | Float64.(PZero | NZero) -> not (NumTok.Signed.is_zero n)
    | Float64.(PNormal | NNormal | PSubn | NSubn) ->
       let m, e =
         let (_, i), f, e = NumTok.Signed.to_int_frac_and_exponent n in
         let i = NumTok.UnsignedNat.to_string i in
         let f = match f with
           | None -> "" | Some f -> NumTok.UnsignedNat.to_string f in
         let e = match e with
           | None -> "0" | Some e -> NumTok.SignedNat.to_string e in
         Bigint.of_string (i ^ f),
         (try int_of_string e with Failure _ -> 0) - String.length f in
       let m', e' =
         let m', e' = Float64.frshiftexp f in
         let m' = Float64.normfr_mantissa m' in
         let e' = Uint63.to_int_min e' 4096 - Float64.eshift - 53 in
         Bigint.of_string (Uint63.to_string m'),
         e' in
       let c2, c5 = Bigint.(of_int 2, of_int 5) in
       (* check m*5^e <> m'*2^e' *)
       let check m e m' e' =
         not (Bigint.(equal (mult m (pow c5 e)) (mult m' (pow c2 e')))) in
       (* check m*5^e*2^e' <> m' *)
       let check' m e e' m' =
         not (Bigint.(equal (mult (mult m (pow c5 e)) (pow c2 e')) m')) in
       (* we now have to check m*10^e <> m'*2^e' *)
       if e >= 0 then
         if e <= e' then check m e m' (e' - e)
         else check' m e (e - e') m'
       else  (* e < 0 *)
         if e' <= e then check m' (-e) m (e - e')
         else check' m' (-e) (e' - e) m in
  if NumTok.(Signed.classify n = CDec) && inexact () then
    warn_inexact_float ?loc (sn, f);
  DAst.make ?loc (GFloat f)

(* Pretty printing is already handled in constrextern.ml *)

let uninterp_float _ = None

(* Actually declares the interpreter for float *)

open Notation

let at_declare_ml_module f x =
  Mltop.declare_cache_obj (fun () -> f x) __coq_plugin_name

let float_module = ["Coq"; "Floats"; "PrimFloat"]
let float_path = make_path float_module "float"
let float_scope = "float_scope"

let _ =
  register_rawnumeral_interpretation float_scope (interp_float,uninterp_float);
  at_declare_ml_module enable_prim_token_interpretation
    { pt_local = false;
      pt_scope = float_scope;
      pt_interp_info = Uid float_scope;
      pt_required = (float_path,float_module);
      pt_refs = [];
      pt_in_match = false }
