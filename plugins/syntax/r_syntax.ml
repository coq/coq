(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Names
open Glob_term
open Bigint

(* Poor's man DECLARE PLUGIN *)
let __coq_plugin_name = "r_syntax_plugin"
let () = Mltop.add_known_module __coq_plugin_name

exception Non_closed_number

(**********************************************************************)
(* Parsing positive via scopes                                        *)
(**********************************************************************)

let binnums = ["Coq";"Numbers";"BinNums"]

let make_dir l = DirPath.make (List.rev_map Id.of_string l)
let make_path dir id = Libnames.make_path (make_dir dir) (Id.of_string id)

let is_gr c gr = match DAst.get c with
| GRef (r, _) -> GlobRef.equal r gr
| _ -> false

let positive_modpath = MPfile (make_dir binnums)

let positive_kn = MutInd.make2 positive_modpath (Label.make "positive")
let path_of_xI = ((positive_kn,0),1)
let path_of_xO = ((positive_kn,0),2)
let path_of_xH = ((positive_kn,0),3)
let glob_xI = GlobRef.ConstructRef path_of_xI
let glob_xO = GlobRef.ConstructRef path_of_xO
let glob_xH = GlobRef.ConstructRef path_of_xH

let pos_of_bignat ?loc x =
  let ref_xI = DAst.make @@ GRef (glob_xI, None) in
  let ref_xH = DAst.make @@ GRef (glob_xH, None) in
  let ref_xO = DAst.make @@ GRef (glob_xO, None) in
  let rec pos_of x =
    match div2_with_rest x with
      | (q,false) -> DAst.make @@ GApp (ref_xO,[pos_of q])
      | (q,true) when not (Bigint.equal q zero) -> DAst.make @@ GApp (ref_xI,[pos_of q])
      | (q,true) -> ref_xH
  in
  pos_of x

(**********************************************************************)
(* Printing positive via scopes                                       *)
(**********************************************************************)

let rec bignat_of_pos c = match DAst.get c with
  | GApp (r, [a]) when is_gr r glob_xO -> mult_2(bignat_of_pos a)
  | GApp (r, [a]) when is_gr r glob_xI -> add_1(mult_2(bignat_of_pos a))
  | GRef (a, _) when GlobRef.equal a glob_xH -> Bigint.one
  | _ -> raise Non_closed_number

(**********************************************************************)
(* Parsing Z via scopes                                               *)
(**********************************************************************)

let z_kn = MutInd.make2 positive_modpath (Label.make "Z")
let path_of_ZERO = ((z_kn,0),1)
let path_of_POS = ((z_kn,0),2)
let path_of_NEG = ((z_kn,0),3)
let glob_ZERO = GlobRef.ConstructRef path_of_ZERO
let glob_POS = GlobRef.ConstructRef path_of_POS
let glob_NEG = GlobRef.ConstructRef path_of_NEG

let z_of_int ?loc n =
  if not (Bigint.equal n zero) then
    let sgn, n =
      if is_pos_or_zero n then glob_POS, n else glob_NEG, Bigint.neg n in
    DAst.make @@ GApp(DAst.make @@ GRef (sgn,None), [pos_of_bignat ?loc n])
  else
    DAst.make @@ GRef (glob_ZERO, None)

(**********************************************************************)
(* Printing Z via scopes                                              *)
(**********************************************************************)

let bigint_of_z c = match DAst.get c with
  | GApp (r,[a]) when is_gr r glob_POS -> bignat_of_pos a
  | GApp (r,[a]) when is_gr r glob_NEG -> Bigint.neg (bignat_of_pos a)
  | GRef (a, _) when GlobRef.equal a glob_ZERO -> Bigint.zero
  | _ -> raise Non_closed_number

(**********************************************************************)
(* Parsing R via scopes                                               *)
(**********************************************************************)

let rdefinitions = ["Coq";"Reals";"Rdefinitions"]
let r_modpath = MPfile (make_dir rdefinitions)
let r_base_modpath = MPdot (r_modpath, Label.make "RbaseSymbolsImpl")
let r_path = make_path ["Coq";"Reals";"Rdefinitions";"RbaseSymbolsImpl"] "R"

let glob_IZR = GlobRef.ConstRef (Constant.make2 r_modpath @@ Label.make "IZR")
let glob_Rmult = GlobRef.ConstRef (Constant.make2 r_base_modpath @@ Label.make "Rmult")
let glob_Rdiv = GlobRef.ConstRef (Constant.make2 r_modpath @@ Label.make "Rdiv")

let binintdef = ["Coq";"ZArith";"BinIntDef"]
let z_modpath = MPdot (MPfile (make_dir binintdef), Label.make "Z")

let glob_pow_pos = GlobRef.ConstRef (Constant.make2 z_modpath @@ Label.make "pow_pos")

let r_of_rawnum ?loc n =
  let n,e = NumTok.Signed.to_bigint_and_exponent n in
  let e,p = NumTok.(match e with EDec e -> e, 10 | EBin e -> e, 2) in
  let izr z =
    DAst.make @@ GApp (DAst.make @@ GRef(glob_IZR,None), [z]) in
  let rmult r r' =
    DAst.make @@ GApp (DAst.make @@ GRef(glob_Rmult,None), [r; r']) in
  let rdiv r r' =
    DAst.make @@ GApp (DAst.make @@ GRef(glob_Rdiv,None), [r; r']) in
  let pow p e =
    let p = z_of_int ?loc (Bigint.of_int p) in
    let e = pos_of_bignat e in
    DAst.make @@ GApp (DAst.make @@ GRef(glob_pow_pos,None), [p; e]) in
  let n =
    izr (z_of_int ?loc n) in
  if Bigint.is_strictly_pos e then rmult n (izr (pow p e))
  else if Bigint.is_strictly_neg e then rdiv n (izr (pow p (neg e)))
  else n  (* e = 0 *)

(**********************************************************************)
(* Printing R via scopes                                              *)
(**********************************************************************)

let rawnum_of_r c =
  (* print i * 10^e, precondition: e <> 0 *)
  let numTok_of_int_exp i e =
    (* choose between 123e-2 and 1.23, this is purely heuristic
       and doesn't play any soundness role *)
    let choose_exponent =
      if Bigint.is_strictly_pos e then
        true  (* don't print 12 * 10^2 as 1200 to distinguish them *)
      else
        let i = Bigint.to_string i in
        let li = if i.[0] = '-' then String.length i - 1 else String.length i in
        let e = Bigint.neg e in
        let le = String.length (Bigint.to_string e) in
        Bigint.(less_than (add (of_int li) (of_int le)) e) in
    (* print 123 * 10^-2 as 123e-2 *)
    let numTok_exponent () =
      NumTok.Signed.of_bigint_and_exponent i (NumTok.EDec e) in
    (* print 123 * 10^-2 as 1.23, precondition e < 0 *)
    let numTok_dot () =
      let s, i =
        if Bigint.is_pos_or_zero i then NumTok.SPlus, Bigint.to_string i
        else NumTok.SMinus, Bigint.(to_string (neg i)) in
      let ni = String.length i in
      let e = - (Bigint.to_int e) in
      assert (e > 0);
      let i, f =
        if e < ni then String.sub i 0 (ni - e), String.sub i (ni - e) e
        else "0", String.make (e - ni) '0' ^ i in
      let i = s, NumTok.UnsignedNat.of_string i in
      let f = NumTok.UnsignedNat.of_string f in
      NumTok.Signed.of_int_frac_and_exponent i (Some f) None in
    if choose_exponent then numTok_exponent () else numTok_dot () in
  match DAst.get c with
  | GApp (r, [a]) when is_gr r glob_IZR ->
     let n = bigint_of_z a in
     NumTok.(Signed.of_bigint CDec n)
  | GApp (md,  [l; r]) when is_gr md glob_Rmult || is_gr md glob_Rdiv ->
     begin match DAst.get l, DAst.get r with
     | GApp (i, [l]), GApp (i', [r])
          when is_gr i glob_IZR && is_gr i' glob_IZR ->
        begin match DAst.get r with
        | GApp (p, [t; e]) when is_gr p glob_pow_pos ->
           let t = bigint_of_z t in
           if not (Bigint.(equal t (of_int 10))) then
             raise Non_closed_number
           else
             let i = bigint_of_z l in
             let e = bignat_of_pos e in
             let e = if is_gr md glob_Rdiv then neg e else e in
             numTok_of_int_exp i e
        | _ -> raise Non_closed_number
        end
     | _ -> raise Non_closed_number
     end
  | _ -> raise Non_closed_number

let uninterp_r (AnyGlobConstr p) =
  try
    Some (rawnum_of_r p)
  with Non_closed_number ->
    None

open Notation

let at_declare_ml_module f x =
  Mltop.declare_cache_obj (fun () -> f x) __coq_plugin_name

let r_scope = "R_scope"

let _ =
  register_rawnumeral_interpretation r_scope (r_of_rawnum,uninterp_r);
  at_declare_ml_module enable_prim_token_interpretation
    { pt_local = false;
      pt_scope = r_scope;
      pt_interp_info = Uid r_scope;
      pt_required = (r_path,["Coq";"Reals";"Rdefinitions"]);
      pt_refs = [glob_IZR; glob_Rmult; glob_Rdiv];
      pt_in_match = false }
