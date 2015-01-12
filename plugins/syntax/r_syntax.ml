(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util
open Names
open Globnames

exception Non_closed_number

(**********************************************************************)
(* Parsing R via scopes                                               *)
(**********************************************************************)

open Glob_term
open Bigint

let make_dir l = DirPath.make (List.rev_map Id.of_string l)
let rdefinitions = make_dir ["Coq";"Reals";"Rdefinitions"]
let make_path dir id = Libnames.make_path dir (Id.of_string id)

let r_path = make_path rdefinitions "R"

(* TODO: temporary hack *)
let make_path dir id = Globnames.encode_con dir (Id.of_string id)

let r_kn = make_path rdefinitions "R"
let glob_R = ConstRef r_kn
let glob_R1 = ConstRef (make_path rdefinitions "R1")
let glob_R0 = ConstRef (make_path rdefinitions "R0")
let glob_Ropp = ConstRef (make_path rdefinitions "Ropp")
let glob_Rplus = ConstRef (make_path rdefinitions "Rplus")
let glob_Rmult = ConstRef (make_path rdefinitions "Rmult")

let two = mult_2 one
let three = add_1 two
let four = mult_2 two

(* Unary representation of strictly positive numbers *)
let rec small_r dloc n =
  if equal one n then GRef (dloc, glob_R1, None)
  else GApp(dloc,GRef (dloc,glob_Rplus, None),
            [GRef (dloc, glob_R1, None);small_r dloc (sub_1 n)])

let r_of_posint dloc n =
  let r1 = GRef (dloc, glob_R1, None) in
  let r2 = small_r dloc two in
  let rec r_of_pos n =
    if less_than n four then small_r dloc n
    else
      let (q,r) = div2_with_rest n in
      let b = GApp(dloc,GRef(dloc,glob_Rmult,None),[r2;r_of_pos q]) in
      if r then GApp(dloc,GRef(dloc,glob_Rplus,None),[r1;b]) else b in
  if not (Bigint.equal n zero) then r_of_pos n else GRef(dloc,glob_R0,None)

let r_of_int dloc z =
  if is_strictly_neg z then
    GApp (dloc, GRef(dloc,glob_Ropp,None), [r_of_posint dloc (neg z)])
  else
    r_of_posint dloc z

(**********************************************************************)
(* Printing R via scopes                                              *)
(**********************************************************************)

let bignat_of_r =
(* for numbers > 1 *)
let rec bignat_of_pos = function
  (* 1+1 *)
  | GApp (_,GRef (_,p,_), [GRef (_,o1,_); GRef (_,o2,_)])
      when Globnames.eq_gr p glob_Rplus && Globnames.eq_gr o1 glob_R1 && Globnames.eq_gr o2 glob_R1 -> two
  (* 1+(1+1) *)
  | GApp (_,GRef (_,p1,_), [GRef (_,o1,_);
      GApp(_,GRef (_,p2,_),[GRef(_,o2,_);GRef(_,o3,_)])])
      when Globnames.eq_gr p1 glob_Rplus && Globnames.eq_gr p2 glob_Rplus &&
           Globnames.eq_gr o1 glob_R1 && Globnames.eq_gr o2 glob_R1 && Globnames.eq_gr o3 glob_R1 -> three
  (* (1+1)*b *)
  | GApp (_,GRef (_,p,_), [a; b]) when Globnames.eq_gr p glob_Rmult ->
      if not (Bigint.equal (bignat_of_pos a) two) then raise Non_closed_number;
      mult_2 (bignat_of_pos b)
  (* 1+(1+1)*b *)
  | GApp (_,GRef (_,p1,_), [GRef (_,o,_); GApp (_,GRef (_,p2,_),[a;b])])
      when Globnames.eq_gr p1 glob_Rplus && Globnames.eq_gr p2 glob_Rmult && Globnames.eq_gr o glob_R1  ->
      if not (Bigint.equal (bignat_of_pos a) two) then raise Non_closed_number;
        add_1 (mult_2 (bignat_of_pos b))
  | _ -> raise Non_closed_number
in
let bignat_of_r = function
  | GRef (_,a,_) when Globnames.eq_gr a glob_R0 -> zero
  | GRef (_,a,_) when Globnames.eq_gr a glob_R1 -> one
  | r -> bignat_of_pos r
in
bignat_of_r

let bigint_of_r = function
  | GApp (_,GRef (_,o,_), [a]) when Globnames.eq_gr o glob_Ropp ->
      let n = bignat_of_r a in
      if Bigint.equal n zero then raise Non_closed_number;
      neg n
  | a -> bignat_of_r a

let uninterp_r p =
  try
    Some (bigint_of_r p)
  with Non_closed_number ->
    None

let mkGRef gr = GRef (Loc.ghost,gr,None)

let _ = Notation.declare_numeral_interpreter "R_scope"
  (r_path,["Coq";"Reals";"Rdefinitions"])
  r_of_int
  (List.map mkGRef 
    [glob_Ropp;glob_R0;glob_Rplus;glob_Rmult;glob_R1],
    uninterp_r,
    false)
