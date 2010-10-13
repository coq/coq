(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* digit-based syntax for int31, bigN bigZ and bigQ *)

open Bigint
open Libnames
open Rawterm

(*** Constants for locating int31 / bigN / bigZ / bigQ constructors ***)

let make_dir l = Names.make_dirpath (List.map Names.id_of_string (List.rev l))
let make_path dir id = Libnames.make_path (make_dir dir) (Names.id_of_string id)

let make_mind mp id = Names.make_mind mp Names.empty_dirpath (Names.mk_label id)
let make_mind_mpfile dir id = make_mind (Names.MPfile (make_dir dir)) id
let make_mind_mpdot dir modname id =
  let mp = Names.MPdot (Names.MPfile (make_dir dir), Names.mk_label modname)
  in make_mind mp id


(* int31 stuff *)
let int31_module = ["Coq"; "Numbers"; "Cyclic"; "Int31"; "Int31Native"]
let int31_path = make_path int31_module "int"
(*
let int31_notation_module = 
  ["Coq"; "Numbers"; "Cyclic"; "Int31"; "Int31Notation"]
let int31_notation_path = make_path int31_notation_module "int31"
*)
let int31_id = make_mind_mpfile int31_module
let int31_scope = "int31_scope"


(* bigN stuff*)
let zn2z_module = ["Coq"; "Numbers"; "Cyclic"; "DoubleCyclic"; "DoubleType"]
let zn2z_path = make_path zn2z_module "zn2z"
let zn2z_id = make_mind_mpfile zn2z_module

let zn2z_W0 = ConstructRef ((zn2z_id "zn2z",0),1)
let zn2z_WW = ConstructRef ((zn2z_id "zn2z",0),2)

let bigN_module = ["Coq"; "Numbers"; "Natural"; "BigN"; "BigN" ]
let bigN_path = make_path (bigN_module@["BigN"]) "t"
let bigN_t = make_mind_mpdot bigN_module "BigN" "t_"
let bigN_scope = "bigN_scope"

(* number of inlined level of bigN (actually the level 0 to n_inlined-1 are inlined) *)
let n_inlined = of_string "7"
let bigN_constructor =
 (* converts a bigint into an int the ugly way *)
  let rec to_int i =
    if equal i zero then
      0
    else
      let (quo,rem) = div2_with_rest i in
      if rem then
	2*(to_int quo)+1
      else
	2*(to_int quo)
  in
  fun i ->
  ConstructRef ((bigN_t,0),
		if less_than i n_inlined then
		  (to_int i)+1
		else
		  (to_int n_inlined)+1
	       )

(*bigZ stuff*)
let bigZ_module = ["Coq"; "Numbers"; "Integer"; "BigZ"; "BigZ" ]
let bigZ_path = make_path (bigZ_module@["BigZ"]) "t"
let bigZ_t = make_mind_mpdot bigZ_module "BigZ" "t_"
let bigZ_scope = "bigZ_scope"

let bigZ_pos = ConstructRef ((bigZ_t,0),1)
let bigZ_neg = ConstructRef ((bigZ_t,0),2)


(*bigQ stuff*)
let bigQ_module = ["Coq"; "Numbers"; "Rational"; "BigQ"; "BigQ"]
let bigQ_path = make_path (bigQ_module@["BigQ"]) "t"
let bigQ_t = make_mind_mpdot bigQ_module "BigQ" "t_"
let bigQ_scope = "bigQ_scope"

let bigQ_z =  ConstructRef ((bigQ_t,0),1)


(*** Definition of the Non_closed exception, used in the pretty printing ***)
exception Non_closed

(*** Parsing for int31 in digital notation ***)

(* parses a *non-negative* integer (from bigint.ml) into an int31
   wraps modulo 2^31 *)

let interp_int31 dloc n =
  let sn = to_string n in
  try RNativeInt (dloc, Native.Uint31.of_string sn)
  with Failure "int_of_string" ->
    let msg = 
      if is_pos_or_zero n then "int31: object to large."
      else "int31 are only non-negative numbers." in
    Util.user_err_loc (dloc, "interp_int31", Pp.str msg)


(* Pretty prints an int31 *)


let uninterp_int31 i =
  match i with
  | RNativeInt(_,i) -> Some (of_string (Native.Uint31.to_string i))
  | _ -> None


(* Actually declares the interpreter for int31 *)
let _ = Notation.declare_numeral_interpreter int31_scope
  (int31_path, int31_module)
  interp_int31
  ([], uninterp_int31, true)


(*** Parsing for bigN in digital notation ***)
(* the base for bigN (in Coq) that is 2^31 in our case *)
let base = pow two (of_string "31")

(* base of the bigN of height N : *)
let rank n = pow base (pow two n)

(* splits a number bi at height n, that is the rest needs 2^n int31 to be stored
   it is expected to be used only when the quotient would also need 2^n int31 to be
   stored *)
let split_at n bi =
  euclid bi (rank (sub_1 n))

(* search the height of the Coq bigint needed to represent the integer bi *)
let height bi =
  let rec height_aux n =
    if less_than bi (rank n) then
      n
    else
      height_aux (add_1 n)
  in
  height_aux zero


(* n must be a non-negative integer (from bigint.ml) *)
let word_of_pos_bigint dloc hght n =
  assert false
(*  let ref_W0 = RRef (dloc, zn2z_W0) in
  let ref_WW = RRef (dloc, zn2z_WW) in
  let rec decomp hgt n =
    if is_neg_or_zero hgt then
      int31_of_pos_bigint dloc n
    else if equal n zero then
      RApp (dloc, ref_W0, [RHole (dloc, Evd.InternalHole)])
    else
      let (h,l) = split_at hgt n in
      RApp (dloc, ref_WW, [RHole (dloc, Evd.InternalHole);
			   decomp (sub_1 hgt) h;
			   decomp (sub_1 hgt) l])
  in
  decomp hght n *)

let bigN_of_pos_bigint dloc n =
  let ref_constructor i = RRef (dloc, bigN_constructor i) in
  let result h word = RApp (dloc, ref_constructor h, if less_than h n_inlined then
				                       [word]
			                             else
				                      [Nat_syntax.nat_of_int dloc (sub h n_inlined);
						       word])
  in
  let hght = height n in
  result hght (word_of_pos_bigint dloc hght n)

let bigN_error_negative dloc =
  Util.user_err_loc (dloc, "interp_bigN", Pp.str "bigN are only non-negative numbers.")

let interp_bigN dloc n =
  if is_pos_or_zero n then
    bigN_of_pos_bigint dloc n
  else
    bigN_error_negative dloc


(* Pretty prints a bigN *)

let bigint_of_word =
(*
  let rec get_height rc =
    match rc with
    | RApp (_,RRef(_,c), [_;lft;rght]) when c = zn2z_WW ->
	                                  let hleft = get_height lft in
					  let hright = get_height rght in
					  add_1
					    (if less_than hleft hright then
						 hright
					     else
						 hleft)
    | _ -> zero
  in
  let rec transform hght rc =
    match rc with
    | RApp (_,RRef(_,c),_) when c = zn2z_W0-> zero
    | RApp (_,RRef(_,c), [_;lft;rght]) when c=zn2z_WW-> let new_hght = sub_1 hght in
	                                                add (mult (rank new_hght)
                                                          (transform (new_hght) lft))
	                                            (transform (new_hght) rght)
    | _ -> bigint_of_int31 rc
  in
*)
  fun rc -> assert false (*
    let hght = get_height rc in
    transform hght rc
*)
let bigint_of_bigN rc =
  match rc with
  | RApp (_,_,[one_arg]) -> bigint_of_word one_arg
  | RApp (_,_,[_;second_arg]) -> bigint_of_word second_arg
  | _ -> raise Non_closed

let uninterp_bigN rc =
  try
    Some (bigint_of_bigN rc)
  with Non_closed ->
    None


(* declare the list of constructors of bigN used in the declaration of the
   numeral interpreter *)

let bigN_list_of_constructors =
  let rec build i =
    if less_than i (add_1 n_inlined) then
      RRef (Util.dummy_loc, bigN_constructor i)::(build (add_1 i))
    else
      []
  in
  build zero

(* Actually declares the interpreter for bigN *)
let _ = Notation.declare_numeral_interpreter bigN_scope
  (bigN_path, bigN_module)
  interp_bigN
  (bigN_list_of_constructors,
   uninterp_bigN,
   true)


(*** Parsing for bigZ in digital notation ***)
let interp_bigZ dloc n =
  let ref_pos = RRef (dloc, bigZ_pos) in
  let ref_neg = RRef (dloc, bigZ_neg) in
  if is_pos_or_zero n then
    RApp (dloc, ref_pos, [bigN_of_pos_bigint dloc n])
  else
    RApp (dloc, ref_neg, [bigN_of_pos_bigint dloc (neg n)])

(* pretty printing functions for bigZ *)
let bigint_of_bigZ = function
  | RApp (_, RRef(_,c), [one_arg]) when c = bigZ_pos -> bigint_of_bigN one_arg
  | RApp (_, RRef(_,c), [one_arg]) when c = bigZ_neg ->
      let opp_val = bigint_of_bigN one_arg in
      if equal opp_val zero then
	raise Non_closed
      else
	neg opp_val
  | _ -> raise Non_closed


let uninterp_bigZ rc =
  try
    Some (bigint_of_bigZ rc)
  with Non_closed ->
    None

(* Actually declares the interpreter for bigZ *)
let _ = Notation.declare_numeral_interpreter bigZ_scope
  (bigZ_path, bigZ_module)
  interp_bigZ
  ([RRef (Util.dummy_loc, bigZ_pos);
    RRef (Util.dummy_loc, bigZ_neg)],
   uninterp_bigZ,
   true)

(*** Parsing for bigQ in digital notation ***)
let interp_bigQ dloc n =
  let ref_z = RRef (dloc, bigQ_z) in
  RApp (dloc, ref_z, [interp_bigZ dloc n])

let uninterp_bigQ rc =
  try match rc with
    | RApp (_, RRef(_,c), [one_arg]) when c = bigQ_z ->
	Some (bigint_of_bigZ one_arg)
    | _ -> None (* we don't pretty-print yet fractions *)
  with Non_closed -> None

(* Actually declares the interpreter for bigQ *)
let _ = Notation.declare_numeral_interpreter bigQ_scope
  (bigQ_path, bigQ_module)
  interp_bigQ
  ([RRef (Util.dummy_loc, bigQ_z)], uninterp_bigQ,
   true)
