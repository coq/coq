(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* digit-based syntax for int31, bigN bigZ and bigQ *)

open Bigint
open Names
open Globnames
open Glob_term

(*** Constants for locating int31 / bigN / bigZ / bigQ constructors ***)

let make_dir l = DirPath.make (List.rev_map Id.of_string l)
let make_path dir id = Libnames.make_path (make_dir dir) (Id.of_string id)

let make_mind mp id = Names.MutInd.make2 mp (Label.make id)
let make_mind_mpfile dir id = make_mind (MPfile (make_dir dir)) id
let make_mind_mpdot dir modname id =
  let mp = MPdot (MPfile (make_dir dir), Label.make modname)
  in make_mind mp id


(* int31 stuff *)
let int31_module = ["Coq"; "Numbers"; "Cyclic"; "Int31"; "Int31"]
let int31_path = make_path int31_module "int31"
let int31_id = make_mind_mpfile int31_module
let int31_scope = "int31_scope"

let int31_construct = ConstructRef ((int31_id "int31",0),1)

let int31_0 = ConstructRef ((int31_id "digits",0),1)
let int31_1 = ConstructRef ((int31_id "digits",0),2)


(* bigN stuff*)
let zn2z_module = ["Coq"; "Numbers"; "Cyclic"; "DoubleCyclic"; "DoubleType"]
let zn2z_path = make_path zn2z_module "zn2z"
let zn2z_id = make_mind_mpfile zn2z_module

let zn2z_W0 = ConstructRef ((zn2z_id "zn2z",0),1)
let zn2z_WW = ConstructRef ((zn2z_id "zn2z",0),2)

let bigN_module = ["Coq"; "Numbers"; "Natural"; "BigN"; "BigN" ]
let bigN_path = make_path (bigN_module@["BigN"]) "t"
let bigN_t = make_mind_mpdot bigN_module "BigN" "t'"
let bigN_scope = "bigN_scope"

(* number of inlined level of bigN (actually the level 0 to n_inlined-1 are inlined) *)
let n_inlined = 7

let bigN_constructor i =
  ConstructRef ((bigN_t,0),(min i n_inlined)+1)

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
let int31_of_pos_bigint dloc n =
  let ref_construct = GRef (dloc, int31_construct, None) in
  let ref_0 = GRef (dloc, int31_0, None) in
  let ref_1 = GRef (dloc, int31_1, None) in
  let rec args counter n =
    if counter <= 0 then
      []
    else
      let (q,r) = div2_with_rest n in
	(if r then ref_1 else ref_0)::(args (counter-1) q)
  in
  GApp (dloc, ref_construct, List.rev (args 31 n))

let error_negative dloc =
  Errors.user_err_loc (dloc, "interp_int31", Pp.str "int31 are only non-negative numbers.")

let interp_int31 dloc n =
  if is_pos_or_zero n then
    int31_of_pos_bigint dloc n
  else
    error_negative dloc

(* Pretty prints an int31 *)

let bigint_of_int31 =
  let rec args_parsing args cur =
    match args with
      | [] -> cur
      | (GRef (_,b,_))::l when eq_gr b int31_0 -> args_parsing l (mult_2 cur)
      | (GRef (_,b,_))::l when eq_gr b int31_1 -> args_parsing l (add_1 (mult_2 cur))
      | _ -> raise Non_closed
  in
  function
  | GApp (_, GRef (_, c, _), args) when eq_gr c int31_construct -> args_parsing args zero
  | _ -> raise Non_closed

let uninterp_int31 i =
  try
    Some (bigint_of_int31 i)
  with Non_closed ->
    None

(* Actually declares the interpreter for int31 *)
let _ = Notation.declare_numeral_interpreter int31_scope
  (int31_path, int31_module)
  interp_int31
  ([GRef (Loc.ghost, int31_construct, None)],
   uninterp_int31,
   true)


(*** Parsing for bigN in digital notation ***)
(* the base for bigN (in Coq) that is 2^31 in our case *)
let base = pow two 31

(* base of the bigN of height N : (2^31)^(2^n) *)
let rank n =
  let rec rk n pow2 =
    if n <= 0 then pow2
    else rk (n-1) (mult pow2 pow2)
  in rk n base

(* splits a number bi at height n, that is the rest needs 2^n int31 to be stored
   it is expected to be used only when the quotient would also need 2^n int31 to be
   stored *)
let split_at n bi =
  euclid bi (rank (n-1))

(* search the height of the Coq bigint needed to represent the integer bi *)
let height bi =
  let rec hght n pow2 =
    if less_than bi pow2 then n
    else hght (n+1) (mult pow2 pow2)
  in hght 0 base

(* n must be a non-negative integer (from bigint.ml) *)
let word_of_pos_bigint dloc hght n =
  let ref_W0 = GRef (dloc, zn2z_W0, None) in
  let ref_WW = GRef (dloc, zn2z_WW, None) in
  let rec decomp hgt n =
    if hgt <= 0 then
      int31_of_pos_bigint dloc n
    else if equal n zero then
      GApp (dloc, ref_W0, [GHole (dloc, Evar_kinds.InternalHole, Misctypes.IntroAnonymous, None)])
    else
      let (h,l) = split_at hgt n in
      GApp (dloc, ref_WW, [GHole (dloc, Evar_kinds.InternalHole, Misctypes.IntroAnonymous, None);
			   decomp (hgt-1) h;
			   decomp (hgt-1) l])
  in
  decomp hght n

let bigN_of_pos_bigint dloc n =
  let h = height n in
  let ref_constructor = GRef (dloc, bigN_constructor h, None) in
  let word = word_of_pos_bigint dloc h n in
  let args =
    if h < n_inlined then [word]
    else [Nat_syntax.nat_of_int dloc (of_int (h-n_inlined));word]
  in
  GApp (dloc, ref_constructor, args)

let bigN_error_negative dloc =
  Errors.user_err_loc (dloc, "interp_bigN", Pp.str "bigN are only non-negative numbers.")

let interp_bigN dloc n =
  if is_pos_or_zero n then
    bigN_of_pos_bigint dloc n
  else
    bigN_error_negative dloc


(* Pretty prints a bigN *)

let bigint_of_word =
  let rec get_height rc =
    match rc with
    | GApp (_,GRef(_,c,_), [_;lft;rght]) when eq_gr c zn2z_WW ->
      1+max (get_height lft) (get_height rght)
    | _ -> 0
  in
  let rec transform hght rc =
    match rc with
    | GApp (_,GRef(_,c,_),_) when eq_gr c zn2z_W0-> zero
    | GApp (_,GRef(_,c,_), [_;lft;rght]) when eq_gr c zn2z_WW->
      let new_hght = hght-1 in
      add (mult (rank new_hght)
             (transform new_hght lft))
	(transform new_hght rght)
    | _ -> bigint_of_int31 rc
  in
  fun rc ->
    let hght = get_height rc in
    transform hght rc

let bigint_of_bigN rc =
  match rc with
  | GApp (_,_,[one_arg]) -> bigint_of_word one_arg
  | GApp (_,_,[_;second_arg]) -> bigint_of_word second_arg
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
    if i < n_inlined+1 then
      GRef (Loc.ghost, bigN_constructor i,None)::(build (i+1))
    else
      []
  in
  build 0

(* Actually declares the interpreter for bigN *)
let _ = Notation.declare_numeral_interpreter bigN_scope
  (bigN_path, bigN_module)
  interp_bigN
  (bigN_list_of_constructors,
   uninterp_bigN,
   true)


(*** Parsing for bigZ in digital notation ***)
let interp_bigZ dloc n =
  let ref_pos = GRef (dloc, bigZ_pos, None) in
  let ref_neg = GRef (dloc, bigZ_neg, None) in
  if is_pos_or_zero n then
    GApp (dloc, ref_pos, [bigN_of_pos_bigint dloc n])
  else
    GApp (dloc, ref_neg, [bigN_of_pos_bigint dloc (neg n)])

(* pretty printing functions for bigZ *)
let bigint_of_bigZ = function
  | GApp (_, GRef(_,c,_), [one_arg]) when eq_gr c bigZ_pos -> bigint_of_bigN one_arg
  | GApp (_, GRef(_,c,_), [one_arg]) when eq_gr c bigZ_neg ->
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
  ([GRef (Loc.ghost, bigZ_pos, None);
    GRef (Loc.ghost, bigZ_neg, None)],
   uninterp_bigZ,
   true)

(*** Parsing for bigQ in digital notation ***)
let interp_bigQ dloc n =
  let ref_z = GRef (dloc, bigQ_z, None) in
  GApp (dloc, ref_z, [interp_bigZ dloc n])

let uninterp_bigQ rc =
  try match rc with
    | GApp (_, GRef(_,c,_), [one_arg]) when eq_gr c bigQ_z ->
	Some (bigint_of_bigZ one_arg)
    | _ -> None (* we don't pretty-print yet fractions *)
  with Non_closed -> None

(* Actually declares the interpreter for bigQ *)
let _ = Notation.declare_numeral_interpreter bigQ_scope
  (bigQ_path, bigQ_module)
  interp_bigQ
  ([GRef (Loc.ghost, bigQ_z, None)], uninterp_bigQ,
   true)
