(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $ $ i*)

(* digit-based syntax for int31 and bigint *)

open Bigint
open Libnames
open Rawterm

(* arnaud : plan : 
  - path des modules int31 et bigint dans des variables
  - nom des constructeurs dans des variables
  - nom des scopes dans des variables
  - fonction qui cree les int31 en fonction d'un entier (ce sont des bigint de coq)
    <= div2 with rest 31 fois, dans un tableau d'args preconstruit
  - fonction qui cree un bigint de hauteur n (en appelant deux fois la fonction 
    a la hauteur n-1 (sauf dans les cas ou il y a du 0))
  /!\ attention aux nombres negatifs  *)

(*** Constants for locating the int31 and bigN ***)



let make_dir l = Names.make_dirpath (List.map Names.id_of_string (List.rev l))
let make_path dir id = Libnames.make_path (make_dir dir) (Names.id_of_string id)

(* copied on g_zsyntax.ml, where it is said to be a temporary hack*)
(* takes a path an identifier in the form of a string list and a string, 
   returns a kernel_name *)
let make_kn dir id = Libnames.encode_kn (make_dir dir) (Names.id_of_string id)


(* int31 stuff *)
let int31_module = ["Coq"; "Ints"; "Int31"]
let int31_path = make_path int31_module "int31"
let int31_id = make_kn int31_module


let int31_construct = ConstructRef ((int31_id "int31",0),1)

let int31_0 = ConstructRef ((int31_id "digits",0),1)
let int31_1 = ConstructRef ((int31_id "digits",0),2)


(* bigint stuff*)
let zn2z_module = ["Coq"; "Ints"; "Basic_type"]
let zn2z_path = make_path zn2z_module "zn2z"
let zn2z_id = make_kn zn2z_module

let zn2z_W0 = ConstructRef ((zn2z_id "zn2z",0),1)
let zn2z_WW = ConstructRef ((zn2z_id "zn2z",0),2)

let bigN_module = ["Coq"; "Ints"; "BigN"]
let bigN_path = make_path bigN_module "bigN"
(* big ugly hack *)
let bigN_id id = (Obj.magic ((Names.MPdot ((Names.MPfile (make_dir bigN_module)), 
                             Names.mk_label "BigN")),
              [], Names.id_of_string id) : Names.kernel_name)

(* number of inlined level of bigN (actually the level 0 to n_inlined-1 are inlined) *)
let n_inlined = of_string "13"
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
  ConstructRef ((bigN_id "t_",0),
		if less_than i n_inlined then
		  (to_int i)+1
		else
		  (to_int n_inlined)+1
	       )

(*** Definition of the Non_closed exception, used in the pretty printing ***)
exception Non_closed

(*** Parsing for int31 in digital notation ***)

(* parses a *non-negative* integer (from bigint.ml) into an int31
   wraps modulo 2^31 *)
let int31_of_pos_bigint dloc n = 
  let ref_construct = RRef (dloc, int31_construct) in
  let ref_0 = RRef (dloc, int31_0) in
  let ref_1 = RRef (dloc, int31_1) in
  let rec args counter n =
    if counter <= 0 then
      []
    else
      let (q,r) = div2_with_rest n in
	(if r then ref_1 else ref_0)::(args (counter-1) q)
  in
  RApp (dloc, ref_construct, List.rev (args 31 n))

let error_negative dloc =
  Util.user_err_loc (dloc, "interp_int31", Pp.str "int31 are only non-negative numbers")

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
      | (RRef (_,b))::l when b = int31_0 -> args_parsing l (mult_2 cur)
      | (RRef (_,b))::l when b = int31_1 -> args_parsing l (add_1 (mult_2 cur))
      | _ -> raise Non_closed
  in
  function 
  | RApp (_, RRef (_, c), args) when c=int31_construct -> args_parsing args zero
  | _ -> raise Non_closed

let uninterp_int31 i = 
  try 
    Some (bigint_of_int31 i)
  with Non_closed ->
    None

(* Actually declares the interpreter for int31 *)
let _ = Notation.declare_numeral_interpreter "int31_scope"
  (int31_path, int31_module)
  interp_int31
  ([RRef (Util.dummy_loc, int31_construct)],
   uninterp_int31,
   true)


(*** Parsing for BigN in digital notation ***)
(* the base for BigN (in Coq) that is 2^31 in our case *)
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
  let ref_W0 = RRef (dloc, zn2z_W0) in
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
  decomp hght n
      
let bigN_of_pos_bigint dloc n =
  let ref_constructor i = RRef (dloc, bigN_constructor i) in
  let result h word = RApp (dloc, ref_constructor h, if less_than h n_inlined then
				                       [word]
			                             else
				                      [RHole (dloc, Evd.InternalHole);
						       word])
  in
  let hght = height n in
  result hght (word_of_pos_bigint dloc hght n)
  
let bigN_error_negative dloc =
  Util.user_err_loc (dloc, "interp_bigN", Pp.str "bogN are only non-negative numbers")

let interp_bigN dloc n = 
  if is_pos_or_zero n then
    bigN_of_pos_bigint dloc n
  else
    bigN_error_negative dloc


(* Pretty prints a bigN *)

let bigint_of_word = 
  let rec get_height rc =
    match rc with
    | RApp (_,RRef(_,c), [_;lft;rght]) when c = zn2z_WW -> 
	                                  let hleft = get_height lft in
					  let hright = get_height rght in
					  if less_than hleft hright then
					    hright
					  else
					    hleft
    | _ -> zero
  in
  let rec transform hght rc =
    match rc with
    | RApp (_,RRef(_,c),_) when c = zn2z_W0-> zero
    | RApp (_,RRef(_,c), [_;lft;rght]) when c=zn2z_WW-> add (mult (rank hght)
                                                          (transform (sub_1 hght) lft))
	                                            (transform (sub_1 hght) rght)
    | _ -> bigint_of_int31 rc
  in
  fun rc ->
    let hght = get_height rc in
    transform hght rc
    
let bigint_of_bigN rc=
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
let _ = Notation.declare_numeral_interpreter "bigN_scope"
  (bigN_path, bigN_module)
  interp_bigN
  (bigN_list_of_constructors,
   uninterp_bigN,
   true)
