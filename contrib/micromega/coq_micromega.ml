(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*                                                                      *)
(* Micromega: A reflexive tactic using the Positivstellensatz           *)
(*                                                                      *)
(*  Frédéric Besson (Irisa/Inria) 2006-2008                             *)
(*                                                                      *)
(************************************************************************)

open Mutils
let debug = false

let time str f x = 
 let t0 = (Unix.times()).Unix.tms_utime in
 let res = f x in 
 let t1 = (Unix.times()).Unix.tms_utime in 
  (*if debug then*) (Printf.printf "time %s %f\n" str (t1 -. t0) ; 
		     flush stdout); 
  res

type ('a,'b) formula =
  | TT 
  | FF 
  | X of 'b 
  | A of 'a * Names.name
  | C of ('a,'b) formula * ('a,'b) formula * Names.name
  | D of ('a,'b) formula * ('a,'b) formula * Names.name
  | N of ('a,'b) formula * Names.name
  | I of ('a,'b) formula * ('a,'b) formula * Names.name

let none = Names.Anonymous

let tag_formula t f = 
 match f with
  | A(x,_) -> A(x,t)
  | C(x,y,_) -> C(x,y,t)
  | D(x,y,_) -> D(x,y,t)
  | N(x,_) -> N(x,t)
  | I(x,y,_) -> I(x,y,t)
  |   _      -> f

let tt = []
let ff = [ [] ]


type ('constant,'contr) sentence =  
  ('constant Micromega.formula, 'contr) formula

let cnf negate normalise f = 
 let negate a = 
  CoqToCaml.list (fun cl -> CoqToCaml.list (fun x -> x) cl) (negate a) in

 let normalise a = 
  CoqToCaml.list (fun cl -> CoqToCaml.list (fun x -> x) cl) (normalise a) in

 let and_cnf x y = x @ y in
 let or_clause_cnf t f =  List.map (fun x -> t@x ) f in
  
 let rec or_cnf f f'  =
  match f with
   | [] -> tt
   | e :: rst -> (or_cnf rst f') @ (or_clause_cnf e f') in
  
 let rec xcnf  (pol : bool) f    =
  match f with
   | TT -> if pol then tt else ff (* ?? *)
   | FF  -> if pol then ff else tt (* ?? *)
   | X p -> if pol then ff else ff (* ?? *)
   | A(x,t) -> if pol then normalise  x else negate x
   | N(e,t)  -> xcnf  (not pol) e
   | C(e1,e2,t) -> 
      (if pol then and_cnf else or_cnf) (xcnf  pol e1) (xcnf  pol e2)
   | D(e1,e2,t)  -> 
      (if pol then or_cnf else and_cnf) (xcnf  pol e1) (xcnf  pol e2)
   | I(e1,e2,t) -> 
      (if pol then or_cnf else and_cnf) (xcnf  (not pol) e1) (xcnf  pol e2) in

  xcnf  true f



module M =
struct
 open Coqlib
 open Term
  (*    let constant = gen_constant_in_modules "Omicron" coq_modules*)
  
  
 let logic_dir = ["Coq";"Logic";"Decidable"]
 let coq_modules =
  init_modules @ 
   [logic_dir] @ arith_modules @ zarith_base_modules @ 
   [ ["Coq";"Lists";"List"];
     ["ZMicromega"];
     ["Tauto"];
     ["RingMicromega"];
     ["EnvRing"];
     ["Coq"; "micromega"; "ZMicromega"];
     ["Coq" ; "micromega" ; "Tauto"];
     ["Coq" ; "micromega" ; "RingMicromega"];
     ["Coq" ; "micromega" ; "EnvRing"];
     ["Coq";"QArith"; "QArith_base"];
     ["Coq";"Reals" ; "Rdefinitions"];
     ["LRing_normalise"]]
   
 let constant = gen_constant_in_modules "ZMicromega" coq_modules

 let coq_and = lazy (constant "and")
 let coq_or = lazy (constant "or")
 let coq_not = lazy (constant "not")
 let coq_iff = lazy (constant "iff")
 let coq_True = lazy (constant "True")
 let coq_False = lazy (constant "False")
  
 let coq_cons = lazy (constant "cons")
 let coq_nil = lazy (constant "nil")
 let coq_list = lazy (constant "list")

 let coq_O = lazy (constant "O")
 let coq_S = lazy (constant "S")
 let coq_nat = lazy (constant "nat")

 let coq_NO = lazy 
  (gen_constant_in_modules "N" [ ["Coq";"NArith";"BinNat" ]]  "N0")
 let coq_Npos = lazy 
  (gen_constant_in_modules "N" [ ["Coq";"NArith"; "BinNat"]]  "Npos")
  (* let coq_n = lazy (constant "N")*)

 let coq_pair = lazy (constant "pair")
 let coq_None = lazy (constant "None")
 let coq_option = lazy (constant "option")
 let coq_positive = lazy (constant "positive")
 let coq_xH = lazy (constant "xH")
 let coq_xO = lazy (constant "xO")
 let coq_xI = lazy (constant "xI")
  
 let coq_N0 = lazy (constant "N0")
 let coq_N0 = lazy (constant "Npos")


 let coq_Z = lazy (constant "Z")
 let coq_Q = lazy (constant "Q")
 let coq_R = lazy (constant "R")

 let coq_ZERO = lazy (constant  "Z0")
 let coq_POS = lazy (constant  "Zpos")
 let coq_NEG = lazy (constant  "Zneg")

 let coq_QWitness = lazy 
  (gen_constant_in_modules "QMicromega" 
    [["Coq"; "micromega"; "QMicromega"]] "QWitness")
 let coq_ZWitness = lazy 
  (gen_constant_in_modules "QMicromega" 
    [["Coq"; "micromega"; "ZMicromega"]] "ZWitness")


 let coq_Build_Witness = lazy (constant "Build_Witness")


 let coq_Qmake = lazy (constant "Qmake")

 let coq_proofTerm = lazy (constant "ProofTerm")
 let coq_ratProof = lazy (constant "RatProof")
 let coq_cutProof = lazy (constant "CutProof")
 let coq_enumProof = lazy (constant "EnumProof")

 let coq_Zgt = lazy (constant "Zgt")
 let coq_Zge = lazy (constant "Zge")
 let coq_Zle = lazy (constant "Zle")
 let coq_Zlt = lazy (constant "Zlt")
 let coq_Eq  = lazy (constant "eq")

 let coq_Zplus = lazy (constant "Zplus")
 let coq_Zminus = lazy (constant "Zminus")
 let coq_Zopp = lazy (constant "Zopp")
 let coq_Zmult = lazy (constant "Zmult")
 let coq_N_of_Z = lazy 
  (gen_constant_in_modules "ZArithRing" 
    [["Coq";"setoid_ring";"ZArithRing"]] "N_of_Z")


 let coq_PEX = lazy (constant "PEX" )
 let coq_PEc = lazy (constant"PEc")
 let coq_PEadd = lazy (constant "PEadd")
 let coq_PEopp = lazy (constant "PEopp")
 let coq_PEmul = lazy (constant "PEmul")
 let coq_PEsub = lazy (constant "PEsub")
 let coq_PEpow = lazy (constant "PEpow")


 let coq_OpEq = lazy (constant "OpEq")
 let coq_OpNEq = lazy (constant "OpNEq")
 let coq_OpLe = lazy (constant "OpLe")
 let coq_OpLt = lazy (constant  "OpLt")
 let coq_OpGe = lazy (constant "OpGe")
 let coq_OpGt = lazy (constant  "OpGt")


 let coq_S_In = lazy (constant "S_In")
 let coq_S_Square = lazy (constant "S_Square")
 let coq_S_Monoid = lazy (constant "S_Monoid")
 let coq_S_Ideal = lazy (constant "S_Ideal")
 let coq_S_Mult = lazy (constant "S_Mult")
 let coq_S_Add  = lazy (constant "S_Add")
 let coq_S_Pos  = lazy (constant "S_Pos")
 let coq_S_Z    = lazy (constant "S_Z")
 let coq_coneMember    = lazy (constant "coneMember")
  

 let coq_make_impl = lazy 
  (gen_constant_in_modules "Zmicromega" [["Refl"]] "make_impl")
 let coq_make_conj = lazy 
  (gen_constant_in_modules "Zmicromega" [["Refl"]] "make_conj")

 let coq_Build = lazy 
  (gen_constant_in_modules "RingMicromega" 
    [["Coq" ; "micromega" ; "RingMicromega"] ; ["RingMicromega"] ] 
    "Build_Formula")
 let coq_Cstr = lazy 
  (gen_constant_in_modules "RingMicromega" 
    [["Coq" ; "micromega" ; "RingMicromega"] ; ["RingMicromega"] ] "Formula")

 type parse_error  = 
   | Ukn 
   | BadStr of string 
   | BadNum of int 
   | BadTerm of Term.constr 
   | Msg   of string
   | Goal of (Term.constr list ) * Term.constr * parse_error

 let string_of_error = function
  | Ukn -> "ukn"
  | BadStr s -> s
  | BadNum i -> string_of_int i
  | BadTerm _ -> "BadTerm"
  | Msg  s    -> s
  | Goal _    -> "Goal"


 exception ParseError 




 let get_left_construct term = 
  match Term.kind_of_term term with
   | Term.Construct(_,i) -> (i,[| |])
   | Term.App(l,rst) -> 
      (match Term.kind_of_term l with
       | Term.Construct(_,i) -> (i,rst)
       |   _     -> raise ParseError
      )
   | _ ->   raise ParseError
      
 module Mc = Micromega
      
 let rec parse_nat term = 
  let (i,c) = get_left_construct term in
   match i with
    | 1 -> Mc.O
    | 2 -> Mc.S (parse_nat (c.(0)))
    | i -> raise ParseError
       

 let pp_nat o n = Printf.fprintf o "%i" (CoqToCaml.nat n)


 let rec dump_nat x = 
  match x with
   | Mc.O -> Lazy.force coq_O
   | Mc.S p -> Term.mkApp(Lazy.force coq_S,[| dump_nat p |])


 let rec parse_positive term = 
  let (i,c) = get_left_construct term in
   match i with
    | 1 -> Mc.XI (parse_positive c.(0))
    | 2 -> Mc.XO (parse_positive c.(0))
    | 3 -> Mc.XH
    | i -> raise ParseError
       

 let rec dump_positive x = 
  match x with
   | Mc.XH -> Lazy.force coq_xH
   | Mc.XO p -> Term.mkApp(Lazy.force coq_xO,[| dump_positive p |])
   | Mc.XI p -> Term.mkApp(Lazy.force coq_xI,[| dump_positive p |])

 let pp_positive o x = Printf.fprintf o "%i" (CoqToCaml.positive x)	  


 let rec dump_n x = 
  match x with 
   | Mc.N0 -> Lazy.force coq_N0
   | Mc.Npos p -> Term.mkApp(Lazy.force coq_Npos,[| dump_positive p|])

 let rec dump_index x = 
  match x with
   | Mc.XH -> Lazy.force coq_xH
   | Mc.XO p -> Term.mkApp(Lazy.force coq_xO,[| dump_index p |])
   | Mc.XI p -> Term.mkApp(Lazy.force coq_xI,[| dump_index p |])


 let pp_index o x = Printf.fprintf o "%i" (CoqToCaml.index x)	  

 let rec dump_n x = 
  match x with
   | Mc.N0 -> Lazy.force coq_NO
   | Mc.Npos p -> Term.mkApp(Lazy.force coq_Npos,[| dump_positive p |])

 let rec pp_n o x =  output_string o  (string_of_int (CoqToCaml.n x))

 let dump_pair t1 t2 dump_t1 dump_t2 (Mc.Pair (x,y)) =
  Term.mkApp(Lazy.force coq_pair,[| t1 ; t2 ; dump_t1 x ; dump_t2 y|])


 let rec parse_z term =
  let (i,c) = get_left_construct term in
   match i with
    | 1 -> Mc.Z0
    | 2 -> Mc.Zpos (parse_positive c.(0))
    | 3 -> Mc.Zneg (parse_positive c.(0))
    | i -> raise ParseError

 let dump_z x =
  match x with
   | Mc.Z0 ->Lazy.force coq_ZERO
   | Mc.Zpos p -> Term.mkApp(Lazy.force coq_POS,[| dump_positive p|]) 
   | Mc.Zneg p -> Term.mkApp(Lazy.force coq_NEG,[| dump_positive p|])  

 let pp_z o x = Printf.fprintf o "%i" (CoqToCaml.z x)

let dump_num bd1 = 
 Term.mkApp(Lazy.force coq_Qmake,
	   [|dump_z (CamlToCoq.bigint (numerator bd1)) ; 
	     dump_positive (CamlToCoq.positive_big_int (denominator bd1)) |])


let dump_q q = 
 Term.mkApp(Lazy.force coq_Qmake, 
	   [| dump_z q.Micromega.qnum ; dump_positive q.Micromega.qden|])

let parse_q term =  
 match Term.kind_of_term term with
  | Term.App(c, args) -> 
     (
      match Term.kind_of_term c with
	Term.Construct((n,j),i) -> 
      if Names.string_of_kn n  = "Coq.QArith.QArith_base#<>#Q"
      then {Mc.qnum = parse_z args.(0) ; Mc.qden = parse_positive args.(1) }
      else raise ParseError
       |  _ -> raise ParseError
     )
  |   _ -> raise ParseError
  
 let rec parse_list parse_elt term = 
  let (i,c) = get_left_construct term in
   match i with
    | 1 -> Mc.Nil
    | 2 -> Mc.Cons(parse_elt c.(1), parse_list parse_elt c.(2))
    | i -> raise ParseError


 let rec dump_list typ dump_elt l =
  match l with
   | Mc.Nil -> Term.mkApp(Lazy.force coq_nil,[| typ |])
   | Mc.Cons(e,l) -> Term.mkApp(Lazy.force coq_cons, 
			       [| typ; dump_elt e;dump_list typ dump_elt l|])
      
 let rec dump_ml_list typ dump_elt l =
  match l with
   | [] -> Term.mkApp(Lazy.force coq_nil,[| typ |])
   | e::l -> Term.mkApp(Lazy.force coq_cons, 
		       [| typ; dump_elt e;dump_ml_list typ dump_elt l|])



 let pp_list op cl elt o l = 
  let rec _pp  o l = 
   match l with
    | Mc.Nil -> ()
    | Mc.Cons(e,Mc.Nil) -> Printf.fprintf o "%a" elt e
    | Mc.Cons(e,l) -> Printf.fprintf o "%a ,%a" elt e  _pp l in
   Printf.fprintf o "%s%a%s" op _pp l cl 



 let pp_var  = pp_positive
 let dump_var = dump_positive

 let rec pp_expr o e = 
  match e with
   | Mc.PEX n -> Printf.fprintf o "V %a" pp_var n
   | Mc.PEc z -> pp_z o z
   | Mc.PEadd(e1,e2) -> Printf.fprintf o "(%a)+(%a)" pp_expr e1 pp_expr e2
   | Mc.PEmul(e1,e2) -> Printf.fprintf o "%a*(%a)" pp_expr e1 pp_expr e2
   | Mc.PEopp e -> Printf.fprintf o "-(%a)" pp_expr e
   | Mc.PEsub(e1,e2) -> Printf.fprintf o "(%a)-(%a)" pp_expr e1 pp_expr e2
   | Mc.PEpow(e,n) -> Printf.fprintf o "(%a)^(%a)" pp_expr e pp_n  n


 let  dump_expr typ dump_z e =
  let rec dump_expr  e =
  match e with
   | Mc.PEX n -> mkApp(Lazy.force coq_PEX,[| typ; dump_var n |])
   | Mc.PEc z -> mkApp(Lazy.force coq_PEc,[| typ ; dump_z z |])
   | Mc.PEadd(e1,e2) -> mkApp(Lazy.force coq_PEadd,
			     [| typ; dump_expr e1;dump_expr e2|])
   | Mc.PEsub(e1,e2) -> mkApp(Lazy.force coq_PEsub,
			     [| typ; dump_expr  e1;dump_expr  e2|])
   | Mc.PEopp e -> mkApp(Lazy.force coq_PEopp,
			[| typ; dump_expr  e|])
   | Mc.PEmul(e1,e2) ->  mkApp(Lazy.force coq_PEmul,
			      [| typ; dump_expr  e1;dump_expr e2|])
   | Mc.PEpow(e,n) ->  mkApp(Lazy.force coq_PEpow,
			    [| typ; dump_expr  e; dump_n  n|])
     in
   dump_expr e

 let rec dump_monoid l = dump_list (Lazy.force coq_nat) dump_nat l

 let rec dump_cone typ dump_z e = 
  let z = Lazy.force typ in 
 let rec dump_cone e =
  match e with
   | Mc.S_In n -> mkApp(Lazy.force coq_S_In,[| z; dump_nat n |])
   | Mc.S_Ideal(e,c) -> mkApp(Lazy.force coq_S_Ideal, 
			     [| z; dump_expr z dump_z e ; dump_cone c |])
   | Mc.S_Square e -> mkApp(Lazy.force coq_S_Square, 
			   [| z;dump_expr z dump_z e|])
   | Mc.S_Monoid l -> mkApp (Lazy.force coq_S_Monoid, 
			    [|z; dump_monoid l|])
   | Mc.S_Add(e1,e2) -> mkApp(Lazy.force coq_S_Add,
			     [| z; dump_cone e1; dump_cone e2|])
   | Mc.S_Mult(e1,e2) -> mkApp(Lazy.force coq_S_Mult,
			      [| z; dump_cone e1; dump_cone e2|])
   | Mc.S_Pos p -> mkApp(Lazy.force coq_S_Pos,[| z; dump_z p|])
   | Mc.S_Z    -> mkApp( Lazy.force coq_S_Z,[| z|]) in 
  dump_cone e


 let  pp_cone pp_z o e = 
  let rec pp_cone o e = 
   match e with 
    | Mc.S_In n -> 
       Printf.fprintf o "(S_In %a)%%nat" pp_nat n
    | Mc.S_Ideal(e,c) -> 
       Printf.fprintf o "(S_Ideal %a %a)" pp_expr e pp_cone c
    | Mc.S_Square e -> 
       Printf.fprintf o "(S_Square %a)" pp_expr e
    | Mc.S_Monoid l -> 
       Printf.fprintf o "(S_Monoid %a)" (pp_list "[" "]" pp_nat) l
    | Mc.S_Add(e1,e2) -> 
       Printf.fprintf o "(S_Add %a %a)" pp_cone e1 pp_cone e2
    | Mc.S_Mult(e1,e2) -> 
       Printf.fprintf o "(S_Mult %a %a)" pp_cone e1 pp_cone e2
    | Mc.S_Pos p -> 
       Printf.fprintf o "(S_Pos %a)%%positive" pp_z p
    | Mc.S_Z    -> 
       Printf.fprintf o "S_Z" in
   pp_cone o e




 let rec parse_op term = 
  let (i,c) = get_left_construct term in
   match i with
    | 1 -> Mc.OpEq
    | 2 -> Mc.OpLe
    | 3 -> Mc.OpGe
    | 4 -> Mc.OpGt
    | 5 -> Mc.OpLt
    | i -> raise ParseError


 let rec dump_op = function
  | Mc.OpEq-> Lazy.force coq_OpEq
  | Mc.OpNEq-> Lazy.force coq_OpNEq
  | Mc.OpLe -> Lazy.force coq_OpLe
  | Mc.OpGe -> Lazy.force coq_OpGe
  | Mc.OpGt-> Lazy.force coq_OpGt
  | Mc.OpLt-> Lazy.force coq_OpLt



 let pp_op o e= 
  match e with 
   | Mc.OpEq-> Printf.fprintf o "="
   | Mc.OpNEq-> Printf.fprintf o "<>"
   | Mc.OpLe -> Printf.fprintf o "=<"
   | Mc.OpGe -> Printf.fprintf o ">="
   | Mc.OpGt-> Printf.fprintf o ">"
   | Mc.OpLt-> Printf.fprintf o "<"




 let pp_cstr o {Mc.flhs = l ; Mc.fop = op ; Mc.frhs = r } =
  Printf.fprintf o"(%a %a %a)" pp_expr l pp_op op pp_expr r

 let dump_cstr typ dump_constant {Mc.flhs = e1 ; Mc.fop = o ; Mc.frhs = e2} =
   Term.mkApp(Lazy.force coq_Build,
	     [| typ; dump_expr typ dump_constant e1 ; 
		dump_op o ; 
		dump_expr typ dump_constant e2|])



 let parse_zop (op,args) =
  match kind_of_term op with
   | Const x -> 
      (match Names.string_of_con x with
       | "Coq.ZArith.BinInt#<>#Zgt" -> (Mc.OpGt, args.(0), args.(1))
       | "Coq.ZArith.BinInt#<>#Zge" -> (Mc.OpGe, args.(0), args.(1))
       | "Coq.ZArith.BinInt#<>#Zlt" -> (Mc.OpLt, args.(0), args.(1))
       | "Coq.ZArith.BinInt#<>#Zle" -> (Mc.OpLe, args.(0), args.(1))
       (*| "Coq.Init.Logic#<>#not"    -> Mc.OpNEq  (* for backward compat *)*)
       |   s -> raise ParseError
      )
   |  Ind(n,0) -> 
       (match Names.string_of_kn n with
	| "Coq.Init.Logic#<>#eq" -> 
	   if args.(0) <> Lazy.force coq_Z
	   then raise ParseError
	   else (Mc.OpEq, args.(1), args.(2))
	|  _ -> raise ParseError)
   |   _ -> failwith "parse_zop"


 let parse_rop (op,args) =
  try 
   match kind_of_term op with
    | Const x -> 
       (match Names.string_of_con x with
	| "Coq.Reals.Rdefinitions#<>#Rgt" -> (Mc.OpGt, args.(0), args.(1))
	| "Coq.Reals.Rdefinitions#<>#Rge" -> (Mc.OpGe, args.(0), args.(1))
	| "Coq.Reals.Rdefinitions#<>#Rlt" -> (Mc.OpLt, args.(0), args.(1))
	| "Coq.Reals.Rdefinitions#<>#Rle" -> (Mc.OpLe, args.(0), args.(1))
	   (*| "Coq.Init.Logic#<>#not"-> Mc.OpNEq  (* for backward compat *)*)
       |   s -> raise ParseError
       )
    |  Ind(n,0) -> 
	(match Names.string_of_kn n with
	 | "Coq.Init.Logic#<>#eq" -> 
	    (*   if args.(0) <> Lazy.force coq_R
		 then raise ParseError
		 else*) (Mc.OpEq, args.(1), args.(2))
	 |  _ -> raise ParseError)
    |   _ -> failwith "parse_rop"
  with x -> 
   (Pp.pp (Pp.str "parse_rop failure ") ; 
    Pp.pp (Printer.prterm op) ; Pp.pp_flush ()) 
   ; raise x


 let parse_qop (op,args) =
  (
   (match kind_of_term op with
   | Const x -> 
      (match Names.string_of_con x with
       | "Coq.QArith.QArith_base#<>#Qgt" -> Mc.OpGt
       | "Coq.QArith.QArith_base#<>#Qge" -> Mc.OpGe
       | "Coq.QArith.QArith_base#<>#Qlt" -> Mc.OpLt
       | "Coq.QArith.QArith_base#<>#Qle" -> Mc.OpLe
       | "Coq.QArith.QArith_base#<>#Qeq" -> Mc.OpEq
       |   s -> raise ParseError
      )
   |   _ -> failwith "parse_zop") , args.(0) , args.(1))


 module Env =
 struct 
  type t = constr list
    
  let compute_rank_add env v =
   let rec _add env n v =
    match env with
     | [] -> ([v],n)
     | e::l -> 
	if eq_constr e v 
	then (env,n)
	else 
	 let (env,n) = _add l ( n+1) v in
	  (e::env,n) in
   let (env, n) =  _add env 1 v in
    (env, CamlToCoq.idx n)

     
  let empty = []
   
  let elements env = env

 end


 let is_constant t = (* This is an approx *)
  match kind_of_term t with
   | Construct(i,_) -> true 
   |   _ -> false


 type 'a op = 
   | Binop of ('a Mc.pExpr -> 'a Mc.pExpr -> 'a Mc.pExpr) 
   | Opp 
   | Power 
   | Ukn of string


 let parse_expr parse_constant parse_exp ops_spec env term = 
 if debug 
 then (Pp.pp (Pp.str "parse_expr: ");   
       Pp.pp_flush ();Pp.pp (Printer.prterm  term); Pp.pp_flush ());

  let constant_or_variable env term = 
   try 
    ( Mc.PEc (parse_constant term) , env)
   with ParseError -> 
    let (env,n) = Env.compute_rank_add env term in
     (Mc.PEX  n , env) in

  let rec parse_expr env term = 
   let combine env op (t1,t2) =
    let (expr1,env) = parse_expr env t1 in
    let (expr2,env) = parse_expr env t2 in
    (op expr1 expr2,env) in
    match kind_of_term term with
     | App(t,args) -> 
	(
	 match kind_of_term t with
	  | Const c -> 
	     ( match ops_spec (Names.string_of_con c) with
	      | Binop f -> combine env f (args.(0),args.(1))
	      | Opp     -> let (expr,env) = parse_expr env args.(0) in
			    (Mc.PEopp expr, env)
	      | Power   -> 
		 let (expr,env) = parse_expr env args.(0) in
		 let exp = (parse_exp args.(1)) in 
		  (Mc.PEpow(expr, exp)  , env) 
	      | Ukn  s -> 
		 if debug 
		 then (Printf.printf "unknown op: %s\n" s; flush stdout;);
		 let (env,n) = Env.compute_rank_add env term in (Mc.PEX n, env)
	     )
	  |   _ -> constant_or_variable env term
	)
     | _ -> constant_or_variable env term in
   parse_expr env term
    

let zop_spec = function
 | "Coq.ZArith.BinInt#<>#Zplus"    -> Binop (fun x y -> Mc.PEadd(x,y))
 | "Coq.ZArith.BinInt#<>#Zminus"   -> Binop (fun x y -> Mc.PEsub(x,y)) 
 | "Coq.ZArith.BinInt#<>#Zmult"    -> Binop  (fun x y -> Mc.PEmul (x,y))
  | "Coq.ZArith.BinInt#<>#Zopp"     ->  Opp
  | "Coq.ZArith.Zpow_def#<>#Zpower" -> Power
  |  s                                   -> Ukn s

let qop_spec = function
 | "Coq.QArith.QArith_base#<>#Qplus"    -> Binop (fun x y -> Mc.PEadd(x,y))
 | "Coq.QArith.QArith_base#<>#Qminus"   -> Binop (fun x y -> Mc.PEsub(x,y)) 
 | "Coq.QArith.QArith_base#<>#Qmult"    -> Binop  (fun x y -> Mc.PEmul (x,y)) 
  | "Coq.QArith.QArith_base#<>#Qopp"     ->  Opp
  | "Coq.QArith.QArith_base#<>#Qpower" -> Power
  |  s                                   -> Ukn s

let rop_spec = function
 | "Coq.Reals.Rdefinitions#<>#Rplus"    -> Binop (fun x y -> Mc.PEadd(x,y))
 | "Coq.Reals.Rdefinitions#<>#Rminus"   -> Binop (fun x y -> Mc.PEsub(x,y)) 
 | "Coq.Reals.Rdefinitions#<>#Rmult"    -> Binop  (fun x y -> Mc.PEmul (x,y))
 | "Coq.Reals.Rdefinitions#<>#Ropp"     -> Opp
 | "Coq.Reals.Rpow_def#<>#pow"          -> Power
 |  s                                        -> Ukn s




      
let zconstant = parse_z
let qconstant = parse_q


let rconstant term = 
 if debug 
 then (Pp.pp_flush ();
       Pp.pp (Pp.str "rconstant: ");
       Pp.pp (Printer.prterm  term); Pp.pp_flush ());
 match Term.kind_of_term term with
  | Const x ->        
     (match Names.string_of_con x with
      | "Coq.Reals.Rdefinitions#<>#R0" -> Mc.Z0
      | "Coq.Reals.Rdefinitions#<>#R1" -> Mc.Zpos Mc.XH
      | _   -> raise ParseError
     )
  |  _ -> raise ParseError


let parse_zexpr = 
 parse_expr zconstant (fun x -> Mc.n_of_Z (parse_z x))  zop_spec 
let parse_qexpr  = 
 parse_expr qconstant (fun x -> Mc.n_of_Z (parse_z x)) qop_spec 
let parse_rexpr = 
 parse_expr rconstant  (fun x -> Mc.n_of_nat (parse_nat x)) rop_spec


 let  parse_arith parse_op parse_expr env cstr = 
  if debug 
  then (Pp.pp_flush ();
	Pp.pp (Pp.str "parse_arith: ");
	Pp.pp (Printer.prterm  cstr); 
	Pp.pp_flush ());
  match kind_of_term cstr with
   | App(op,args) -> 
      let (op,lhs,rhs) = parse_op (op,args) in
      let (e1,env) = parse_expr env lhs in
      let (e2,env) = parse_expr env rhs in
       ({Mc.flhs = e1; Mc.fop = op;Mc.frhs = e2},env)
   |  _ -> failwith "error : parse_arith(2)"

 let parse_zarith = parse_arith  parse_zop parse_zexpr 
  
 let parse_qarith = parse_arith  parse_qop parse_qexpr
  
 let parse_rarith = parse_arith  parse_rop parse_rexpr
  
  
 (* generic parsing of arithmetic expressions *)
  
 let rec parse_conj parse_arith env term = 
  match kind_of_term term with
   | App(l,rst) -> 
      (match kind_of_term l with
       | Ind (n,_) -> 
	  ( match Names.string_of_kn n with
	   | "Coq.Init.Logic#<>#and" -> 
	      let (e1,env) = parse_arith env rst.(0) in
	      let (e2,env) = parse_conj parse_arith env rst.(1) in
	       (Mc.Cons(e1,e2),env)
	   |   _ -> (* This might be an equality *) 
		let (e,env) = parse_arith env term in
		 (Mc.Cons(e,Mc.Nil),env))
       |  _ -> (* This is an arithmetic expression *)
	   let (e,env) = parse_arith env term in
	    (Mc.Cons(e,Mc.Nil),env))
   |  _ -> failwith "parse_conj(2)"



 let rec f2f = function
  | TT  -> Mc.TT
  | FF  -> Mc.FF
  | X _  -> Mc.X
  | A (x,_) -> Mc.A x
  | C (a,b,_)  -> Mc.Cj(f2f a,f2f b)
  | D (a,b,_)  -> Mc.D(f2f a,f2f b)
  | N (a,_) -> Mc.N(f2f a)
  | I(a,b,_)  -> Mc.I(f2f a,f2f b)

 let is_prop t = 
  match t with
   | Names.Anonymous -> true (* Not quite right *)
   | Names.Name x    -> false

 let mkC f1 f2 = C(f1,f2,none)
 let mkD f1 f2 = D(f1,f2,none)
 let mkIff f1 f2 = C(I(f1,f2,none),I(f2,f2,none),none)
 let mkI f1 f2 = I(f1,f2,none)

 let mkformula_binary g term f1 f2 =
   match f1 , f2 with
   |  X _  , X _ -> X(term)
   |   _         -> g f1 f2

 let parse_formula parse_atom env term =
  let parse_atom env t = try let (at,env) = parse_atom env t in (A(at,none), env) with _ -> (X(t),env) in

  let rec xparse_formula env term =
   match kind_of_term term with
    | App(l,rst) ->
        (match rst with
         | [|a;b|] when l = Lazy.force coq_and ->
	     let f,env = xparse_formula env a in
	     let g,env = xparse_formula env b in
             mkformula_binary mkC term f g,env
         | [|a;b|] when l = Lazy.force coq_or ->
	     let f,env = xparse_formula env a in
	     let g,env = xparse_formula env b in
             mkformula_binary mkD term f g,env
         | [|a|] when l = Lazy.force coq_not ->
             let (f,env) = xparse_formula env a in (N(f,none), env)
         | [|a;b|] when l = Lazy.force coq_iff ->
	     let f,env = xparse_formula env a in
	     let g,env = xparse_formula env b in
             mkformula_binary mkIff term f g,env
         | _ -> parse_atom env term)
    | Prod(typ,a,b) when not (Termops.dependent (mkRel 1) b) ->
	let f,env = xparse_formula env a in
	let g,env = xparse_formula env b in
        mkformula_binary mkI term f g,env
    | _ when term = Lazy.force coq_True -> (TT,env)
    | _ when term = Lazy.force coq_False -> (FF,env)
    | _  -> X(term),env in
  xparse_formula env term

 let coq_TT = lazy 
  (gen_constant_in_modules "ZMicromega" 
    [["Coq" ; "micromega" ; "Tauto"];["Tauto"]]  "TT")
 let coq_FF = lazy 
  (gen_constant_in_modules "ZMicromega" 
    [["Coq" ; "micromega" ; "Tauto"];["Tauto"]]  "FF")
 let coq_And = lazy 
  (gen_constant_in_modules "ZMicromega"    
    [["Coq" ; "micromega" ; "Tauto"];["Tauto"]]  "Cj")
 let coq_Or = lazy 
  (gen_constant_in_modules "ZMicromega"  
    [["Coq" ; "micromega" ; "Tauto"];["Tauto"]]    "D")
 let coq_Neg = lazy 
  (gen_constant_in_modules "ZMicromega" 
    [["Coq" ; "micromega" ; "Tauto"];["Tauto"]]  "N")
 let coq_Atom = lazy 
  (gen_constant_in_modules "ZMicromega" 
    [["Coq" ; "micromega" ; "Tauto"];["Tauto"]]  "A")
 let coq_X = lazy 
  (gen_constant_in_modules "ZMicromega"  
    [["Coq" ; "micromega" ; "Tauto"];["Tauto"]]  "X")
 let coq_Impl = lazy 
  (gen_constant_in_modules "ZMicromega" 
    [["Coq" ; "micromega" ; "Tauto"];["Tauto"]]  "I")
 let coq_Formula = lazy 
  (gen_constant_in_modules "ZMicromega" 
    [["Coq" ; "micromega" ; "Tauto"];["Tauto"]]  "BFormula")

 let dump_formula typ dump_atom f = 
  let rec xdump f = 
   match f with
    | TT  -> mkApp(Lazy.force coq_TT,[| typ|])
    | FF  -> mkApp(Lazy.force coq_FF,[| typ|])
    | C(x,y,_) -> mkApp(Lazy.force coq_And,[| typ ; xdump x ; xdump y|])
    | D(x,y,_) -> mkApp(Lazy.force coq_Or,[| typ ; xdump x ; xdump y|])
    | I(x,y,_) -> mkApp(Lazy.force coq_Impl,[| typ ; xdump x ; xdump y|])
    | N(x,_) -> mkApp(Lazy.force coq_Neg,[| typ ; xdump x|])
    | A(x,_) -> mkApp(Lazy.force coq_Atom,[| typ ; dump_atom x|]) 
    | X(t) -> mkApp(Lazy.force coq_X,[| typ ; t|])  in

   xdump f
    

 (* Backward compat *)

 let rec parse_concl parse_arith env term =
  match kind_of_term term with
   | Prod(_,expr,rst) -> (* a -> b *)
      let (lhs,rhs,env) = parse_concl parse_arith env rst in
      let (e,env) = parse_arith env expr in
       (Mc.Cons(e,lhs),rhs,env)
   | App(_,_) -> 
      let (conj, env) = parse_conj parse_arith env term in
       (Mc.Nil,conj,env)
   |  Ind(n,_) -> 
       (match (Names.string_of_kn n) with
	| "Coq.Init.Logic#<>#False" -> (Mc.Nil,Mc.Nil,env)
	|    s                           -> 
	      print_string s ; flush stdout;
	      failwith "parse_concl")
   |  _ -> failwith "parse_concl"


 let rec parse_hyps parse_arith env goal_hyps hyps = 
  match hyps with
   | [] -> ([],goal_hyps,env)
   | (i,t)::l -> 
      let (li,lt,env) = parse_hyps parse_arith env goal_hyps l in
       try 
	let (c,env) = parse_arith env  t in
	 (i::li, Mc.Cons(c,lt), env)
       with  x -> 
	(*(if debug then Printf.printf "parse_arith : %s\n" x);*)
	(li,lt,env)


 let parse_goal parse_arith env hyps term = 
  try
   let (lhs,rhs,env) = parse_concl parse_arith env term in
   let (li,lt,env) = parse_hyps parse_arith env lhs hyps in
    (li,lt,rhs,env)
  with Failure x -> raise ParseError
   (* backward compat *)


 (* ! reverse the list of bindings *)
 let set l concl =
  let rec _set acc = function
   | [] -> acc
   | (e::l) ->  
      let (name,expr,typ) = e in
       _set (Term.mkNamedLetIn
	      (Names.id_of_string name)
	      expr typ acc) l in
   _set concl l


end            

open M


let rec sig_of_cone = function
 | Mc.S_In n -> [CoqToCaml.nat n]
 | Mc.S_Ideal(e,w) -> sig_of_cone w
 | Mc.S_Mult(w1,w2) ->
    (sig_of_cone w1)@(sig_of_cone w2)
 | Mc.S_Add(w1,w2) -> 	(sig_of_cone w1)@(sig_of_cone w2)
 | _  -> []

let same_proof sg cl1 cl2 =
 let cl1 = CoqToCaml.list (fun x -> x) cl1 in
 let cl2 = CoqToCaml.list (fun x -> x) cl2 in
 let rec xsame_proof sg = 
  match sg with
   | [] -> true
   | n::sg -> (try List.nth cl1 n = List.nth cl2 n with _ -> false) 
      && (xsame_proof sg ) in
  xsame_proof sg




let tags_of_clause tgs wit clause = 
 let rec xtags tgs = function
  | Mc.S_In n -> Names.Idset.union tgs  
     (snd (List.nth clause (CoqToCaml.nat n) ))
  | Mc.S_Ideal(e,w) -> xtags tgs w
  | Mc.S_Mult (w1,w2) | Mc.S_Add(w1,w2) -> xtags (xtags tgs w1) w2
  |   _   -> tgs in
  xtags tgs wit

let tags_of_cnf wits cnf = 
 List.fold_left2 (fun acc w cl -> tags_of_clause acc w cl) 
  Names.Idset.empty wits cnf


let find_witness prover  polys1 =
 let l = CoqToCaml.list (fun x -> x) polys1 in
  try_any prover l

let rec witness prover   l1 l2 = 
 match l2 with
  | Micromega.Nil -> Some (Micromega.Nil)
  | Micromega.Cons(e,l2) -> 
     match find_witness prover   (Micromega.Cons( e,l1)) with
      | None -> None
      | Some w -> 
	 (match witness prover   l1 l2 with
	  | None -> None
	  | Some l -> Some (Micromega.Cons (w,l))
	 )


let rec apply_ids t ids = 
 match ids with
  | [] -> t
  | i::ids -> apply_ids (Term.mkApp(t,[| Term.mkVar i |])) ids

     
let coq_Node = lazy 
 (Coqlib.gen_constant_in_modules "VarMap" 
   [["Coq" ; "micromega" ; "VarMap"];["VarMap"]] "Node")
let coq_Leaf = lazy 
 (Coqlib.gen_constant_in_modules "VarMap" 
   [["Coq" ; "micromega" ; "VarMap"];["VarMap"]] "Leaf")
let coq_Empty = lazy 
 (Coqlib.gen_constant_in_modules "VarMap" 
   [["Coq" ; "micromega" ;"VarMap"];["VarMap"]] "Empty")
 
 
let btree_of_array typ a  =
 let size_of_a = Array.length a in
 let semi_size_of_a = size_of_a lsr 1 in
 let node = Lazy.force coq_Node
 and leaf = Lazy.force coq_Leaf
 and empty = Term.mkApp (Lazy.force coq_Empty, [| typ |]) in
 let rec aux n =
  if n > size_of_a 
  then empty
  else if  n > semi_size_of_a 
  then Term.mkApp (leaf, [| typ; a.(n-1) |])
  else Term.mkApp (node, [| typ; aux (2*n); a.(n-1); aux (2*n+1) |])
 in 
  aux 1

let btree_of_array typ a = 
 try 
  btree_of_array typ a
 with x -> 
  failwith (Printf.sprintf "btree of array : %s" (Printexc.to_string x))

let dump_varmap typ env =
 btree_of_array typ (Array.of_list env)


let rec pp_varmap o vm = 
 match vm with
  | Mc.Empty -> output_string o "[]"
  | Mc.Leaf z -> Printf.fprintf o "[%a]" pp_z  z
  | Mc.Node(l,z,r) -> Printf.fprintf o "[%a, %a, %a]" pp_varmap l  pp_z z pp_varmap r



let rec dump_proof_term = function 
 | Micromega.RatProof cone -> 
    Term.mkApp(Lazy.force coq_ratProof, [|dump_cone coq_Z dump_z cone|])
 | Micromega.CutProof(e,q,cone,prf) ->
    Term.mkApp(Lazy.force coq_cutProof, 
	      [| dump_expr (Lazy.force coq_Z) dump_z e ; 
		 dump_q q ; 
		 dump_cone coq_Z dump_z cone ; 
		 dump_proof_term prf|])
 | Micromega.EnumProof( q1,e1,q2,c1,c2,prfs) -> 
    Term.mkApp (Lazy.force coq_enumProof,
	       [| dump_q q1 ; dump_expr (Lazy.force coq_Z) dump_z e1 ; dump_q q2;
		  dump_cone coq_Z dump_z c1 ; dump_cone coq_Z dump_z c2 ; 
		  dump_list (Lazy.force coq_proofTerm) dump_proof_term prfs |])

let pp_q o q = Printf.fprintf o "%a/%a" pp_z q.Micromega.qnum pp_positive q.Micromega.qden
 
 
let rec pp_proof_term o = function
 | Micromega.RatProof cone -> Printf.fprintf o "R[%a]" (pp_cone pp_z) cone
 | Micromega.CutProof(e,q,_,p) -> failwith "not implemented"
 | Micromega.EnumProof(q1,e1,q2,c1,c2,rst) -> 
    Printf.fprintf o "EP[%a,%a,%a,%a,%a,%a]" 
     pp_q q1 pp_expr e1 pp_q q2 (pp_cone pp_z) c1 (pp_cone pp_z) c2 
     (pp_list "[" "]" pp_proof_term) rst

let rec parse_hyps parse_arith env hyps =
 match hyps with
  | [] -> ([],env)
  | (i,t)::l -> 
     let (lhyps,env) = parse_hyps parse_arith env l in
      try 
       let (c,env) = parse_formula parse_arith env  t in
	((i,c)::lhyps, env)
      with _ -> 		(lhyps,env)
       (*(if debug then Printf.printf "parse_arith : %s\n" x);*)


exception ParseError

let parse_goal parse_arith env hyps term = 
 (*  try*)
 let (f,env) = parse_formula parse_arith env term in
 let (lhyps,env) = parse_hyps parse_arith env hyps in
  (lhyps,f,env)
   (*  with Failure x -> raise ParseError*)


type ('a, 'b) domain_spec = { 
 typ : Term.constr; (* Z, Q , R *)
 coeff : Term.constr ; (* Z, Q *)
 dump_coeff : 'a -> Term.constr ; 
 proof_typ : Term.constr ; 
 dump_proof : 'b -> Term.constr
}

let zz_domain_spec  = lazy {
 typ = Lazy.force coq_Z;
 coeff = Lazy.force coq_Z;
 dump_coeff = dump_z ;
 proof_typ = Lazy.force coq_proofTerm ;
 dump_proof = dump_proof_term
}

let qq_domain_spec  = lazy {
 typ = Lazy.force coq_Q;
 coeff = Lazy.force coq_Q;
 dump_coeff = dump_q ;
 proof_typ = Lazy.force coq_QWitness ;
 dump_proof = dump_cone coq_Q dump_q
}

let rz_domain_spec = lazy {
 typ = Lazy.force coq_R;
 coeff = Lazy.force coq_Z;
 dump_coeff = dump_z;
 proof_typ = Lazy.force coq_ZWitness ;
 dump_proof = dump_cone coq_Z dump_z
}




let micromega_order_change spec cert cert_typ env  ff gl = 
 let formula_typ = (Term.mkApp( Lazy.force coq_Cstr,[|  spec.coeff|])) in

 let ff = dump_formula formula_typ (dump_cstr spec.coeff spec.dump_coeff) ff in
 let vm  = dump_varmap  ( spec.typ)  env in
  Tactics.change_in_concl None
   (set 
     [ 
      ("__ff", ff, Term.mkApp(Lazy.force coq_Formula ,[| formula_typ |]));
      ("__varmap", vm , Term.mkApp 
       (Coqlib.gen_constant_in_modules "VarMap" 
	 [["Coq" ; "micromega" ; "VarMap"];["VarMap"]] "t", [|  spec.typ|]));
      ("__wit", cert,cert_typ)
     ]  	
     (Tacmach.pf_concl gl )

       )
   gl 
   

let detect_duplicates cnf wit = 
 let cnf = CoqToCaml.list (fun x -> x) cnf in
 let wit = CoqToCaml.list (fun x -> x) wit in

 let rec xdup cnf wit = 
  match wit with
   | [] -> []
   | w :: wit -> 
      let sg = sig_of_cone w in
       match cnf with
	| [] -> []
	| e::cnf -> 
	   let (dups,cnf) = (List.partition (fun x -> same_proof sg e x) cnf) in
	    dups@(xdup cnf wit) in
  xdup cnf wit

let find_witness prover    polys1 =
 try_any prover polys1


let witness_list_with_tags prover l = 
 
 let rec xwitness_list l = 
  match l with
   | [] -> Some([])
   | e::l -> 
      match find_witness prover  (List.map fst e)  with
       | None -> None
       | Some w -> 
	  (match xwitness_list l with
	   | None -> None
	   | Some l -> Some (w::l)
	  ) in
  xwitness_list l

let witness_list_without_tags prover l = 
 
 let rec xwitness_list l = 
  match l with
   | [] -> Some([])
   | e::l -> 
      match find_witness prover e  with
       | None -> None
       | Some w -> 
	  (match xwitness_list l with
	   | None -> None
	   | Some l -> Some (w::l)
	  ) in
  xwitness_list l

let witness_list prover l = 
 let rec xwitness_list l = 
  match l with
   | Micromega.Nil -> Some(Micromega.Nil)
   | Micromega.Cons(e,l) -> 
      match find_witness prover e  with
       | None -> None
       | Some w -> 
	  (match xwitness_list l with
	   | None -> None
	   | Some l -> Some (Micromega.Cons(w,l))
	  ) in
  xwitness_list l




let is_singleton = function [] -> true | [e] -> true | _ -> false
 

let micromega_tauto negate normalise spec prover env polys1 polys2  gl = 
 let spec = Lazy.force spec in 
 let (ff,ids) = 
  List.fold_right 
   (fun (id,f)  (cc,ids) -> 
    match f with 
      X _ -> (cc,ids) 
     | _ -> (I(tag_formula (Names.Name id) f,cc,none), id::ids)) 
   polys1 (polys2,[]) in

 let cnf_ff = cnf negate normalise ff in

  if debug then 
   (Pp.pp (Pp.str "Formula....\n") ;
     let formula_typ = (Term.mkApp( Lazy.force coq_Cstr,[| spec.coeff|])) in
     let ff = dump_formula formula_typ 
      (dump_cstr spec.typ spec.dump_coeff) ff in
      Pp.pp (Printer.prterm  ff) ;  Pp.pp_flush ()) ;

   match witness_list_without_tags prover  cnf_ff with
    | None -> Tacticals.tclFAIL 0 (Pp.str "Cannot find witness") gl
    | Some res -> (*Printf.printf "\nList %i" (List.length res); *)
       let (ff,res,ids) = (ff,res,List.map Term.mkVar ids) in
       let res' = dump_ml_list (spec.proof_typ) spec.dump_proof  res in
	(Tacticals.tclTHENSEQ
	  [
	   Tactics.generalize ids;
	   micromega_order_change spec res' 
	    (Term.mkApp(Lazy.force coq_list,[|  spec.proof_typ|]))  env  ff ;
	   ]) gl


let micromega_gen parse_arith negate normalise spec  prover   gl =
 let concl = Tacmach.pf_concl gl in
 let hyps  = Tacmach.pf_hyps_types gl in
  try
   let (hyps,concl,env) = parse_goal parse_arith Env.empty hyps concl in
   let env = Env.elements env in
    micromega_tauto negate normalise spec prover env hyps concl gl
  with 
   | Failure x -> flush stdout ; Pp.pp_flush () ; 
      Tacticals.tclFAIL 0 (Pp.str x) gl
   | ParseError  -> Tacticals.tclFAIL 0 (Pp.str "Bad logical fragment") gl


let lift_ratproof prover l =
 match prover l with
  | None -> None
  | Some c -> Some (Mc.RatProof c)


type csdpcert = Certificate.Mc.z Certificate.Mc.coneMember option
type micromega_polys = (Micromega.z Mc.pExpr, Mc.op1) Micromega.prod list
type provername = string * int option

let call_csdpcert provername poly =
  let tmp_to,ch_to = Filename.open_temp_file "csdpcert" ".in" in
  let tmp_from = Filename.temp_file "csdpcert" ".out" in
  output_value ch_to (provername,poly : provername * micromega_polys);
  close_out ch_to;
  let cmdname =
    Filename.concat Coq_config.bindir
      ("csdpcert" ^ Coq_config.exec_extension) in
  let c = Sys.command (cmdname ^" "^ tmp_to ^" "^ tmp_from) in
  (try Sys.remove tmp_to with _ -> ());
  if c <> 0 then Util.error ("Failed to call csdp certificate generator");
  let ch_from = open_in tmp_from in
  let cert = (input_value ch_from : csdpcert) in
  close_in ch_from; Sys.remove tmp_from;
  cert

let omicron gl = 
 micromega_gen parse_zarith  Mc.negate Mc.normalise zz_domain_spec
  [lift_ratproof 
    (Certificate.linear_prover Certificate.z_spec), "fourier refutation" ] gl


let qomicron gl = 
 micromega_gen  parse_qarith Mc.cnf_negate Mc.cnf_normalise qq_domain_spec 
  [ Certificate.linear_prover Certificate.q_spec, "fourier refutation" ]   gl

let romicron gl = 
 micromega_gen  parse_rarith Mc.cnf_negate Mc.cnf_normalise rz_domain_spec 
  [ Certificate.linear_prover Certificate.z_spec, "fourier refutation" ]   gl


let rmicromega i gl = 
 micromega_gen parse_rarith Mc.negate Mc.normalise rz_domain_spec
  [ call_csdpcert ("real_nonlinear_prover", Some i), "fourier refutation" ]  gl

  
let micromega i gl = 
 micromega_gen parse_zarith Mc.negate Mc.normalise zz_domain_spec 
 [lift_ratproof (call_csdpcert ("real_nonlinear_prover",Some i)), 
  "fourier refutation" ] gl


let sos gl = 
 micromega_gen parse_zarith Mc.negate Mc.normalise  zz_domain_spec 
  [lift_ratproof (call_csdpcert ("pure_sos", None)), "pure sos refutation"]  gl

let zomicron gl = 
 micromega_gen parse_zarith Mc.negate Mc.normalise   zz_domain_spec 
  [Certificate.zlinear_prover, "zprover"] gl
