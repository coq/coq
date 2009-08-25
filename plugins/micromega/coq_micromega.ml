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
(*  Frédéric Besson (Irisa/Inria) 2006-2009                             *)
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


type tag = Tag.t
type 'cst atom = 'cst Micromega.formula

type 'cst formula =
  | TT 
  | FF 
  | X of Term.constr
  | A of 'cst atom * tag * Term.constr
  | C of 'cst  formula * 'cst formula 
  | D of 'cst formula * 'cst formula 
  | N of 'cst formula 
  | I of 'cst formula * Names.identifier option * 'cst formula 


let rec pp_formula o f = 
  match f with
    | TT -> output_string  o "tt"
    | FF -> output_string  o "ff"
    | X c -> output_string o "X " 
    | A(_,t,_) -> Printf.fprintf o "A(%a)" Tag.pp t
    | C(f1,f2) -> Printf.fprintf o "C(%a,%a)" pp_formula f1 pp_formula f2
    | D(f1,f2) -> Printf.fprintf o "D(%a,%a)" pp_formula f1 pp_formula f2
    | I(f1,n,f2) -> Printf.fprintf o "I(%a%s,%a)" 
	pp_formula f1 
	  (match n with 
	    | Some id -> Names.string_of_id id 
	    | None -> "") pp_formula f2
    | N(f) -> Printf.fprintf o "N(%a)" pp_formula f 

let rec ids_of_formula f =
  match f with
    | I(f1,Some id,f2) -> id::(ids_of_formula f2)
    | _                -> []

module ISet = Set.Make(struct type t = int let compare : int -> int -> int = Pervasives.compare end)

let selecti s m = 
  let rec xselect i m = 
    match m with
      | [] -> []
      | e::m -> if ISet.mem i s then e:: (xselect (i+1) m) else xselect (i+1) m in
    xselect 0 m


type 'cst clause = ('cst Micromega.nFormula * tag) list 

type 'cst cnf = ('cst clause) list

let tt : 'cst cnf = []
let ff : 'cst cnf = [ [] ]


type 'cst mc_cnf = ('cst Micromega.nFormula) list list

let cnf (negate: 'cst atom -> 'cst mc_cnf) (normalise:'cst atom -> 'cst mc_cnf) (f:'cst formula) = 
 let negate a t =
  List.map (fun cl -> List.map (fun x -> (x,t)) cl) (negate a) in

 let normalise a t =
     List.map (fun cl -> List.map (fun x -> (x,t)) cl) (normalise a) in

 let and_cnf x y = x @ y in

 let or_clause_cnf t f =  List.map (fun x -> t@x) f in
  
 let rec or_cnf f f'  =
  match f with
   | [] -> tt
   | e :: rst -> (or_cnf rst f') @ (or_clause_cnf e f') in
  
 let rec xcnf  (pol : bool) f    =
  match f with
   | TT -> if pol then tt else ff (* ?? *)
   | FF  -> if pol then ff else tt (* ?? *)
   | X p -> if pol then ff else ff (* ?? *)
   | A(x,t,_) -> if pol then normalise  x t else negate x t
   | N(e)  -> xcnf  (not pol) e
   | C(e1,e2) -> 
      (if pol then and_cnf else or_cnf) (xcnf  pol e1) (xcnf  pol e2)
   | D(e1,e2)  -> 
      (if pol then or_cnf else and_cnf) (xcnf  pol e1) (xcnf  pol e2)
   | I(e1,_,e2) -> 
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
     ["Coq";"Reals" ; "Rpow_def"];
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
 let coq_R0    = lazy (constant "R0")
 let coq_R1    = lazy (constant "R1")


 let coq_proofTerm = lazy (constant "ZArithProof")
 let coq_doneProof = lazy (constant "DoneProof")
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
 let coq_Zpower = lazy (constant "Zpower")
 let coq_N_of_Z = lazy 
  (gen_constant_in_modules "ZArithRing" 
    [["Coq";"setoid_ring";"ZArithRing"]] "N_of_Z")

 let coq_Qgt = lazy (constant "Qgt")
 let coq_Qge = lazy (constant "Qge")
 let coq_Qle = lazy (constant "Qle")
 let coq_Qlt = lazy (constant "Qlt")
 let coq_Qeq = lazy (constant "Qeq")


 let coq_Qplus = lazy (constant "Qplus")
 let coq_Qminus = lazy (constant "Qminus")
 let coq_Qopp = lazy (constant "Qopp")
 let coq_Qmult = lazy (constant "Qmult")
 let coq_Qpower = lazy (constant "Qpower")


 let coq_Rgt = lazy (constant "Rgt")
 let coq_Rge = lazy (constant "Rge")
 let coq_Rle = lazy (constant "Rle")
 let coq_Rlt = lazy (constant "Rlt")

 let coq_Rplus = lazy (constant "Rplus")
 let coq_Rminus = lazy (constant "Rminus")
 let coq_Ropp = lazy (constant "Ropp")
 let coq_Rmult = lazy (constant "Rmult")
 let coq_Rpower = lazy (constant "pow")


 let coq_PEX = lazy (constant "PEX" )
 let coq_PEc = lazy (constant"PEc")
 let coq_PEadd = lazy (constant "PEadd")
 let coq_PEopp = lazy (constant "PEopp")
 let coq_PEmul = lazy (constant "PEmul")
 let coq_PEsub = lazy (constant "PEsub")
 let coq_PEpow = lazy (constant "PEpow")

 let coq_PX = lazy (constant "PX" )
 let coq_Pc = lazy (constant"Pc")
 let coq_Pinj = lazy (constant "Pinj")


 let coq_OpEq = lazy (constant "OpEq")
 let coq_OpNEq = lazy (constant "OpNEq")
 let coq_OpLe = lazy (constant "OpLe")
 let coq_OpLt = lazy (constant  "OpLt")
 let coq_OpGe = lazy (constant "OpGe")
 let coq_OpGt = lazy (constant  "OpGt")


 let coq_PsatzIn = lazy (constant "PsatzIn")
 let coq_PsatzSquare = lazy (constant "PsatzSquare")
 let coq_PsatzMulE = lazy (constant "PsatzMulE")
 let coq_PsatzMultC = lazy (constant "PsatzMulC")
 let coq_PsatzAdd  = lazy (constant "PsatzAdd")
 let coq_PsatzC  = lazy (constant "PsatzC")
 let coq_PsatzZ    = lazy (constant "PsatzZ")
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

 let dump_pair t1 t2 dump_t1 dump_t2 (x,y) =
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
  | Term.App(c, args) -> if c = Lazy.force coq_Qmake then
	{Mc.qnum = parse_z args.(0) ; Mc.qden = parse_positive args.(1) }
      else raise ParseError
  |  _ -> raise ParseError

  
 let rec parse_list parse_elt term = 
  let (i,c) = get_left_construct term in
   match i with
    | 1 -> []
    | 2 -> parse_elt c.(1) :: parse_list parse_elt c.(2)
    | i -> raise ParseError


 let rec dump_list typ dump_elt l =
  match l with
   | [] -> Term.mkApp(Lazy.force coq_nil,[| typ |])
   | e :: l -> Term.mkApp(Lazy.force coq_cons,
			       [| typ; dump_elt e;dump_list typ dump_elt l|])


 let pp_list op cl elt o l = 
  let rec _pp  o l = 
   match l with
    | [] -> ()
    | [e] -> Printf.fprintf o "%a" elt e
    | e::l -> Printf.fprintf o "%a ,%a" elt e  _pp l in
   Printf.fprintf o "%s%a%s" op _pp l cl 


 let pp_var  = pp_positive
 let dump_var = dump_positive

 let pp_expr pp_z o e = 
 let rec pp_expr  o e = 
  match e with
   | Mc.PEX n -> Printf.fprintf o "V %a" pp_var n
   | Mc.PEc z -> pp_z o z
   | Mc.PEadd(e1,e2) -> Printf.fprintf o "(%a)+(%a)" pp_expr e1 pp_expr e2
   | Mc.PEmul(e1,e2) -> Printf.fprintf o "%a*(%a)" pp_expr e1 pp_expr e2
   | Mc.PEopp e -> Printf.fprintf o "-(%a)" pp_expr e
   | Mc.PEsub(e1,e2) -> Printf.fprintf o "(%a)-(%a)" pp_expr e1 pp_expr e2
   | Mc.PEpow(e,n) -> Printf.fprintf o "(%a)^(%a)" pp_expr e pp_n  n in
   pp_expr o e


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


 let dump_pol typ dump_c e = 
   let rec dump_pol e = 
     match e with 
       | Mc.Pc n -> mkApp(Lazy.force coq_Pc, [|typ ; dump_c n|])
       | Mc.Pinj(p,pol) -> mkApp(Lazy.force coq_Pinj , [| typ ; dump_positive p ; dump_pol pol|])
       | Mc.PX(pol1,p,pol2) -> mkApp(Lazy.force coq_PX, [| typ ; dump_pol pol1 ; dump_positive p ; dump_pol pol2|]) in
     dump_pol e

 let pp_pol pp_c o e = 
   let rec pp_pol o e = 
     match e with 
       | Mc.Pc n -> Printf.fprintf o "Pc %a" pp_c n
       | Mc.Pinj(p,pol) -> Printf.fprintf o "Pinj(%a,%a)" pp_positive p pp_pol pol
       | Mc.PX(pol1,p,pol2) -> Printf.fprintf o "PX(%a,%a,%a)" pp_pol pol1 pp_positive p pp_pol pol2 in
     pp_pol o e
     
   
 let pp_cnf pp_c o f = 
   let pp_clause o l = List.iter (fun ((p,_),t) -> Printf.fprintf o "(%a @%a)" (pp_pol pp_c)  p Tag.pp t) l in
     List.iter (fun l -> Printf.fprintf o "[%a]" pp_clause l) f

	   
 let dump_psatz typ dump_z e = 
  let z = Lazy.force typ in 
 let rec dump_cone e =
  match e with
   | Mc.PsatzIn n -> mkApp(Lazy.force coq_PsatzIn,[| z; dump_nat n |])
   | Mc.PsatzMulC(e,c) -> mkApp(Lazy.force coq_PsatzMultC, 
			     [| z; dump_pol z dump_z e ; dump_cone c |])
   | Mc.PsatzSquare e -> mkApp(Lazy.force coq_PsatzSquare, 
			   [| z;dump_pol z dump_z e|])
   | Mc.PsatzAdd(e1,e2) -> mkApp(Lazy.force coq_PsatzAdd,
			     [| z; dump_cone e1; dump_cone e2|])
   | Mc.PsatzMulE(e1,e2) -> mkApp(Lazy.force coq_PsatzMulE,
			      [| z; dump_cone e1; dump_cone e2|])
   | Mc.PsatzC p -> mkApp(Lazy.force coq_PsatzC,[| z; dump_z p|])
   | Mc.PsatzZ    -> mkApp( Lazy.force coq_PsatzZ,[| z|]) in 
  dump_cone e


 let  pp_psatz pp_z o e = 
  let rec pp_cone o e = 
   match e with 
    | Mc.PsatzIn n -> 
       Printf.fprintf o "(In %a)%%nat" pp_nat n
    | Mc.PsatzMulC(e,c) -> 
       Printf.fprintf o "( %a [*] %a)" (pp_pol pp_z) e pp_cone c
    | Mc.PsatzSquare e -> 
       Printf.fprintf o "(%a^2)" (pp_pol pp_z) e
    | Mc.PsatzAdd(e1,e2) -> 
       Printf.fprintf o "(%a [+] %a)" pp_cone e1 pp_cone e2
    | Mc.PsatzMulE(e1,e2) -> 
       Printf.fprintf o "(%a [*] %a)" pp_cone e1 pp_cone e2
    | Mc.PsatzC p -> 
       Printf.fprintf o "(%a)%%positive" pp_z p
    | Mc.PsatzZ    -> 
       Printf.fprintf o "0" in
   pp_cone o e


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




 let pp_cstr pp_z o {Mc.flhs = l ; Mc.fop = op ; Mc.frhs = r } =
  Printf.fprintf o"(%a %a %a)" (pp_expr pp_z) l pp_op op (pp_expr pp_z) r

 let dump_cstr typ dump_constant {Mc.flhs = e1 ; Mc.fop = o ; Mc.frhs = e2} =
   Term.mkApp(Lazy.force coq_Build,
	     [| typ; dump_expr typ dump_constant e1 ; 
		dump_op o ; 
		dump_expr typ dump_constant e2|])

 let assoc_const x l = 
  try 
  snd (List.find (fun (x',y) -> x = Lazy.force x') l)
  with
    Not_found -> raise ParseError

 let zop_table = [ 
  coq_Zgt, Mc.OpGt ; 
  coq_Zge, Mc.OpGe ;
  coq_Zlt, Mc.OpLt ;
  coq_Zle, Mc.OpLe ]

 let rop_table = [ 
  coq_Rgt, Mc.OpGt ; 
  coq_Rge, Mc.OpGe ;
  coq_Rlt, Mc.OpLt ;
  coq_Rle, Mc.OpLe ]

 let qop_table = [ 
  coq_Qlt, Mc.OpLt ;
  coq_Qle, Mc.OpLe ;
  coq_Qeq, Mc.OpEq
 ]


 let parse_zop (op,args) =
  match kind_of_term op with
   | Const x -> (assoc_const op zop_table, args.(0) , args.(1))
   |  Ind(n,0) -> 
       if op = Lazy.force coq_Eq &&   args.(0) = Lazy.force coq_Z
       then (Mc.OpEq, args.(1), args.(2))
       else raise ParseError
   |   _ -> failwith "parse_zop"


 let parse_rop (op,args) =
   match kind_of_term op with
    | Const x -> (assoc_const op rop_table, args.(0) , args.(1))
    |  Ind(n,0) -> 
       if op = Lazy.force coq_Eq &&   args.(0) = Lazy.force coq_R
       then (Mc.OpEq, args.(1), args.(2))
       else raise ParseError
   |   _ -> failwith "parse_zop"

 let parse_qop (op,args) =
   (assoc_const op qop_table, args.(0) , args.(1))


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


 let assoc_ops x l = 
  try 
    snd (List.find (fun (x',y) -> x = Lazy.force x') l)
  with
    Not_found -> Ukn "Oups"



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
	     ( match assoc_ops t ops_spec  with
	      | Binop f -> combine env f (args.(0),args.(1))
	      | Opp     -> let (expr,env) = parse_expr env args.(0) in
			    (Mc.PEopp expr, env)
	      | Power   -> 
		  begin
		    try 
		      let (expr,env) = parse_expr env args.(0) in
		      let exp = (parse_exp args.(1)) in 
			(Mc.PEpow(expr, exp)  , env) 
		    with _ ->   (* if the exponent is a variable *)
		      let (env,n) = Env.compute_rank_add env term in (Mc.PEX n, env)
		  end
	      | Ukn  s -> 
		 if debug 
		 then (Printf.printf "unknown op: %s\n" s; flush stdout;);
		 let (env,n) = Env.compute_rank_add env term in (Mc.PEX n, env)
	     )
	  |   _ -> constant_or_variable env term
	)
     | _ -> constant_or_variable env term in
   parse_expr env term
    

 let zop_spec = 
   [ 
     coq_Zplus , Binop (fun x y -> Mc.PEadd(x,y)) ;
     coq_Zminus , Binop (fun x y -> Mc.PEsub(x,y)) ;
     coq_Zmult  , Binop  (fun x y -> Mc.PEmul (x,y)) ; 
     coq_Zopp   , Opp ; 
     coq_Zpower , Power]

let qop_spec = 
  [
     coq_Qplus , Binop (fun x y -> Mc.PEadd(x,y)) ;
     coq_Qminus , Binop (fun x y -> Mc.PEsub(x,y)) ;
     coq_Qmult  , Binop  (fun x y -> Mc.PEmul (x,y)) ; 
     coq_Qopp   , Opp ; 
     coq_Qpower , Power]

let rop_spec = 
  [
     coq_Rplus , Binop (fun x y -> Mc.PEadd(x,y)) ;
     coq_Rminus , Binop (fun x y -> Mc.PEsub(x,y)) ;
     coq_Rmult  , Binop  (fun x y -> Mc.PEmul (x,y)) ; 
     coq_Ropp   , Opp ; 
     coq_Rpower , Power]




      
let zconstant = parse_z
let qconstant = parse_q


let rconstant term = 
 if debug 
 then (Pp.pp_flush ();
       Pp.pp (Pp.str "rconstant: ");
       Pp.pp (Printer.prterm  term); Pp.pp_flush ());
 match Term.kind_of_term term with
  | Const x ->  
      if term = Lazy.force coq_R0
      then Mc.Z0
      else if term = Lazy.force coq_R1
      then Mc.Zpos Mc.XH
      else raise ParseError
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
  



 let rec f2f = function
  | TT  -> Mc.TT
  | FF  -> Mc.FF
  | X _  -> Mc.X
  | A (x,_,_) -> Mc.A x
  | C (a,b)  -> Mc.Cj(f2f a,f2f b)
  | D (a,b)  -> Mc.D(f2f a,f2f b)
  | N (a) -> Mc.N(f2f a)
  | I(a,_,b)  -> Mc.I(f2f a,f2f b)

 let is_prop t = 
  match t with
   | Names.Anonymous -> true (* Not quite right *)
   | Names.Name x    -> false

 let mkC f1 f2 = C(f1,f2)
 let mkD f1 f2 = D(f1,f2)
 let mkIff f1 f2 = C(I(f1,None,f2),I(f2,None,f1))
 let mkI f1 f2 = I(f1,None,f2)

 let mkformula_binary g term f1 f2 =
   match f1 , f2 with
   |  X _  , X _ -> X(term)
   |   _         -> g f1 f2

 let parse_formula parse_atom env term =

  let parse_atom env tg t = try let (at,env) = parse_atom env t in 
				  (A(at,tg,t), env,Tag.next tg) with _ -> (X(t),env,tg) in

  let rec xparse_formula env tg term =
   match kind_of_term term with
    | App(l,rst) ->
        (match rst with
         | [|a;b|] when l = Lazy.force coq_and ->
	     let f,env,tg = xparse_formula env tg a in
	     let g,env, tg = xparse_formula env tg b  in
             mkformula_binary mkC term f g,env,tg
         | [|a;b|] when l = Lazy.force coq_or ->
	     let f,env,tg = xparse_formula env tg a in
	     let g,env,tg  = xparse_formula env tg b in
             mkformula_binary mkD term f g,env,tg
         | [|a|] when l = Lazy.force coq_not ->
             let (f,env,tg) = xparse_formula env tg a in (N(f), env,tg)
         | [|a;b|] when l = Lazy.force coq_iff ->
	     let f,env,tg = xparse_formula env tg a in
	     let g,env,tg = xparse_formula env tg b in
             mkformula_binary mkIff term f g,env,tg
         | _ -> parse_atom env tg term)
    | Prod(typ,a,b) when not (Termops.dependent (mkRel 1) b) ->
	let f,env,tg = xparse_formula env tg a in
	let g,env,tg = xparse_formula env tg b in
        mkformula_binary mkI term f g,env,tg
    | _ when term = Lazy.force coq_True -> (TT,env,tg)
    | _ when term = Lazy.force coq_False -> (FF,env,tg)
    | _  -> X(term),env,tg in
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
    | C(x,y) -> mkApp(Lazy.force coq_And,[| typ ; xdump x ; xdump y|])
    | D(x,y) -> mkApp(Lazy.force coq_Or,[| typ ; xdump x ; xdump y|])
    | I(x,_,y) -> mkApp(Lazy.force coq_Impl,[| typ ; xdump x ; xdump y|])
    | N(x) -> mkApp(Lazy.force coq_Neg,[| typ ; xdump x|])
    | A(x,_,_) -> mkApp(Lazy.force coq_Atom,[| typ ; dump_atom x|]) 
    | X(t) -> mkApp(Lazy.force coq_X,[| typ ; t|])  in

   xdump f
    



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
 | Mc.PsatzIn n -> [CoqToCaml.nat n]
 | Mc.PsatzMulE(w1,w2) ->
    (sig_of_cone w1)@(sig_of_cone w2)
 | Mc.PsatzMulC(w1,w2) -> (sig_of_cone w2)
 | Mc.PsatzAdd(w1,w2) -> 	(sig_of_cone w1)@(sig_of_cone w2)
 | _  -> []

let same_proof sg cl1 cl2 =
 let rec xsame_proof sg = 
  match sg with
   | [] -> true
   | n::sg -> (try List.nth cl1 n = List.nth cl2 n with _ -> false) 
      && (xsame_proof sg ) in
  xsame_proof sg




let tags_of_clause tgs wit clause = 
 let rec xtags tgs = function
  | Mc.PsatzIn n -> Names.Idset.union tgs  
     (snd (List.nth clause (CoqToCaml.nat n) ))
  | Mc.PsatzMulC(e,w) -> xtags tgs w
  | Mc.PsatzMulE (w1,w2) | Mc.PsatzAdd(w1,w2) -> xtags (xtags tgs w1) w2
  |   _   -> tgs in
  xtags tgs wit

let tags_of_cnf wits cnf = 
 List.fold_left2 (fun acc w cl -> tags_of_clause acc w cl) 
  Names.Idset.empty wits cnf


let find_witness prover polys1 = try_any prover polys1

let rec witness prover   l1 l2 = 
 match l2 with
  | [] -> Some []
  | e :: l2 ->
     match find_witness prover (e::l1) with
      | None -> None
      | Some w ->
	 (match witness prover l1 l2 with
	  | None -> None
	  | Some l -> Some (w::l)
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
  | Micromega.DoneProof -> Lazy.force coq_doneProof
  | Micromega.RatProof(cone,rst) -> 
    Term.mkApp(Lazy.force coq_ratProof, [| dump_psatz coq_Z dump_z cone; dump_proof_term rst|])
 | Micromega.CutProof(cone,prf) ->
    Term.mkApp(Lazy.force coq_cutProof, 
	      [| dump_psatz coq_Z dump_z cone ; 
		 dump_proof_term prf|])
 | Micromega.EnumProof(c1,c2,prfs) -> 
    Term.mkApp (Lazy.force coq_enumProof,
	       [|  dump_psatz coq_Z dump_z c1 ; dump_psatz coq_Z dump_z c2 ; 
		  dump_list (Lazy.force coq_proofTerm) dump_proof_term prfs |])

let pp_q o q = Printf.fprintf o "%a/%a" pp_z q.Micromega.qnum pp_positive q.Micromega.qden
 
 
let rec pp_proof_term o = function
  | Micromega.DoneProof -> Printf.fprintf o "D"
  | Micromega.RatProof(cone,rst) -> Printf.fprintf o "R[%a,%a]" (pp_psatz  pp_z) cone pp_proof_term rst
  | Micromega.CutProof(cone,rst) -> Printf.fprintf o "C[%a,%a]" (pp_psatz  pp_z) cone pp_proof_term rst
  | Micromega.EnumProof(c1,c2,rst) -> 
      Printf.fprintf o "EP[%a,%a,%a]" 
	(pp_psatz pp_z) c1 (pp_psatz pp_z) c2 
     (pp_list "[" "]" pp_proof_term) rst

let rec parse_hyps parse_arith env tg hyps =
 match hyps with
  | [] -> ([],env,tg)
  | (i,t)::l -> 
     let (lhyps,env,tg) = parse_hyps parse_arith env tg l in
      try 
       let (c,env,tg) = parse_formula parse_arith env  tg t in
	((i,c)::lhyps, env,tg)
      with _ -> 		(lhyps,env,tg)
       (*(if debug then Printf.printf "parse_arith : %s\n" x);*)


exception ParseError

let parse_goal parse_arith env hyps term = 
 (*  try*)
 let (f,env,tg) = parse_formula parse_arith env (Tag.from 0) term in
 let (lhyps,env,tg) = parse_hyps parse_arith env tg hyps in
  (lhyps,f,env)
   (*  with Failure x -> raise ParseError*)


type ('d, 'prf) domain_spec = { 
 typ : Term.constr; (* Z, Q , R *)
 coeff : Term.constr ; (* Z, Q *)
 dump_coeff : 'd -> Term.constr ; 
 proof_typ : Term.constr ; 
 dump_proof : 'prf -> Term.constr
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
 dump_proof = dump_psatz coq_Q dump_q
}

let rz_domain_spec = lazy {
 typ = Lazy.force coq_R;
 coeff = Lazy.force coq_Z;
 dump_coeff = dump_z;
 proof_typ = Lazy.force coq_ZWitness ;
 dump_proof = dump_psatz coq_Z dump_z
}


let abstract_formula hyps f = 
  
  let rec xabs f = 
    match f with
      | X c -> X c
      | A(a,t,term) -> if TagSet.mem t hyps then A(a,t,term) else X(term)
      | C(f1,f2) -> 
	  (match xabs f1 , xabs f2 with
	    |   X a1    ,  X a2   -> X (Term.mkApp(Lazy.force coq_and, [|a1;a2|]))
	    |    f1     , f2      -> C(f1,f2) )
      | D(f1,f2) -> 
	  (match xabs f1 , xabs f2 with
	    |   X a1    ,  X a2   -> X (Term.mkApp(Lazy.force coq_or, [|a1;a2|]))
	    |    f1     , f2      -> D(f1,f2) )
      | N(f) -> 
	  (match xabs f with
	    |   X a    -> X (Term.mkApp(Lazy.force coq_not, [|a|]))
	    |     f     -> N f)
      | I(f1,hyp,f2) -> 
	  (match xabs f1 , hyp, xabs f2 with
	    | X a1      , Some _ , af2    ->  af2
	    | X a1      , None   , X a2   -> X (Term.mkArrow a1 a2)
	    |   af1     ,  _     , af2    -> I(af1,hyp,af2)
	  )
      | FF -> FF
      | TT -> TT

  in  xabs f




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
   

type ('a,'prf) prover = {
  name : string ; (* name of the prover *)
  prover : 'a list -> 'prf option; (* the prover itself *)
  hyps : 'prf -> ISet.t; (* extract the indexes of the hypotheses really used in the proof *)
  compact : 'prf -> (int -> int) -> 'prf; (* remap the hyp indexes according to function *)
  pp_prf : out_channel -> 'prf -> unit ;(* pretting printing of proof *)
  pp_f   : out_channel -> 'a   -> unit
}

let find_witness provers    polys1 =
  
  let provers = List.map (fun p -> 
    (fun l -> 
      match p.prover l with
        | None -> None
        | Some prf -> Some(prf,p)) , p.name) provers in
                           
    try_any provers (List.map fst polys1)


let witness_list prover l = 
 let rec xwitness_list l = 
  match l with
   | [] -> Some []
   | e :: l ->
      match find_witness prover e  with
       | None -> None
       | Some w ->
	  (match xwitness_list l with
	   | None -> None
	   | Some l -> Some (w :: l)
	  ) in
  xwitness_list l


let witness_list_tags  = witness_list
 
let is_singleton = function [] -> true | [e] -> true | _ -> false

let pp_ml_list pp_elt o l = 
  output_string o "[" ;
  List.iter (fun x -> Printf.fprintf o "%a ;" pp_elt x) l ; 
  output_string o "]" 

let compact_proofs (cnf_ff: 'cst cnf) res (cnf_ff': 'cst cnf) = 

  let compact_proof (old_cl:'cst clause) (prf,prover) (new_cl:'cst clause) = 
    let new_cl = Mutils.mapi (fun (f,_) i -> (f,i)) new_cl in
    let remap i = 
      let formula = try fst (List.nth old_cl i) with Failure _ -> failwith "bad old index" in
	List.assoc formula new_cl in

      if debug then 
	begin
	  Printf.printf "\ncompact_proof : %a %a %a" 
	    (pp_ml_list prover.pp_f) (List.map fst old_cl) 
	    prover.pp_prf prf 
	    (pp_ml_list prover.pp_f) (List.map fst new_cl)   ;
	    flush stdout
	end ;
      let res = try prover.compact prf remap with x ->
	if debug then Printf.fprintf stdout "Proof compaction %s" (Printexc.to_string x) ; 
	(* This should not happen -- this is the recovery plan... *)
	match prover.prover (List.map fst new_cl) with 
	  | None -> failwith "proof compaction error"
	  | Some p ->  p 
      in
      if debug then 
	begin
	  Printf.printf " -> %a\n" 
	    prover.pp_prf res ;
	  flush stdout
	end
	  ; 
      res in



  let is_proof_compatible (old_cl:'cst clause) (prf,prover) (new_cl:'cst clause) = 
    let hyps_idx = prover.hyps prf in
    let hyps = selecti hyps_idx old_cl in
      is_sublist hyps new_cl in

  let cnf_res = List.combine cnf_ff res in (* we get pairs clause * proof *)
    
    List.map (fun x -> 
      let (o,p) = List.find (fun (l,p) -> is_proof_compatible l p x) cnf_res 
      in compact_proof o p x) cnf_ff' 
    



let micromega_tauto negate normalise spec prover env polys1 polys2  gl = 
 let spec = Lazy.force spec in 
 let (ff,ids) = 
  List.fold_right 
   (fun (id,f)  (cc,ids) -> 
    match f with 
      X _ -> (cc,ids) 
     | _ -> (I(f,Some id,cc), id::ids)) 
   polys1 (polys2,[]) in

 let cnf_ff = cnf negate normalise ff in

  if debug then 
    begin
      Pp.pp (Pp.str "Formula....\n") ;
      let formula_typ = (Term.mkApp( Lazy.force coq_Cstr,[| spec.coeff|])) in
      let ff = dump_formula formula_typ 
        (dump_cstr spec.typ spec.dump_coeff) ff in
        Pp.pp (Printer.prterm  ff) ;  Pp.pp_flush ();
	  Printf.fprintf stdout "cnf : %a\n" (pp_cnf (fun o _ -> ())) cnf_ff
    end;

   match witness_list_tags prover  cnf_ff with
    | None -> Tacticals.tclFAIL 0 (Pp.str "Cannot find witness") gl
    | Some res -> (*Printf.printf "\nList %i" (List.length `res); *)

        let hyps = List.fold_left (fun s (cl,(prf,p)) -> 
	  let tags = ISet.fold (fun i s -> let t = snd (List.nth cl i) in
					     if debug then (Printf.fprintf stdout "T : %i -> %a" i Tag.pp t) ;
	    (*try*) TagSet.add t s (* with Invalid_argument _ -> s*)) (p.hyps prf) TagSet.empty in
	  TagSet.union s tags) TagSet.empty (List.combine cnf_ff res) in

	  if debug then (Printf.printf "TForm : %a\n" pp_formula ff ; flush stdout;
			 Printf.printf "Hyps : %a\n" (fun o s -> TagSet.fold (fun i _ -> Printf.fprintf o "%a " Tag.pp i) s ()) hyps) ;  
	  
        let ff'   = abstract_formula hyps ff in
	  
        let cnf_ff' = cnf negate normalise ff' in

	  if debug then
	    begin
	      Pp.pp (Pp.str "\nAFormula\n") ; 
	      let formula_typ = (Term.mkApp( Lazy.force coq_Cstr,[| spec.coeff|])) in
	      let ff' = dump_formula formula_typ 
		(dump_cstr spec.typ spec.dump_coeff) ff' in
		Pp.pp (Printer.prterm  ff') ;  Pp.pp_flush ();
		Printf.fprintf stdout "cnf : %a\n" (pp_cnf (fun o _ -> ())) cnf_ff'
	    end;

   (* Even if it does not work, this does not mean it is not provable 
      -- the prover is REALLY incomplete *)
(*	if debug then
	  begin
	    (* recompute the proofs *)
	    match witness_list_tags prover  cnf_ff' with
	      | None -> failwith "abstraction is wrong"
	      | Some res -> ()
	  end ; *)
	  let res' = compact_proofs cnf_ff res cnf_ff' in

        let (ff',res',ids) = (ff',res',List.map Term.mkVar (ids_of_formula ff')) in

       let res' = dump_list (spec.proof_typ) spec.dump_proof   res' in
        (Tacticals.tclTHENSEQ
          [
           Tactics.generalize ids;
           micromega_order_change spec res' 
            (Term.mkApp(Lazy.force coq_list,[|  spec.proof_typ|]))  env  ff' ;
           ]) gl


let micromega_gen 
    parse_arith 
    (negate:'cst atom -> 'cst mc_cnf) 
    (normalise:'cst atom -> 'cst mc_cnf) 
    spec  prover   gl =
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


let lift_ratproof  prover l =
 match prover l with
  | None -> None
  | Some c -> Some (Mc.RatProof( c,Mc.DoneProof))

type micromega_polys = (Micromega.q Mc.pol * Mc.op1) list
type csdp_certificate = S of Sos_types.positivstellensatz option | F of string
type provername = string * int option

open Persistent_cache

module Cache = PHashtable(struct 
  type t = (provername * micromega_polys) 
  let equal = (=)
  let hash  = Hashtbl.hash
end)

let csdp_cache = "csdp.cache" 

let really_call_csdpcert : provername -> micromega_polys -> Sos_types.positivstellensatz option  =
  fun provername poly -> 

  let cmdname =
    List.fold_left Filename.concat (Envars.coqlib ())
      ["plugins"; "micromega"; "csdpcert" ^ Coq_config.exec_extension] in

    match ((command cmdname [| cmdname |] (provername,poly)) : csdp_certificate) with
      | F str -> failwith str
      | S res -> res



let xcall_csdpcert =
  Cache.memo csdp_cache (fun (prover,pb) -> really_call_csdpcert prover pb)


let call_csdpcert prover pb = xcall_csdpcert (prover,pb)

let rec z_to_q_pol e = 
 match e with
  | Mc.Pc z   -> Mc.Pc {Mc.qnum = z ; Mc.qden = Mc.XH}
  | Mc.Pinj(p,pol)   -> Mc.Pinj(p,z_to_q_pol pol)
  | Mc.PX(pol1,p,pol2) -> Mc.PX(z_to_q_pol pol1, p, z_to_q_pol pol2)


let call_csdpcert_q provername poly = 
 match call_csdpcert provername poly with
  | None -> None
  | Some cert -> 
     let cert = Certificate.q_cert_of_pos cert in
     if Mc.qWeakChecker poly cert
     then Some cert
     else ((print_string "buggy certificate" ; flush stdout) ;None)


let call_csdpcert_z provername poly = 
 let l = List.map (fun (e,o) -> (z_to_q_pol e,o)) poly in
  match call_csdpcert provername l with
   | None -> None
   | Some cert -> 
      let cert = Certificate.z_cert_of_pos cert in
      if Mc.zWeakChecker poly cert
      then Some cert
      else ((print_string "buggy certificate" ; flush stdout) ;None)


let  xhyps_of_cone base acc prf = 
  let rec xtract e acc = 
    match e with
    | Mc.PsatzC _ | Mc.PsatzZ | Mc.PsatzSquare _ -> acc
    | Mc.PsatzIn n -> let n = (CoqToCaml.nat n) in
			if n >= base
			then  ISet.add (n-base) acc
			else acc
    | Mc.PsatzMulC(_,c) -> xtract  c acc
    | Mc.PsatzAdd(e1,e2) |  Mc.PsatzMulE(e1,e2) -> xtract e1 (xtract e2 acc) in

    xtract prf acc

let hyps_of_cone prf = xhyps_of_cone 0 ISet.empty prf

let compact_cone prf f  =
  let np n = CamlToCoq.nat (f (CoqToCaml.nat n)) in

  let rec xinterp prf = 
    match prf with
    | Mc.PsatzC _ | Mc.PsatzZ | Mc.PsatzSquare _ -> prf
    | Mc.PsatzIn n -> Mc.PsatzIn (np n)
    | Mc.PsatzMulC(e,c) -> Mc.PsatzMulC(e,xinterp c)
    | Mc.PsatzAdd(e1,e2) -> Mc.PsatzAdd(xinterp e1,xinterp e2)
    | Mc.PsatzMulE(e1,e2) -> Mc.PsatzMulE(xinterp e1,xinterp e2) in

    xinterp prf

let hyps_of_pt pt = 
  let rec xhyps base pt acc = 
    match pt with
      | Mc.DoneProof -> acc
      | Mc.RatProof(c,pt) ->  xhyps (base+1) pt (xhyps_of_cone base acc c)
      | Mc.CutProof(c,pt) -> xhyps (base+1) pt (xhyps_of_cone base acc c)
      | Mc.EnumProof(c1,c2,l) -> 
	  let s = xhyps_of_cone base (xhyps_of_cone base acc c2) c1 in
	    List.fold_left (fun s x -> xhyps (base + 1) x s) s l in
    
    xhyps 0 pt ISet.empty

let hyps_of_pt pt = 
  let res = hyps_of_pt pt in
    if debug 
    then (Printf.fprintf stdout "\nhyps_of_pt : %a -> " pp_proof_term pt ; ISet.iter (fun i -> Printf.printf "%i " i) res);
    res
	  
  
let compact_pt pt f = 
  let translate ofset x =
    if x < ofset then x
    else (f (x-ofset)  + ofset) in

  let rec compact_pt ofset pt = 
    match pt with
      | Mc.DoneProof -> Mc.DoneProof
      | Mc.RatProof(c,pt) -> Mc.RatProof(compact_cone c (translate (ofset)), compact_pt (ofset+1) pt )
      | Mc.CutProof(c,pt) -> Mc.CutProof(compact_cone c (translate (ofset)), compact_pt (ofset+1) pt )
      | Mc.EnumProof(c1,c2,l) -> Mc.EnumProof(compact_cone c1 (translate (ofset)), compact_cone c2 (translate (ofset)),
						   Mc.map (fun x -> compact_pt (ofset+1) x) l) in
    compact_pt 0 pt



(** Definition of provers *)

let lift_pexpr_prover p l =  p (List.map (fun (e,o) -> Mc.denorm e , o) l)

let linear_prover_Z = {
  name    = "linear prover" ; 
  prover  = lift_ratproof (lift_pexpr_prover (Certificate.linear_prover_with_cert Certificate.z_spec)) ; 
  hyps    = hyps_of_pt ;
  compact = compact_pt ;
  pp_prf  = pp_proof_term;
  pp_f    = fun o x -> pp_pol pp_z o (fst x)
}

let linear_prover_Q = {
  name    = "linear prover";
  prover  = lift_pexpr_prover (Certificate.linear_prover_with_cert Certificate.q_spec) ; 
  hyps    = hyps_of_cone ; 
  compact = compact_cone ;
  pp_prf  = pp_psatz pp_q ;
  pp_f   = fun o x -> pp_pol pp_q o  (fst x)
}

let linear_prover_R = {
  name    = "linear prover";
  prover  = lift_pexpr_prover (Certificate.linear_prover_with_cert Certificate.z_spec) ; 
  hyps    = hyps_of_cone ; 
  compact = compact_cone ;
  pp_prf  = pp_psatz pp_z ;
  pp_f    =  fun o x -> pp_pol pp_z o (fst x)
}

let non_linear_prover_Q str o = {
  name    = "real nonlinear prover";
  prover  = call_csdpcert_q (str, o);
  hyps    = hyps_of_cone;
  compact = compact_cone ;
  pp_prf  = pp_psatz pp_q ;
  pp_f    = fun o x -> pp_pol pp_q o  (fst x)
}

let non_linear_prover_R str o = {
  name    = "real nonlinear prover";
  prover  = call_csdpcert_z (str, o);
  hyps    = hyps_of_cone;
  compact = compact_cone;
  pp_prf  = pp_psatz pp_z;
  pp_f    = fun o x -> pp_pol pp_z o  (fst x)
}

let non_linear_prover_Z str o  = {
  name    = "real nonlinear prover";
  prover  = lift_ratproof (call_csdpcert_z (str, o));
  hyps    = hyps_of_pt;
  compact = compact_pt;
  pp_prf  = pp_proof_term;
  pp_f    =  fun o x -> pp_pol pp_z o (fst x)
}

module CacheZ = PHashtable(struct 
  type t = (Mc.z Mc.pol * Mc.op1) list
  let equal = (=)
  let hash  = Hashtbl.hash
end)

let memo_zlinear_prover = CacheZ.memo "lia.cache" (lift_pexpr_prover Certificate.zlinear_prover)


let linear_Z =   {
  name = "lia";
  prover = memo_zlinear_prover ; 
  hyps   = hyps_of_pt;
  compact = compact_pt;
  pp_prf      = pp_proof_term;
  pp_f    = fun o x -> pp_pol pp_z o (fst x)
}



(** Instantiation of the tactics *)

let psatzl_Z gl = 
 micromega_gen parse_zarith  Mc.negate Mc.normalise zz_domain_spec
  [linear_prover_Z ] gl


let psatzl_Q gl = 
 micromega_gen  parse_qarith Mc.qnegate Mc.qnormalise qq_domain_spec 
  [ linear_prover_Q ]   gl


let psatz_Q i gl = 
 micromega_gen parse_qarith Mc.qnegate Mc.qnormalise qq_domain_spec
  [ non_linear_prover_Q "real_nonlinear_prover" (Some i) ]  gl


let psatzl_R gl = 
 micromega_gen  parse_rarith Mc.rnegate Mc.rnormalise rz_domain_spec 
  [ linear_prover_R ]   gl

let psatz_R i gl = 
 micromega_gen parse_rarith Mc.rnegate Mc.rnormalise rz_domain_spec
  [ non_linear_prover_R "real_nonlinear_prover" (Some i)]  gl


let psatz_Z i gl = 
 micromega_gen parse_zarith Mc.negate Mc.normalise zz_domain_spec 
 [non_linear_prover_Z "real_nonlinear_prover" (Some i) ] gl


let sos_Z gl = 
 micromega_gen parse_zarith Mc.negate Mc.normalise  zz_domain_spec 
  [non_linear_prover_Z "pure_sos" None]  gl

let sos_Q gl = 
 micromega_gen parse_qarith Mc.qnegate Mc.qnormalise  qq_domain_spec 
  [non_linear_prover_Q "pure_sos" None]  gl


let sos_R gl = 
 micromega_gen parse_rarith Mc.rnegate Mc.rnormalise  rz_domain_spec 
  [non_linear_prover_R "pure_sos" None]  gl



let xlia gl = 
 micromega_gen parse_zarith Mc.negate Mc.normalise   zz_domain_spec 
  [linear_Z] gl

(* Local Variables: *)
(* coding: utf-8 *)
(* End: *)
