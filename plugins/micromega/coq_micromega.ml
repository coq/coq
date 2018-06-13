(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(*                                                                      *)
(* Micromega: A reflexive tactic using the Positivstellensatz           *)
(*                                                                      *)
(* ** Toplevel definition of tactics **                                 *)
(*                                                                      *)
(* - Modules ISet, M, Mc, Env, Cache, CacheZ                            *)
(*                                                                      *)
(*  Frédéric Besson (Irisa/Inria) 2006-20011                            *)
(*                                                                      *)
(************************************************************************)

open Pp
open Names
open Goptions
open Mutils
open Constr
open Tactypes

(**
  * Debug flag 
  *)

let debug = false

(* Limit the proof search *)

let max_depth = max_int

(* Search limit for provers over Q R *)
let lra_proof_depth = ref max_depth

 
(* Search limit for provers over Z *)
let lia_enum  = ref true
let lia_proof_depth = ref max_depth

let get_lia_option () =
 (!lia_enum,!lia_proof_depth)

let get_lra_option () =
 !lra_proof_depth


 
let _ =
 
 let int_opt l vref =
  {
   optdepr = false;
   optname = List.fold_right (^) l "";
   optkey  = l ;
   optread = (fun () -> Some !vref);
   optwrite = (fun x -> vref := (match x with None -> max_depth | Some v -> v))
  } in

 let lia_enum_opt = 
  {
   optdepr = false;
   optname = "Lia Enum";
   optkey  = ["Lia";"Enum"];
   optread = (fun () -> !lia_enum);
   optwrite = (fun x -> lia_enum := x)
  } in
 let _ = declare_int_option (int_opt ["Lra"; "Depth"] lra_proof_depth) in
 let _ = declare_int_option (int_opt ["Lia"; "Depth"] lia_proof_depth) in 
 let _ = declare_bool_option lia_enum_opt in
 ()
 
(**
  * Initialize a tag type to the Tag module declaration (see Mutils).
  *)

type tag = Tag.t

(**
  * An atom is of the form:
  *   pExpr1 \{<,>,=,<>,<=,>=\} pExpr2
  * where pExpr1, pExpr2 are polynomial expressions (see Micromega). pExprs are
  * parametrized by 'cst, which is used as the type of constants.
  *)

type 'cst atom = 'cst Micromega.formula

(**
  * Micromega's encoding of formulas.
  * By order of appearance: boolean constants, variables, atoms, conjunctions,
  * disjunctions, negation, implication.
*)

type 'cst formula =
  | TT
  | FF
  | X of EConstr.constr
  | A of 'cst atom * tag * EConstr.constr
  | C of 'cst formula * 'cst formula
  | D of 'cst formula * 'cst formula
  | N of 'cst formula
  | I of 'cst formula * Names.Id.t option * 'cst formula

(**
  * Formula pretty-printer.
  *)

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
	    | Some id -> Names.Id.to_string id
	    | None -> "") pp_formula f2
    | N(f) -> Printf.fprintf o "N(%a)" pp_formula f


let rec map_atoms fct f = 
  match f with
    | TT -> TT
    | FF -> FF
    | X x -> X x
    | A (at,tg,cstr) -> A(fct at,tg,cstr)
    | C (f1,f2) -> C(map_atoms fct f1, map_atoms fct f2)
    | D (f1,f2) -> D(map_atoms fct f1, map_atoms fct f2)
    | N f -> N(map_atoms fct f)
    | I(f1,o,f2) -> I(map_atoms fct f1, o , map_atoms fct f2)

let rec map_prop fct f =
  match f with
    | TT -> TT
    | FF -> FF
    | X x -> X (fct x)
    | A (at,tg,cstr) -> A(at,tg,cstr)
    | C (f1,f2) -> C(map_prop fct f1, map_prop fct f2)
    | D (f1,f2) -> D(map_prop fct f1, map_prop fct f2)
    | N f -> N(map_prop fct f)
    | I(f1,o,f2) -> I(map_prop fct f1, o , map_prop fct f2)

(**
  * Collect the identifiers of a (string of) implications. Implication labels
  * are inherited from Coq/CoC's higher order dependent type constructor (Pi).
  *)

let rec ids_of_formula f =
  match f with
    | I(f1,Some id,f2) -> id::(ids_of_formula f2)
    | _                -> []

(**
  * A clause is a list of (tagged) nFormulas.
  * nFormulas are normalized formulas, i.e., of the form:
  *   cPol \{=,<>,>,>=\} 0
  * with cPol compact polynomials (see the Pol inductive type in EnvRing.v).
  *)

type 'cst clause = ('cst Micromega.nFormula * tag) list

(**
  * A CNF is a list of clauses.
  *)

type 'cst cnf = ('cst clause) list

(**
  * True and False are empty cnfs and clauses.
  *)

let tt : 'cst cnf = []

let ff : 'cst cnf = [ [] ]

(**
  * A refinement of cnf with tags left out. This is an intermediary form
  * between the cnf tagged list representation ('cst cnf) used to solve psatz,
  * and the freeform formulas ('cst formula) that is retrieved from Coq.
  *)

module Mc = Micromega

type 'cst mc_cnf = ('cst Mc.nFormula) list list

(**
  * From a freeform formula, build a cnf.
  * The parametric functions negate and normalize are theory-dependent, and
  * originate in micromega.ml (extracted, e.g. for rnegate, from RMicromega.v
  * and RingMicromega.v).
  *)

type 'a tagged_option = T of tag list |  S of 'a 

let cnf 
    (negate: 'cst atom -> 'cst mc_cnf) (normalise:'cst atom -> 'cst mc_cnf) 
    (unsat : 'cst Mc.nFormula -> bool) (deduce : 'cst Mc.nFormula -> 'cst Mc.nFormula -> 'cst Mc.nFormula option) (f:'cst formula) =

 let negate a t =
  List.map (fun cl -> List.map (fun x -> (x,t)) cl) (negate a) in

 let normalise a t =
  List.map (fun cl -> List.map (fun x -> (x,t)) cl) (normalise a) in

 let and_cnf x y = x @ y in

let rec add_term  t0 = function
  | [] -> 
      (match deduce (fst t0) (fst t0) with
	| Some u -> if unsat u then T [snd t0] else S (t0::[])
	| None -> S (t0::[]))
  | t'::cl0 ->
      (match deduce (fst t0) (fst t') with
	 | Some u ->
	     if unsat u
	     then T [snd t0 ; snd t']
	     else (match add_term  t0 cl0 with
		     | S cl' -> S (t'::cl')
		     | T l -> T l)
	 | None ->
	     (match add_term  t0 cl0 with
		| S cl' -> S (t'::cl')
		| T l -> T l)) in


 let rec or_clause  cl1 cl2 =
   match cl1 with
     | [] -> S cl2
     | t0::cl ->
	 (match add_term  t0 cl2 with
	    | S cl' -> or_clause  cl cl'
	    | T l -> T l) in



 let or_clause_cnf t f =  
   List.fold_right (fun e (acc,tg) -> 
		      match or_clause t e with
			| S cl -> (cl :: acc,tg)
			| T l -> (acc,tg@l)) f ([],[]) in


 let rec or_cnf f f' =
  match f with
   | [] -> tt,[]
   | e :: rst -> 
       let (rst_f',t) = or_cnf rst f' in
       let (e_f', t') = or_clause_cnf e f' in
	 (rst_f' @ e_f', t @ t') in


 let rec xcnf (polarity : bool) f =
  match f with
   | TT -> if polarity then (tt,[]) else (ff,[])
   | FF  -> if polarity then (ff,[]) else (tt,[])
   | X p -> if polarity then (ff,[]) else (ff,[])
   | A(x,t,_) -> ((if polarity then normalise x t else negate x t),[])
   | N(e)  -> xcnf (not polarity) e
   | C(e1,e2) -> 
       let e1,t1 = xcnf polarity e1 in
       let e2,t2 = xcnf polarity e2 in
      if polarity 
       then and_cnf e1 e2, t1 @ t2
       else let f',t' = or_cnf e1 e2 in
	 (f', t1 @ t2 @ t')
   | D(e1,e2)  ->
       let e1,t1 = xcnf polarity e1 in
       let e2,t2 = xcnf polarity e2 in
      if polarity 
       then let f',t' = or_cnf e1 e2 in
	 (f', t1 @ t2 @ t')
       else and_cnf e1 e2, t1 @ t2
   | I(e1,_,e2) ->
       let e1 , t1 = (xcnf (not polarity) e1) in
       let e2 , t2 = (xcnf polarity e2) in
      if polarity 
       then let f',t' = or_cnf e1 e2 in
	 (f', t1 @ t2 @ t')
       else and_cnf e1 e2, t1 @ t2 in

  xcnf true f

(**
  * MODULE: Ordered set of integers.
  *)

module ISet = Set.Make(Int)

(**
  * Given a set of integers s=\{i0,...,iN\} and a list m, return the list of
  * elements of m that are at position i0,...,iN.
  *)

let selecti s m =
  let rec xselecti i m =
    match m with
      | [] -> []
      | e::m -> if ISet.mem i s then e::(xselecti (i+1) m) else xselecti (i+1) m in
    xselecti 0 m

(**
  * MODULE: Mapping of the Coq data-strustures into Caml and Caml extracted
  * code. This includes initializing Caml variables based on Coq terms, parsing
  * various Coq expressions into Caml, and dumping Caml expressions into Coq.
  *
  * Opened here and in csdpcert.ml.
  *)

module M =
struct

  (**
    * Location of the Coq libraries.
    *)

  let logic_dir = ["Coq";"Logic";"Decidable"]

  let mic_modules = 
    [ 
      ["Coq";"Lists";"List"];
      ["ZMicromega"];
      ["Tauto"];
      ["RingMicromega"];
      ["EnvRing"];
      ["Coq"; "micromega"; "ZMicromega"];
      ["Coq"; "micromega"; "RMicromega"];
      ["Coq" ; "micromega" ; "Tauto"];
      ["Coq" ; "micromega" ; "RingMicromega"];
      ["Coq" ; "micromega" ; "EnvRing"];
      ["Coq";"QArith"; "QArith_base"];
      ["Coq";"Reals" ; "Rdefinitions"];
      ["Coq";"Reals" ; "Rpow_def"];
      ["LRing_normalise"]]

  let coq_modules =
   Coqlib.(init_modules @
    [logic_dir] @ arith_modules @ zarith_base_modules @ mic_modules)

  let bin_module = [["Coq";"Numbers";"BinNums"]]

  let r_modules =
    [["Coq";"Reals" ; "Rdefinitions"];
     ["Coq";"Reals" ; "Rpow_def"] ;
     ["Coq";"Reals" ; "Raxioms"] ;
     ["Coq";"QArith"; "Qreals"] ;
    ]

  let z_modules = [["Coq";"ZArith";"BinInt"]]

  (**
    * Initialization : a large amount of Caml symbols are derived from
    * ZMicromega.v
    *)

  let gen_constant_in_modules s m n = EConstr.of_constr (UnivGen.constr_of_global @@ Coqlib.gen_reference_in_modules s m n)
  let init_constant = gen_constant_in_modules "ZMicromega" Coqlib.init_modules
  let constant = gen_constant_in_modules "ZMicromega" coq_modules
  let bin_constant = gen_constant_in_modules "ZMicromega" bin_module
  let r_constant = gen_constant_in_modules "ZMicromega" r_modules
  let z_constant = gen_constant_in_modules "ZMicromega" z_modules
  let m_constant = gen_constant_in_modules "ZMicromega" mic_modules

  let coq_and = lazy (init_constant "and")
  let coq_or = lazy (init_constant "or")
  let coq_not = lazy (init_constant "not")

  let coq_iff = lazy (init_constant "iff")
  let coq_True = lazy (init_constant "True")
  let coq_False = lazy (init_constant "False")

  let coq_cons = lazy (constant "cons")
  let coq_nil = lazy (constant "nil")
  let coq_list = lazy (constant "list")

  let coq_O = lazy (init_constant "O")
  let coq_S = lazy (init_constant "S")

  let coq_N0 = lazy (bin_constant "N0")
  let coq_Npos = lazy (bin_constant "Npos")

  let coq_xH = lazy (bin_constant "xH")
  let coq_xO = lazy (bin_constant "xO")
  let coq_xI = lazy (bin_constant "xI")

  let coq_Z = lazy (bin_constant "Z")
  let coq_ZERO = lazy (bin_constant "Z0")
  let coq_POS = lazy (bin_constant "Zpos")
  let coq_NEG = lazy (bin_constant "Zneg")

  let coq_Q = lazy (constant "Q")
  let coq_R = lazy (constant "R")

  let coq_Qmake = lazy (constant "Qmake")

  let coq_Rcst = lazy (constant "Rcst")

  let coq_C0   = lazy (m_constant "C0")
  let coq_C1   = lazy (m_constant "C1")
  let coq_CQ   = lazy (m_constant "CQ")
  let coq_CZ   = lazy (m_constant "CZ")
  let coq_CPlus = lazy (m_constant "CPlus")
  let coq_CMinus = lazy (m_constant "CMinus")
  let coq_CMult  = lazy (m_constant "CMult")
  let coq_CInv   = lazy (m_constant "CInv")
  let coq_COpp   = lazy (m_constant "COpp")


  let coq_R0    = lazy (constant "R0")
  let coq_R1    = lazy (constant "R1")

  let coq_proofTerm = lazy (constant "ZArithProof")
  let coq_doneProof = lazy (constant "DoneProof")
  let coq_ratProof = lazy (constant "RatProof")
  let coq_cutProof = lazy (constant "CutProof")
  let coq_enumProof = lazy (constant "EnumProof")

  let coq_Zgt = lazy (z_constant "Z.gt")
  let coq_Zge = lazy (z_constant "Z.ge")
  let coq_Zle = lazy (z_constant "Z.le")
  let coq_Zlt = lazy (z_constant "Z.lt")
  let coq_Eq  = lazy (init_constant "eq")

  let coq_Zplus = lazy (z_constant "Z.add")
  let coq_Zminus = lazy (z_constant "Z.sub")
  let coq_Zopp = lazy (z_constant "Z.opp")
  let coq_Zmult = lazy (z_constant "Z.mul")
  let coq_Zpower = lazy (z_constant "Z.pow")

  let coq_Qle = lazy (constant "Qle")
  let coq_Qlt = lazy (constant "Qlt")
  let coq_Qeq = lazy (constant "Qeq")

  let coq_Qplus = lazy (constant "Qplus")
  let coq_Qminus = lazy (constant "Qminus")
  let coq_Qopp = lazy (constant "Qopp")
  let coq_Qmult = lazy (constant "Qmult")
  let coq_Qpower = lazy (constant "Qpower")

  let coq_Rgt = lazy (r_constant "Rgt")
  let coq_Rge = lazy (r_constant "Rge")
  let coq_Rle = lazy (r_constant "Rle")
  let coq_Rlt = lazy (r_constant "Rlt")

  let coq_Rplus = lazy (r_constant "Rplus")
  let coq_Rminus = lazy (r_constant "Rminus")
  let coq_Ropp = lazy (r_constant "Ropp")
  let coq_Rmult = lazy (r_constant "Rmult")
  let coq_Rinv = lazy (r_constant "Rinv")
  let coq_Rpower = lazy (r_constant "pow")
  let coq_IZR    = lazy (r_constant "IZR")
  let coq_IQR    = lazy (r_constant "Q2R")


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

  (**
    * Initialization : a few Caml symbols are derived from other libraries;
    * QMicromega, ZArithRing, RingMicromega.
    *)

  let coq_QWitness = lazy
   (gen_constant_in_modules "QMicromega"
     [["Coq"; "micromega"; "QMicromega"]] "QWitness")

  let coq_Build = lazy
   (gen_constant_in_modules "RingMicromega"
     [["Coq" ; "micromega" ; "RingMicromega"] ; ["RingMicromega"] ]
     "Build_Formula")
  let coq_Cstr = lazy
   (gen_constant_in_modules "RingMicromega"
     [["Coq" ; "micromega" ; "RingMicromega"] ; ["RingMicromega"] ] "Formula")

  (**
    * Parsing and dumping : transformation functions between Caml and Coq
    * data-structures.
    *
    * dump_*    functions go from Micromega to Coq terms
    * parse_*   functions go from Coq to Micromega terms
    * pp_*      functions pretty-print Coq terms.
    *)

  exception ParseError

  (* A simple but useful getter function *)

  let get_left_construct sigma term =
   match EConstr.kind sigma term with
    | Construct((_,i),_) -> (i,[| |])
    | App(l,rst) ->
       (match EConstr.kind sigma l with
        | Construct((_,i),_) -> (i,rst)
        |   _     -> raise ParseError
       )
    | _ ->   raise ParseError

  (* Access the Micromega module *)
  
  (* parse/dump/print from numbers up to expressions and formulas *)

  let rec parse_nat sigma term =
   let (i,c) = get_left_construct sigma term in
    match i with
     | 1 -> Mc.O
     | 2 -> Mc.S (parse_nat sigma (c.(0)))
     | i -> raise ParseError

  let pp_nat o n = Printf.fprintf o "%i" (CoqToCaml.nat n)

  let rec dump_nat x =
   match x with
    | Mc.O -> Lazy.force coq_O
    | Mc.S p -> EConstr.mkApp(Lazy.force coq_S,[| dump_nat p |])

  let rec parse_positive sigma term =
   let (i,c) = get_left_construct sigma term in
    match i with
     | 1 -> Mc.XI (parse_positive sigma c.(0))
     | 2 -> Mc.XO (parse_positive sigma c.(0))
     | 3 -> Mc.XH
     | i -> raise ParseError

  let rec dump_positive x =
   match x with
    | Mc.XH -> Lazy.force coq_xH
    | Mc.XO p -> EConstr.mkApp(Lazy.force coq_xO,[| dump_positive p |])
    | Mc.XI p -> EConstr.mkApp(Lazy.force coq_xI,[| dump_positive p |])

  let pp_positive o x = Printf.fprintf o "%i" (CoqToCaml.positive x)

  let dump_n x =
   match x with
    | Mc.N0 -> Lazy.force coq_N0
    | Mc.Npos p -> EConstr.mkApp(Lazy.force coq_Npos,[| dump_positive p|])

  let parse_z sigma term =
   let (i,c) = get_left_construct sigma term in
    match i with
     | 1 -> Mc.Z0
     | 2 -> Mc.Zpos (parse_positive sigma c.(0))
     | 3 -> Mc.Zneg (parse_positive sigma c.(0))
     | i -> raise ParseError

  let dump_z x =
   match x with
    | Mc.Z0 ->Lazy.force coq_ZERO
    | Mc.Zpos p -> EConstr.mkApp(Lazy.force coq_POS,[| dump_positive p|])
    | Mc.Zneg p -> EConstr.mkApp(Lazy.force coq_NEG,[| dump_positive p|])

  let pp_z o x = Printf.fprintf o "%s" (Big_int.string_of_big_int (CoqToCaml.z_big_int x))

  let dump_q q =
   EConstr.mkApp(Lazy.force coq_Qmake,
                 [| dump_z q.Micromega.qnum ; dump_positive q.Micromega.qden|])

  let parse_q sigma term =
     match EConstr.kind sigma term with
       | App(c, args) -> if EConstr.eq_constr sigma c (Lazy.force coq_Qmake) then
             {Mc.qnum = parse_z sigma args.(0) ; Mc.qden = parse_positive sigma args.(1) }
       else raise ParseError
   |  _ -> raise ParseError


  let rec pp_Rcst o cst = 
    match cst with
      | Mc.C0 -> output_string o "C0"
      | Mc.C1 ->  output_string o "C1"
      | Mc.CQ q ->  output_string o "CQ _"
      | Mc.CZ z -> pp_z o z
      | Mc.CPlus(x,y) -> Printf.fprintf o "(%a + %a)" pp_Rcst x pp_Rcst y
      | Mc.CMinus(x,y) -> Printf.fprintf o "(%a - %a)" pp_Rcst x pp_Rcst y
      | Mc.CMult(x,y) -> Printf.fprintf o "(%a * %a)" pp_Rcst x pp_Rcst y
      | Mc.CInv t -> Printf.fprintf o "(/ %a)" pp_Rcst t
      | Mc.COpp t -> Printf.fprintf o "(- %a)" pp_Rcst t


  let rec dump_Rcst cst = 
    match cst with
      | Mc.C0 -> Lazy.force coq_C0 
      | Mc.C1 ->  Lazy.force coq_C1
      | Mc.CQ q ->  EConstr.mkApp(Lazy.force coq_CQ, [| dump_q q |])
      | Mc.CZ z -> EConstr.mkApp(Lazy.force coq_CZ, [| dump_z z |])
      | Mc.CPlus(x,y) -> EConstr.mkApp(Lazy.force coq_CPlus, [| dump_Rcst x ; dump_Rcst y |])
      | Mc.CMinus(x,y) -> EConstr.mkApp(Lazy.force coq_CMinus, [| dump_Rcst x ; dump_Rcst y |])
      | Mc.CMult(x,y) -> EConstr.mkApp(Lazy.force coq_CMult, [| dump_Rcst x ; dump_Rcst y |])
      | Mc.CInv t -> EConstr.mkApp(Lazy.force coq_CInv, [| dump_Rcst t |])
      | Mc.COpp t -> EConstr.mkApp(Lazy.force coq_COpp, [| dump_Rcst t |])

  let rec dump_list typ dump_elt l =
   match l with
    | [] -> EConstr.mkApp(Lazy.force coq_nil,[| typ |])
    | e :: l -> EConstr.mkApp(Lazy.force coq_cons,
                                [| typ; dump_elt e;dump_list typ dump_elt l|])

  let pp_list op cl elt o l =
   let rec _pp  o l =
    match l with
     | [] -> ()
     | [e] -> Printf.fprintf o "%a" elt e
     | e::l -> Printf.fprintf o "%a ,%a" elt e  _pp l in
    Printf.fprintf o "%s%a%s" op _pp l cl

  let dump_var = dump_positive

  let dump_expr typ dump_z e =
   let rec dump_expr  e =
   match e with
    | Mc.PEX n -> EConstr.mkApp(Lazy.force coq_PEX,[| typ; dump_var n |])
    | Mc.PEc z -> EConstr.mkApp(Lazy.force coq_PEc,[| typ ; dump_z z |])
    | Mc.PEadd(e1,e2) -> EConstr.mkApp(Lazy.force coq_PEadd,
                                       [| typ; dump_expr e1;dump_expr e2|])
    | Mc.PEsub(e1,e2) -> EConstr.mkApp(Lazy.force coq_PEsub,
                                       [| typ; dump_expr  e1;dump_expr  e2|])
    | Mc.PEopp e -> EConstr.mkApp(Lazy.force coq_PEopp,
                                  [| typ; dump_expr  e|])
    | Mc.PEmul(e1,e2) ->  EConstr.mkApp(Lazy.force coq_PEmul,
                                        [| typ; dump_expr  e1;dump_expr e2|])
    | Mc.PEpow(e,n) ->  EConstr.mkApp(Lazy.force coq_PEpow,
                                      [| typ; dump_expr  e; dump_n  n|])
      in
    dump_expr e

  let dump_pol typ dump_c e =
    let rec dump_pol e =
      match e with
        | Mc.Pc n -> EConstr.mkApp(Lazy.force coq_Pc, [|typ ; dump_c n|])
        | Mc.Pinj(p,pol) -> EConstr.mkApp(Lazy.force coq_Pinj , [| typ ; dump_positive p ; dump_pol pol|])
        | Mc.PX(pol1,p,pol2) -> EConstr.mkApp(Lazy.force coq_PX, [| typ ; dump_pol pol1 ; dump_positive p ; dump_pol pol2|]) in
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
    | Mc.PsatzIn n -> EConstr.mkApp(Lazy.force coq_PsatzIn,[| z; dump_nat n |])
    | Mc.PsatzMulC(e,c) -> EConstr.mkApp(Lazy.force coq_PsatzMultC,
                                         [| z; dump_pol z dump_z e ; dump_cone c |])
    | Mc.PsatzSquare e -> EConstr.mkApp(Lazy.force coq_PsatzSquare,
                                        [| z;dump_pol z dump_z e|])
    | Mc.PsatzAdd(e1,e2) -> EConstr.mkApp(Lazy.force coq_PsatzAdd,
                                          [| z; dump_cone e1; dump_cone e2|])
    | Mc.PsatzMulE(e1,e2) -> EConstr.mkApp(Lazy.force coq_PsatzMulE,
                                           [| z; dump_cone e1; dump_cone e2|])
    | Mc.PsatzC p -> EConstr.mkApp(Lazy.force coq_PsatzC,[| z; dump_z p|])
    | Mc.PsatzZ    -> EConstr.mkApp(Lazy.force coq_PsatzZ,[| z|]) in
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

  let dump_op = function
   | Mc.OpEq-> Lazy.force coq_OpEq
   | Mc.OpNEq-> Lazy.force coq_OpNEq
   | Mc.OpLe -> Lazy.force coq_OpLe
   | Mc.OpGe -> Lazy.force coq_OpGe
   | Mc.OpGt-> Lazy.force coq_OpGt
   | Mc.OpLt-> Lazy.force coq_OpLt

  let dump_cstr typ dump_constant {Mc.flhs = e1 ; Mc.fop = o ; Mc.frhs = e2} =
    EConstr.mkApp(Lazy.force coq_Build,
                  [| typ; dump_expr typ dump_constant e1 ;
                     dump_op o ;
                     dump_expr typ dump_constant e2|])

  let assoc_const sigma x l =
   try
   snd (List.find (fun (x',y) -> EConstr.eq_constr sigma x (Lazy.force x')) l)
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

  type gl = { env : Environ.env; sigma : Evd.evar_map }

  let is_convertible gl t1 t2 = 
   Reductionops.is_conv gl.env gl.sigma t1 t2

  let parse_zop gl (op,args) =
    let sigma = gl.sigma in
    match EConstr.kind sigma op with
    | Const (x,_) -> (assoc_const sigma op zop_table, args.(0) , args.(1))
    | Ind((n,0),_) ->
        if EConstr.eq_constr sigma op (Lazy.force coq_Eq) && is_convertible gl args.(0) (Lazy.force coq_Z)
        then (Mc.OpEq, args.(1), args.(2))
        else raise ParseError
    |   _ -> failwith "parse_zop"

  let parse_rop gl (op,args) =
    let sigma = gl.sigma in
    match EConstr.kind sigma op with
     | Const (x,_) -> (assoc_const sigma op rop_table, args.(0) , args.(1))
     | Ind((n,0),_) ->
        if EConstr.eq_constr sigma op (Lazy.force coq_Eq) && is_convertible gl args.(0) (Lazy.force coq_R)
        then (Mc.OpEq, args.(1), args.(2))
        else raise ParseError
    |   _ -> failwith "parse_zop"

  let parse_qop gl (op,args) =
    (assoc_const gl.sigma op qop_table, args.(0) , args.(1))

  type 'a op =
    | Binop of ('a Mc.pExpr -> 'a Mc.pExpr -> 'a Mc.pExpr)
    | Opp
    | Power
    | Ukn of string

  let assoc_ops sigma x l =
   try
     snd (List.find (fun (x',y) -> EConstr.eq_constr sigma x (Lazy.force x')) l)
   with
     Not_found -> Ukn "Oups"

  (**
    * MODULE: Env is for environment.
    *)

  module Env =
  struct
   let compute_rank_add env sigma v =
    let rec _add env n v =
     match env with
      | [] -> ([v],n)
      | e::l ->
         if EConstr.eq_constr sigma e v
         then (env,n)
         else
          let (env,n) = _add l ( n+1) v in
           (e::env,n) in
    let (env, n) =  _add env 1 v in
     (env, CamlToCoq.positive n)

   let get_rank env sigma v = 

     let rec _get_rank env n =
       match env with
       | [] -> raise (Invalid_argument "get_rank")
      | e::l ->
         if EConstr.eq_constr sigma e v
         then n
         else  _get_rank l (n+1)  in 
     _get_rank env 1

       
   let empty = []

   let elements env = env

  end (* MODULE END: Env *)

  (**
    * This is the big generic function for expression parsers.
    *)

  let parse_expr sigma parse_constant parse_exp ops_spec env term =
    if debug
    then (
      let _, env = Pfedit.get_current_context () in
      Feedback.msg_debug (Pp.str "parse_expr: " ++ Printer.pr_leconstr_env env sigma term));

(*
    let constant_or_variable env term =
     try
      ( Mc.PEc (parse_constant term) , env)
     with ParseError ->
      let (env,n) = Env.compute_rank_add env term in
       (Mc.PEX  n , env) in
*)
    let parse_variable env term =
      let (env,n) = Env.compute_rank_add env sigma term in
	(Mc.PEX  n , env) in

    let rec parse_expr env term =
     let combine env op (t1,t2) =
      let (expr1,env) = parse_expr env t1 in
      let (expr2,env) = parse_expr env t2 in
      (op expr1 expr2,env) in

       try (Mc.PEc (parse_constant term) , env)
       with ParseError -> 
	 match EConstr.kind sigma term with
           | App(t,args) ->
               (
		 match EConstr.kind sigma t with
                   | Const c ->
		       ( match assoc_ops sigma t ops_spec  with
			   | Binop f -> combine env f (args.(0),args.(1))
                   | Opp     -> let (expr,env) = parse_expr env args.(0) in
                       (Mc.PEopp expr, env)
                   | Power   ->
                       begin
			 try
                           let (expr,env) = parse_expr env args.(0) in
                           let power = (parse_exp expr args.(1)) in
                             (power  , env)
			 with e when CErrors.noncritical e ->
                           (* if the exponent is a variable *)
                           let (env,n) = Env.compute_rank_add env sigma term in (Mc.PEX n, env)
                       end
                   | Ukn  s ->
                       if debug
                       then (Printf.printf "unknown op: %s\n" s; flush stdout;);
                       let (env,n) = Env.compute_rank_add env sigma term in (Mc.PEX n, env)
               )
		   |   _ -> parse_variable env term
               )
	   | _ -> parse_variable env term in
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


  let rconst_assoc = 
    [ 
      coq_Rplus , (fun x y -> Mc.CPlus(x,y)) ;
      coq_Rminus , (fun x y -> Mc.CMinus(x,y)) ; 
      coq_Rmult  , (fun x y -> Mc.CMult(x,y)) ; 
    (*      coq_Rdiv   , (fun x y -> Mc.CMult(x,Mc.CInv y)) ;*)
    ]

  let rec rconstant sigma term =
   match EConstr.kind sigma term with
    | Const x ->
        if EConstr.eq_constr sigma term (Lazy.force coq_R0)
        then Mc.C0
        else if EConstr.eq_constr sigma term (Lazy.force coq_R1)
        then Mc.C1
        else raise ParseError
    | App(op,args) ->
	begin
	  try
            (* the evaluation order is important in the following *)
            let f = assoc_const sigma op rconst_assoc in
            let a = rconstant sigma args.(0) in
            let b = rconstant sigma args.(1) in
            f a b
	  with
	      ParseError -> 
		match op with
		| op when EConstr.eq_constr sigma op (Lazy.force coq_Rinv) ->
                  let arg = rconstant sigma args.(0) in 
                  if Mc.qeq_bool (Mc.q_of_Rcst arg) {Mc.qnum = Mc.Z0 ; Mc.qden = Mc.XH}
                  then raise ParseError (* This is a division by zero -- no semantics *)
                  else Mc.CInv(arg) 
		| op when EConstr.eq_constr sigma op (Lazy.force coq_IQR)  -> Mc.CQ (parse_q sigma args.(0))
		| op when EConstr.eq_constr sigma op   (Lazy.force coq_IZR)  -> Mc.CZ (parse_z sigma args.(0))
		| _ ->  raise ParseError
	end

    |  _ -> raise ParseError


  let rconstant sigma term =
    let _, env = Pfedit.get_current_context () in
    if debug
    then Feedback.msg_debug (Pp.str "rconstant: " ++ Printer.pr_leconstr_env env sigma term ++ fnl ());
    let res = rconstant sigma term in
      if debug then 
	(Printf.printf "rconstant -> %a\n" pp_Rcst res ; flush stdout) ;
      res


  let parse_zexpr sigma =  parse_expr sigma
    (zconstant sigma)
    (fun expr x ->
      let exp = (parse_z sigma x) in
        match exp with
          | Mc.Zneg _ -> Mc.PEc Mc.Z0
          |   _     ->  Mc.PEpow(expr, Mc.Z.to_N exp))
    zop_spec

  let parse_qexpr sigma =  parse_expr sigma
   (qconstant sigma)
    (fun expr x ->
      let exp = parse_z sigma x in
        match exp with
          | Mc.Zneg _ ->
              begin
                match expr with
                | Mc.PEc q -> Mc.PEc (Mc.qpower q exp)
                |     _    -> print_string "parse_qexpr parse error" ; flush stdout ; raise ParseError
              end
          | _     ->  let exp = Mc.Z.to_N  exp in
                        Mc.PEpow(expr,exp))
   qop_spec

  let parse_rexpr sigma =  parse_expr sigma
   (rconstant sigma)
   (fun expr x ->
      let exp = Mc.N.of_nat (parse_nat sigma x) in
        Mc.PEpow(expr,exp))
   rop_spec

  let  parse_arith parse_op parse_expr env cstr gl =
    let sigma = gl.sigma in
    if debug
    then Feedback.msg_debug (Pp.str "parse_arith: " ++ Printer.pr_leconstr_env gl.env sigma cstr ++ fnl ());
    match EConstr.kind sigma cstr with
    | App(op,args) ->
       let (op,lhs,rhs) = parse_op gl (op,args) in
       let (e1,env) = parse_expr sigma env lhs in
       let (e2,env) = parse_expr sigma env rhs in
        ({Mc.flhs = e1; Mc.fop = op;Mc.frhs = e2},env)
    |  _ -> failwith "error : parse_arith(2)"

  let parse_zarith = parse_arith parse_zop parse_zexpr

  let parse_qarith = parse_arith parse_qop parse_qexpr

  let parse_rarith = parse_arith parse_rop parse_rexpr

  (* generic parsing of arithmetic expressions *)

  let mkC f1 f2 = C(f1,f2)
  let mkD f1 f2 = D(f1,f2)
  let mkIff f1 f2 = C(I(f1,None,f2),I(f2,None,f1))
  let mkI f1 f2 = I(f1,None,f2)

  let mkformula_binary g term f1 f2 =
    match f1 , f2 with
    |  X _  , X _ -> X(term)
    |   _         -> g f1 f2

  (**
    * This is the big generic function for formula parsers.
    *)
  
  let parse_formula gl parse_atom env tg term =
    let sigma = gl.sigma in

    let parse_atom env tg t =
      try
        let (at,env) = parse_atom env t gl in
        (A(at,tg,t), env,Tag.next tg)
      with e when CErrors.noncritical e -> (X(t),env,tg) in

    let is_prop term =
      let sort  = Retyping.get_sort_of gl.env gl.sigma term in 
     Sorts.is_prop sort in
     
    let rec xparse_formula env tg term =
      match EConstr.kind sigma term with
      | App(l,rst) ->
        (match rst with
        | [|a;b|] when EConstr.eq_constr sigma l (Lazy.force coq_and) ->
          let f,env,tg = xparse_formula env tg a in
          let g,env, tg = xparse_formula env tg b  in
          mkformula_binary mkC term f g,env,tg
        | [|a;b|] when EConstr.eq_constr sigma l (Lazy.force coq_or) ->
          let f,env,tg = xparse_formula env tg a in
          let g,env,tg  = xparse_formula env tg b in
          mkformula_binary mkD term f g,env,tg
        | [|a|] when EConstr.eq_constr sigma l (Lazy.force coq_not) ->
          let (f,env,tg) = xparse_formula env tg a in (N(f), env,tg)
        | [|a;b|] when EConstr.eq_constr sigma l (Lazy.force coq_iff) ->
          let f,env,tg = xparse_formula env tg a in
          let g,env,tg = xparse_formula env tg b in
          mkformula_binary mkIff term f g,env,tg
        | _ -> parse_atom env tg term)
      | Prod(typ,a,b) when EConstr.Vars.noccurn sigma 1 b ->
        let f,env,tg = xparse_formula env tg a in
        let g,env,tg = xparse_formula env tg b in
        mkformula_binary mkI term f g,env,tg
      | _ when EConstr.eq_constr sigma term (Lazy.force coq_True) -> (TT,env,tg)
      | _ when EConstr.eq_constr sigma term (Lazy.force coq_False) -> (FF,env,tg)
      | _ when is_prop term -> X(term),env,tg
      | _ -> raise ParseError
    in
    xparse_formula env tg  ((*Reductionops.whd_zeta*) term)

  let dump_formula typ dump_atom f =
   let rec xdump f =
    match f with
     | TT  -> EConstr.mkApp(Lazy.force coq_TT,[|typ|])
     | FF  -> EConstr.mkApp(Lazy.force coq_FF,[|typ|])
     | C(x,y) -> EConstr.mkApp(Lazy.force coq_And,[|typ ; xdump x ; xdump y|])
     | D(x,y) -> EConstr.mkApp(Lazy.force coq_Or,[|typ ; xdump x ; xdump y|])
     | I(x,_,y) -> EConstr.mkApp(Lazy.force coq_Impl,[|typ ; xdump x ; xdump y|])
     | N(x) -> EConstr.mkApp(Lazy.force coq_Neg,[|typ ; xdump x|])
     | A(x,_,_) -> EConstr.mkApp(Lazy.force coq_Atom,[|typ ; dump_atom x|])
     | X(t) -> EConstr.mkApp(Lazy.force coq_X,[|typ ; t|])  in
   xdump f


  let prop_env_of_formula sigma form =
    let rec doit env = function
      | TT | FF | A(_,_,_) -> env
      | X t -> fst (Env.compute_rank_add env sigma t)
      | C(f1,f2) | D(f1,f2) | I(f1,_,f2) -> 
        doit (doit env f1) f2
      | N f -> doit env f in
    
    doit [] form

  let var_env_of_formula form =

    let rec vars_of_expr  = function
      | Mc.PEX n -> ISet.singleton (CoqToCaml.positive n)
      | Mc.PEc z -> ISet.empty
      | Mc.PEadd(e1,e2) | Mc.PEmul(e1,e2) | Mc.PEsub(e1,e2) ->
        ISet.union (vars_of_expr e1) (vars_of_expr e2)
      | Mc.PEopp e | Mc.PEpow(e,_)-> vars_of_expr e
    in
    
    let vars_of_atom  {Mc.flhs ; Mc.fop; Mc.frhs} =
      ISet.union (vars_of_expr flhs) (vars_of_expr frhs) in
      
    let rec doit = function
      |  TT | FF | X _ -> ISet.empty
      | A (a,t,c) -> vars_of_atom a
      | C(f1,f2) | D(f1,f2) |I (f1,_,f2) -> ISet.union (doit f1) (doit f2)
      | N f -> doit f in

    doit  form
    


      
  type 'cst dump_expr =  (* 'cst is the type of the syntactic constants *)
    {
      interp_typ : EConstr.constr;
      dump_cst : 'cst -> EConstr.constr;
      dump_add : EConstr.constr;
      dump_sub : EConstr.constr;
      dump_opp : EConstr.constr;
      dump_mul : EConstr.constr;
      dump_pow : EConstr.constr;
      dump_pow_arg : Mc.n -> EConstr.constr;
      dump_op  : (Mc.op2 * EConstr.constr) list
    }

let dump_zexpr = lazy
  {
    interp_typ = Lazy.force coq_Z;
    dump_cst = dump_z;
    dump_add = Lazy.force coq_Zplus;
    dump_sub = Lazy.force coq_Zminus;
    dump_opp = Lazy.force coq_Zopp;
    dump_mul = Lazy.force coq_Zmult;
    dump_pow = Lazy.force coq_Zpower;
    dump_pow_arg = (fun n -> dump_z (CamlToCoq.z (CoqToCaml.n n)));
    dump_op  = List.map (fun (x,y) -> (y,Lazy.force x)) zop_table
  }

let dump_qexpr = lazy
  {
    interp_typ = Lazy.force coq_Q;
    dump_cst = dump_q;
    dump_add = Lazy.force coq_Qplus;
    dump_sub = Lazy.force coq_Qminus;
    dump_opp = Lazy.force coq_Qopp;
    dump_mul = Lazy.force coq_Qmult;
    dump_pow = Lazy.force coq_Qpower;
    dump_pow_arg = (fun n -> dump_z (CamlToCoq.z (CoqToCaml.n n)));
    dump_op  = List.map (fun (x,y) -> (y,Lazy.force x)) qop_table      
  }

let rec dump_Rcst_as_R cst = 
  match cst with
  | Mc.C0 -> Lazy.force coq_R0 
  | Mc.C1 ->  Lazy.force coq_R1
  | Mc.CQ q ->  EConstr.mkApp(Lazy.force coq_IQR, [| dump_q q |])
  | Mc.CZ z -> EConstr.mkApp(Lazy.force coq_IZR, [| dump_z z |])
  | Mc.CPlus(x,y) -> EConstr.mkApp(Lazy.force coq_Rplus, [| dump_Rcst_as_R x ; dump_Rcst_as_R y |])
  | Mc.CMinus(x,y) -> EConstr.mkApp(Lazy.force coq_Rminus, [| dump_Rcst_as_R x ; dump_Rcst_as_R y |])
  | Mc.CMult(x,y) -> EConstr.mkApp(Lazy.force coq_Rmult, [| dump_Rcst_as_R x ; dump_Rcst_as_R y |])
  | Mc.CInv t -> EConstr.mkApp(Lazy.force coq_Rinv, [| dump_Rcst_as_R t |])
  | Mc.COpp t -> EConstr.mkApp(Lazy.force coq_Ropp, [| dump_Rcst_as_R t |])


let dump_rexpr = lazy
  {
    interp_typ = Lazy.force coq_R;
    dump_cst = dump_Rcst_as_R;
    dump_add = Lazy.force coq_Rplus;
    dump_sub = Lazy.force coq_Rminus;
    dump_opp = Lazy.force coq_Ropp;
    dump_mul = Lazy.force coq_Rmult;
    dump_pow = Lazy.force coq_Rpower;
    dump_pow_arg = (fun n -> dump_nat (CamlToCoq.nat (CoqToCaml.n n)));
    dump_op  = List.map (fun (x,y) -> (y,Lazy.force x)) rop_table      
  }


    
    
(** [make_goal_of_formula depxr vars props form] where 
     - vars is an environment for the arithmetic variables occuring in form
     - props is an environment for the propositions occuring in form
    @return a goal where all the variables and propositions of the formula are quantified

*) 

let prodn n env b =
  let rec prodrec = function
    | (0, env, b)        -> b
    | (n, ((v,t)::l), b) -> prodrec (n-1,  l, EConstr.mkProd (v,t,b))
    | _ -> assert false
  in
  prodrec (n,env,b)

let make_goal_of_formula sigma dexpr form =

  let vars_idx =
    List.mapi (fun i v -> (v, i+1))  (ISet.elements (var_env_of_formula form)) in

  (*  List.iter (fun (v,i) -> Printf.fprintf stdout "var %i has index %i\n" v i) vars_idx ;*)
  
  let props     = prop_env_of_formula sigma form in 

  let vars_n  = List.map (fun (_,i) -> (Names.Id.of_string (Printf.sprintf "__x%i" i)) , dexpr.interp_typ) vars_idx in 
  let props_n = List.mapi (fun i _ -> (Names.Id.of_string (Printf.sprintf "__p%i" (i+1))) , EConstr.mkProp) props in 

  let var_name_pos = List.map2 (fun (idx,_) (id,_) -> id,idx) vars_idx vars_n in

  let  dump_expr i e =
    let rec dump_expr  = function
    | Mc.PEX n -> EConstr.mkRel (i+(List.assoc (CoqToCaml.positive n)  vars_idx))
    | Mc.PEc z -> dexpr.dump_cst z
    | Mc.PEadd(e1,e2) -> EConstr.mkApp(dexpr.dump_add,
                               [| dump_expr e1;dump_expr e2|])
    | Mc.PEsub(e1,e2) -> EConstr.mkApp(dexpr.dump_sub,
                               [| dump_expr  e1;dump_expr  e2|])
    | Mc.PEopp e -> EConstr.mkApp(dexpr.dump_opp,
                                  [| dump_expr  e|])
    | Mc.PEmul(e1,e2) -> EConstr.mkApp(dexpr.dump_mul,
                                       [| dump_expr  e1;dump_expr e2|])
    | Mc.PEpow(e,n) -> EConstr.mkApp(dexpr.dump_pow,
                                     [| dump_expr  e; dexpr.dump_pow_arg  n|])
    in dump_expr e in
  
  let mkop op e1 e2 =
      try
        EConstr.mkApp(List.assoc op dexpr.dump_op, [| e1; e2|])
      with Not_found ->
        EConstr.mkApp(Lazy.force coq_Eq,[|dexpr.interp_typ ; e1 ;e2|]) in
    
  let dump_cstr i { Mc.flhs ; Mc.fop ; Mc.frhs } =
    mkop fop (dump_expr i flhs) (dump_expr i frhs) in
  
  let rec xdump pi xi f =
    match f with
    | TT  -> Lazy.force coq_True
    | FF  -> Lazy.force coq_False
    | C(x,y) -> EConstr.mkApp(Lazy.force coq_and,[|xdump pi xi x ; xdump pi xi y|])
    | D(x,y) -> EConstr.mkApp(Lazy.force coq_or,[| xdump pi xi x ; xdump pi xi y|])
    | I(x,_,y) -> EConstr.mkArrow (xdump pi xi x) (xdump (pi+1) (xi+1) y)
    | N(x) -> EConstr.mkArrow (xdump pi xi x) (Lazy.force coq_False)
    | A(x,_,_) -> dump_cstr xi x
    | X(t) -> let idx = Env.get_rank props sigma t in
              EConstr.mkRel (pi+idx) in 
  
  let nb_vars  = List.length vars_n  in
  let nb_props = List.length props_n in 

  (*  Printf.fprintf stdout "NBProps : %i\n" nb_props ;*)
  
  let subst_prop p =
    let idx = Env.get_rank props sigma p in
    EConstr.mkVar (Names.Id.of_string (Printf.sprintf "__p%i"  idx)) in 

  let form' = map_prop subst_prop   form in

  (prodn nb_props (List.map (fun (x,y) -> Name.Name x,y) props_n)
     (prodn nb_vars (List.map (fun (x,y) -> Name.Name x,y) vars_n)
        (xdump (List.length vars_n) 0  form)),
   List.rev props_n, List.rev var_name_pos,form')
    
  (**
     * Given a conclusion and a list of affectations, rebuild a term prefixed by
     * the appropriate letins.
     * TODO: reverse the list of bindings!
  *)
    
  let set l concl =
   let rec xset acc = function
    | [] -> acc
    | (e::l) ->
       let (name,expr,typ) = e in
        xset (EConstr.mkNamedLetIn
               (Names.Id.of_string name)
               expr typ acc) l in
    xset concl l

end (**
      * MODULE END: M 
      *)

open M

let coq_Node = 
 lazy (gen_constant_in_modules "VarMap"
   [["Coq" ; "micromega" ; "VarMap"];["VarMap"]] "Node")
let coq_Leaf = 
 lazy (gen_constant_in_modules "VarMap"
   [["Coq" ; "micromega" ; "VarMap"];["VarMap"]] "Leaf")
let coq_Empty = 
 lazy (gen_constant_in_modules "VarMap"
   [["Coq" ; "micromega" ;"VarMap"];["VarMap"]] "Empty")

let coq_VarMap = 
  lazy (gen_constant_in_modules "VarMap"
     [["Coq" ; "micromega" ; "VarMap"] ; ["VarMap"]] "t")
 

let rec dump_varmap typ m =
  match m with
  | Mc.Empty -> EConstr.mkApp(Lazy.force coq_Empty,[| typ |])
  | Mc.Leaf v -> EConstr.mkApp(Lazy.force coq_Leaf,[| typ; v|])
  | Mc.Node(l,o,r) ->
    EConstr.mkApp (Lazy.force coq_Node, [| typ; dump_varmap typ l; o ; dump_varmap typ r |])


let vm_of_list env =
  match env with
  | [] -> Mc.Empty
  | (d,_)::_ -> 
    List.fold_left (fun vm (c,i) ->
      Mc.vm_add d (CamlToCoq.positive i) c vm) Mc.Empty env 

let rec dump_proof_term = function
  | Micromega.DoneProof -> Lazy.force coq_doneProof
  | Micromega.RatProof(cone,rst) ->
    EConstr.mkApp(Lazy.force coq_ratProof, [| dump_psatz coq_Z dump_z cone; dump_proof_term rst|])
 | Micromega.CutProof(cone,prf) ->
    EConstr.mkApp(Lazy.force coq_cutProof,
	      [| dump_psatz coq_Z dump_z cone ;
		 dump_proof_term prf|])
 | Micromega.EnumProof(c1,c2,prfs) ->
    EConstr.mkApp (Lazy.force coq_enumProof,
	           [|  dump_psatz coq_Z dump_z c1 ; dump_psatz coq_Z dump_z c2 ;
		       dump_list (Lazy.force coq_proofTerm) dump_proof_term prfs |])


let rec size_of_psatz = function
  | Micromega.PsatzIn _ -> 1
  | Micromega.PsatzSquare _ -> 1
  | Micromega.PsatzMulC(_,p) -> 1 + (size_of_psatz p)
  | Micromega.PsatzMulE(p1,p2) | Micromega.PsatzAdd(p1,p2) -> size_of_psatz p1 + size_of_psatz p2
  | Micromega.PsatzC _ -> 1
  | Micromega.PsatzZ   -> 1

let rec size_of_pf = function
  | Micromega.DoneProof -> 1
  | Micromega.RatProof(p,a) -> (size_of_pf a) + (size_of_psatz p)
  | Micromega.CutProof(p,a) -> (size_of_pf a) + (size_of_psatz p)
  | Micromega.EnumProof(p1,p2,l) -> (size_of_psatz p1) + (size_of_psatz p2) + (List.fold_left (fun acc p -> size_of_pf p + acc) 0 l)

let dump_proof_term t = 
  if debug then  Printf.printf "dump_proof_term %i\n" (size_of_pf t) ; 
  dump_proof_term t



let pp_q o q = Printf.fprintf o "%a/%a" pp_z q.Micromega.qnum pp_positive q.Micromega.qden


let rec pp_proof_term o = function
  | Micromega.DoneProof -> Printf.fprintf o "D"
  | Micromega.RatProof(cone,rst) -> Printf.fprintf o "R[%a,%a]" (pp_psatz  pp_z) cone pp_proof_term rst
  | Micromega.CutProof(cone,rst) -> Printf.fprintf o "C[%a,%a]" (pp_psatz  pp_z) cone pp_proof_term rst
  | Micromega.EnumProof(c1,c2,rst) ->
      Printf.fprintf o "EP[%a,%a,%a]"
	(pp_psatz pp_z) c1 (pp_psatz pp_z) c2
     (pp_list "[" "]" pp_proof_term) rst

let rec parse_hyps gl parse_arith env tg hyps =
 match hyps with
  | [] -> ([],env,tg)
  | (i,t)::l ->
     let (lhyps,env,tg) = parse_hyps gl parse_arith env tg l in
      try
       let (c,env,tg) = parse_formula gl parse_arith env  tg t in
	((i,c)::lhyps, env,tg)
      with e when CErrors.noncritical e -> (lhyps,env,tg)
       (*(if debug then Printf.printf "parse_arith : %s\n" x);*)


(*exception ParseError*)

let parse_goal gl parse_arith env hyps term =
 (*  try*)
 let (f,env,tg) = parse_formula gl parse_arith env (Tag.from 0) term in
 let (lhyps,env,tg) = parse_hyps gl parse_arith env tg hyps in
  (lhyps,f,env)
   (*  with Failure x -> raise ParseError*)

(**
  * The datastructures that aggregate theory-dependent proof values.
  *)
type ('synt_c, 'prf) domain_spec = {
  typ : EConstr.constr; (* is the type of the interpretation domain - Z, Q, R*)
  coeff : EConstr.constr ; (* is the type of the syntactic coeffs - Z , Q , Rcst *)
  dump_coeff : 'synt_c -> EConstr.constr ; 
  proof_typ  : EConstr.constr ; 
  dump_proof   : 'prf -> EConstr.constr
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

(** Naive topological sort of constr according to the subterm-ordering *)

(* An element is minimal x is minimal w.r.t y if 
   x <= y or (x and y are incomparable) *)

(**
  * Instanciate the current Coq goal with a Micromega formula, a varmap, and a
  * witness.
  *)

let micromega_order_change spec cert cert_typ env ff  (*: unit Proofview.tactic*) = 
 (* let ids = Util.List.map_i (fun i _ -> (Names.Id.of_string ("__v"^(string_of_int i)))) 0 env in *)
 let formula_typ = (EConstr.mkApp (Lazy.force coq_Cstr,[|spec.coeff|])) in
 let ff  = dump_formula formula_typ (dump_cstr spec.coeff spec.dump_coeff) ff in
 let vm = dump_varmap (spec.typ) (vm_of_list env) in
 (* todo : directly generate the proof term - or generalize before conversion? *)
  Proofview.Goal.nf_enter begin fun gl -> 
   Tacticals.New.tclTHENLIST
    [
     Tactics.change_concl
    (set
      [
       ("__ff", ff, EConstr.mkApp(Lazy.force coq_Formula, [|formula_typ |]));
       ("__varmap", vm, EConstr.mkApp(Lazy.force coq_VarMap, [|spec.typ|]));
       ("__wit", cert, cert_typ)
      ]
      (Tacmach.New.pf_concl gl))
  ] 
  end


(**
  * The datastructures that aggregate prover attributes.
  *)

type ('option,'a,'prf) prover = {
  name : string ; (* name of the prover *)
 get_option : unit ->'option ; (* find the options of the prover *)              
 prover : 'option * 'a list -> 'prf option ; (* the prover itself *)
  hyps : 'prf -> ISet.t ; (* extract the indexes of the hypotheses really used in the proof *)
  compact : 'prf -> (int -> int) -> 'prf ; (* remap the hyp indexes according to function *)
  pp_prf : out_channel -> 'prf -> unit ;(* pretting printing of proof *)
  pp_f   : out_channel -> 'a   -> unit (* pretty printing of the formulas (polynomials)*)
}


 
(**
  * Given a list of provers and a disjunction of atoms, find a proof of any of
  * the atoms.  Returns an (optional) pair of a proof and a prover
  * datastructure.
  *)

let find_witness provers polys1 =
  let provers = List.map (fun p ->
    (fun l ->
      match p.prover (p.get_option (),l) with
        | None -> None
        | Some prf -> Some(prf,p)) , p.name) provers in
  try_any provers (List.map fst polys1)

(**
  * Given a list of provers and a CNF, find a proof for each of the clauses.
  * Return the proofs as a list.
  *)

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

(**
  * Prune the proof object, according to the 'diff' between two cnf formulas.
  *)

let compact_proofs (cnf_ff: 'cst cnf) res (cnf_ff': 'cst cnf) =

  let compact_proof (old_cl:'cst clause) (prf,prover) (new_cl:'cst clause) =
    let new_cl = List.mapi (fun i (f,_) -> (f,i)) new_cl in
    let remap i =
      let formula = try fst (List.nth old_cl i) with Failure _ -> failwith "bad old index" in
      List.assoc formula new_cl in
(*    if debug then
      begin
        Printf.printf "\ncompact_proof : %a %a %a"
          (pp_ml_list prover.pp_f) (List.map fst old_cl)
          prover.pp_prf prf
          (pp_ml_list prover.pp_f) (List.map fst new_cl)   ;
          flush stdout
      end ; *)
    let res = try prover.compact prf remap with x when CErrors.noncritical x ->
      if debug then Printf.fprintf stdout "Proof compaction %s" (Printexc.to_string x) ;
      (* This should not happen -- this is the recovery plan... *)
      match prover.prover (prover.get_option () ,List.map fst new_cl) with
        | None -> failwith "proof compaction error"
        | Some p ->  p
    in
    if debug then
      begin
        Printf.printf " -> %a\n"
          prover.pp_prf res ;
        flush stdout
      end ;
    res in

  let is_proof_compatible (old_cl:'cst clause) (prf,prover) (new_cl:'cst clause) =
    let hyps_idx = prover.hyps prf in
    let hyps = selecti hyps_idx old_cl in
      is_sublist Pervasives.(=) hyps new_cl in

  let cnf_res = List.combine cnf_ff res in (* we get pairs clause * proof *)

  List.map (fun x ->
    let (o,p) = List.find (fun (l,p) -> is_proof_compatible l p x) cnf_res
    in compact_proof o p x) cnf_ff'


(**
  * "Hide out" tagged atoms of a formula by transforming them into generic
  * variables. See the Tag module in mutils.ml for more.
  *)

let abstract_formula hyps f =
  let rec xabs f =
    match f with
      | X c -> X c
      | A(a,t,term) -> if TagSet.mem t hyps then A(a,t,term) else X(term)
      | C(f1,f2) ->
	  (match xabs f1 , xabs f2 with
	    |   X a1    ,  X a2   -> X (EConstr.mkApp(Lazy.force coq_and, [|a1;a2|]))
	    |    f1     , f2      -> C(f1,f2) )
      | D(f1,f2) ->
	  (match xabs f1 , xabs f2 with
	    |   X a1    ,  X a2   -> X (EConstr.mkApp(Lazy.force coq_or, [|a1;a2|]))
	    |    f1     , f2      -> D(f1,f2) )
      | N(f) ->
	  (match xabs f with
	    |   X a    -> X (EConstr.mkApp(Lazy.force coq_not, [|a|]))
	    |     f     -> N f)
      | I(f1,hyp,f2) ->
	  (match xabs f1 , hyp, xabs f2 with
	    | X a1      , Some _ , af2    ->  af2
	    | X a1      , None   , X a2   -> X (EConstr.mkArrow a1 a2)
	    |   af1     ,  _     , af2    -> I(af1,hyp,af2)
	  )
      | FF -> FF
      | TT -> TT
  in  xabs f


(* [abstract_wrt_formula] is used in contexts whre f1 is already an abstraction of f2   *)
let rec abstract_wrt_formula f1 f2 = 
  match f1 , f2 with
    | X c  , _   -> X c
    | A _  , A _ -> f2
    | C(a,b) , C(a',b') -> C(abstract_wrt_formula a a', abstract_wrt_formula b b')
    | D(a,b) , D(a',b') -> D(abstract_wrt_formula a a', abstract_wrt_formula b b')
    | I(a,_,b) , I(a',x,b') -> I(abstract_wrt_formula a a',x, abstract_wrt_formula b b')
    | FF , FF -> FF
    | TT , TT -> TT
    | N x , N y -> N(abstract_wrt_formula x y)
    |    _    -> failwith "abstract_wrt_formula"

(**
  * This exception is raised by really_call_csdpcert if Coq's configure didn't
  * find a CSDP executable.
  *)

exception CsdpNotFound

  
(**
  * This is the core of Micromega: apply the prover, analyze the result and
  * prune unused fomulas, and finally modify the proof state.
  *)

let formula_hyps_concl hyps concl = 
  List.fold_right
   (fun (id,f) (cc,ids) ->
    match f with
      X _ -> (cc,ids)
     | _ -> (I(f,Some id,cc), id::ids))
    hyps (concl,[])


let micromega_tauto negate normalise unsat deduce spec prover env polys1 polys2 gl =

 (* Express the goal as one big implication *)
 let (ff,ids) = formula_hyps_concl polys1 polys2 in

 (* Convert the aplpication into a (mc_)cnf (a list of lists of formulas) *)
 let cnf_ff,cnf_ff_tags = cnf negate normalise unsat deduce ff in

 if debug then
   begin
     Feedback.msg_notice (Pp.str "Formula....\n") ;
     let formula_typ = (EConstr.mkApp(Lazy.force coq_Cstr, [|spec.coeff|])) in
     let ff = dump_formula formula_typ
       (dump_cstr spec.typ spec.dump_coeff) ff in
       Feedback.msg_notice (Printer.pr_leconstr_env gl.env gl.sigma ff);
       Printf.fprintf stdout "cnf : %a\n" (pp_cnf (fun o _ -> ())) cnf_ff
   end;

 match witness_list_tags prover cnf_ff with
  | None -> None
  | Some res -> (*Printf.printf "\nList %i" (List.length `res); *)
  let hyps = List.fold_left (fun s (cl,(prf,p)) ->
    let tags = ISet.fold (fun i s -> let t = snd (List.nth cl i) in
                                     if debug then (Printf.fprintf stdout "T : %i -> %a" i Tag.pp t) ;
      (*try*) TagSet.add t s (* with Invalid_argument _ -> s*)) (p.hyps prf) TagSet.empty in
    TagSet.union s tags) (List.fold_left (fun s i -> TagSet.add i s) TagSet.empty cnf_ff_tags) (List.combine cnf_ff res) in

  if debug then (Printf.printf "TForm : %a\n" pp_formula ff ; flush stdout;
                 Printf.printf "Hyps : %a\n" (fun o s -> TagSet.fold (fun i _ -> Printf.fprintf o "%a " Tag.pp i) s ()) hyps) ;

  let ff'     = abstract_formula hyps ff in
  let cnf_ff',_ = cnf negate normalise unsat deduce ff' in

  if debug then
    begin
      Feedback.msg_notice (Pp.str "\nAFormula\n") ;
      let formula_typ = (EConstr.mkApp( Lazy.force coq_Cstr,[| spec.coeff|])) in
      let ff' = dump_formula formula_typ
          (dump_cstr spec.typ spec.dump_coeff) ff' in
      Feedback.msg_notice (Printer.pr_leconstr_env gl.env gl.sigma ff');
      Printf.fprintf stdout "cnf : %a\n" (pp_cnf (fun o _ -> ())) cnf_ff'
    end;

  (* Even if it does not work, this does not mean it is not provable
  -- the prover is REALLY incomplete *)
  (* if debug then
      begin
        (* recompute the proofs *)
        match witness_list_tags prover  cnf_ff' with
          | None -> failwith "abstraction is wrong"
          | Some res -> ()
      end ; *)
  let res' = compact_proofs cnf_ff res cnf_ff' in

  let (ff',res',ids) = (ff',res', ids_of_formula ff') in

  let res' = dump_list (spec.proof_typ) spec.dump_proof res' in
    Some (ids,ff',res')


(**
  * Parse the proof environment, and call micromega_tauto
  *)

let fresh_id avoid id gl =
  Tactics.fresh_id_in_env avoid id (Proofview.Goal.env gl)

let micromega_gen
    parse_arith 
    (negate:'cst atom -> 'cst mc_cnf)
    (normalise:'cst atom -> 'cst mc_cnf)
    unsat deduce 
    spec dumpexpr prover tac =
 Proofview.Goal.nf_enter begin fun gl -> 
    let sigma = Tacmach.New.project gl in
    let concl = Tacmach.New.pf_concl gl in
    let hyps  = Tacmach.New.pf_hyps_types gl in
    try
     let gl0 = { env = Tacmach.New.pf_env gl; sigma } in
     let (hyps,concl,env) = parse_goal gl0 parse_arith Env.empty hyps concl in
     let env = Env.elements env in
     let spec = Lazy.force spec in
     let dumpexpr = Lazy.force dumpexpr in
     
     match micromega_tauto  negate normalise unsat deduce spec prover env hyps concl gl0 with
     | None -> Tacticals.New.tclFAIL 0 (Pp.str " Cannot find witness")
     | Some (ids,ff',res') -> 
       let (arith_goal,props,vars,ff_arith) = make_goal_of_formula sigma dumpexpr ff' in
       let intro (id,_) = Tactics.introduction id  in 

       let intro_vars = Tacticals.New.tclTHENLIST (List.map intro vars) in
       let intro_props = Tacticals.New.tclTHENLIST (List.map intro props) in
       let ipat_of_name id = Some (CAst.make @@ IntroNaming (Namegen.IntroIdentifier id)) in
       let goal_name = fresh_id Id.Set.empty (Names.Id.of_string "__arith") gl in
       let env' = List.map (fun (id,i) -> EConstr.mkVar id,i) vars in 

       let tac_arith = Tacticals.New.tclTHENLIST [ intro_props ; intro_vars ; 
                                                    micromega_order_change spec res'
                                                      (EConstr.mkApp(Lazy.force coq_list, [|spec.proof_typ|])) env' ff_arith ] in

       let goal_props = List.rev (prop_env_of_formula sigma ff') in 

       let goal_vars = List.map (fun (_,i) -> List.nth env (i-1)) vars in 
       
       let arith_args = goal_props @ goal_vars in

       let kill_arith = 
           Tacticals.New.tclTHEN
             (Tactics.keep [])
             ((*Tactics.tclABSTRACT  None*)
                (Tacticals.New.tclTHEN tac_arith tac)) in 

       Tacticals.New.tclTHENS
         (Tactics.forward true (Some None) (ipat_of_name goal_name) arith_goal)
         [
           kill_arith;
           (Tacticals.New.tclTHENLIST
            [(Tactics.generalize (List.map EConstr.mkVar ids));
             Tactics.exact_check (EConstr.applist (EConstr.mkVar goal_name, arith_args))
            ] )
         ]
    with
    | ParseError  -> Tacticals.New.tclFAIL 0 (Pp.str "Bad logical fragment")
    | Mfourier.TimeOut  -> Tacticals.New.tclFAIL 0 (Pp.str "Timeout")
    | CsdpNotFound -> flush stdout ;
     Tacticals.New.tclFAIL 0 (Pp.str 
                           (" Skipping what remains of this tactic: the complexity of the goal requires "
                            ^ "the use of a specialized external tool called csdp. \n\n" 
                            ^ "Unfortunately Coq isn't aware of the presence of any \"csdp\" executable in the path. \n\n"
                            ^ "Csdp packages are provided by some OS distributions; binaries and source code can be downloaded from https://projects.coin-or.org/Csdp"))
  end

let micromega_gen parse_arith 
    (negate:'cst atom -> 'cst mc_cnf)
    (normalise:'cst atom -> 'cst mc_cnf)
    unsat deduce 
    spec prover  =
 (micromega_gen parse_arith negate normalise unsat deduce spec prover)
 
       

let micromega_order_changer cert env ff  = 
  (*let ids = Util.List.map_i (fun i _ -> (Names.Id.of_string ("__v"^(string_of_int i)))) 0 env in *)
  let coeff = Lazy.force coq_Rcst in
  let dump_coeff = dump_Rcst in
  let typ  = Lazy.force coq_R in
  let cert_typ = (EConstr.mkApp(Lazy.force coq_list, [|Lazy.force coq_QWitness |])) in
 
  let formula_typ = (EConstr.mkApp (Lazy.force coq_Cstr,[| coeff|])) in
  let ff = dump_formula formula_typ (dump_cstr coeff dump_coeff) ff in
  let vm = dump_varmap (typ) (vm_of_list env) in
  Proofview.Goal.nf_enter begin fun gl -> 
    Tacticals.New.tclTHENLIST
     [
     (Tactics.change_concl
      (set
        [
         ("__ff", ff, EConstr.mkApp(Lazy.force coq_Formula, [|formula_typ |]));
         ("__varmap", vm, EConstr.mkApp
          (gen_constant_in_modules "VarMap"
	    [["Coq" ; "micromega" ; "VarMap"] ; ["VarMap"]] "t", [|typ|]));
         ("__wit", cert, cert_typ)
        ]
        (Tacmach.New.pf_concl gl)));
     (*      Tacticals.New.tclTHENLIST (List.map (fun id ->  (Tactics.introduction id)) ids)*)
     ]
  end

let micromega_genr prover tac =
  let parse_arith = parse_rarith in
  let negate = Mc.rnegate in
  let normalise = Mc.rnormalise in
  let unsat = Mc.runsat in
  let deduce = Mc.rdeduce in
  let spec = lazy {
    typ = Lazy.force coq_R;
    coeff = Lazy.force coq_Rcst;
    dump_coeff = dump_q;
    proof_typ = Lazy.force coq_QWitness ;
    dump_proof = dump_psatz coq_Q dump_q
  } in
  Proofview.Goal.nf_enter begin fun gl -> 
     let sigma = Tacmach.New.project gl in
     let concl = Tacmach.New.pf_concl gl in
     let hyps  = Tacmach.New.pf_hyps_types gl in

     try
      let gl0 = { env = Tacmach.New.pf_env gl; sigma } in
      let (hyps,concl,env) = parse_goal gl0 parse_arith Env.empty hyps concl in
       let env = Env.elements env in
       let spec = Lazy.force spec in
       
       let hyps' = List.map (fun (n,f) -> (n, map_atoms (Micromega.map_Formula Micromega.q_of_Rcst) f)) hyps in
       let concl' = map_atoms (Micromega.map_Formula Micromega.q_of_Rcst) concl in
       
       match micromega_tauto  negate normalise unsat deduce spec prover env hyps' concl' gl0 with
       | None -> Tacticals.New.tclFAIL 0 (Pp.str " Cannot find witness") 
       | Some (ids,ff',res') -> 
         let (ff,ids) = formula_hyps_concl 
	     (List.filter (fun (n,_) -> List.mem n ids) hyps) concl in
         let ff' = abstract_wrt_formula ff' ff  in

         let (arith_goal,props,vars,ff_arith) = make_goal_of_formula sigma (Lazy.force dump_rexpr)  ff' in
         let intro (id,_) = Tactics.introduction id  in 

       let intro_vars = Tacticals.New.tclTHENLIST (List.map intro vars) in
       let intro_props = Tacticals.New.tclTHENLIST (List.map intro props) in
       let ipat_of_name id = Some (CAst.make @@ IntroNaming (Namegen.IntroIdentifier id)) in
       let goal_name = fresh_id Id.Set.empty (Names.Id.of_string "__arith") gl in
       let env' = List.map (fun (id,i) -> EConstr.mkVar id,i) vars in 
       
       let tac_arith = Tacticals.New.tclTHENLIST [ intro_props ; intro_vars ; 
                                                    micromega_order_changer res' env' ff_arith ] in

       let goal_props = List.rev (prop_env_of_formula sigma ff') in 

       let goal_vars = List.map (fun (_,i) -> List.nth env (i-1)) vars in 
       
       let arith_args = goal_props @ goal_vars in

       let kill_arith = 
           Tacticals.New.tclTHEN
             (Tactics.keep [])
             ((*Tactics.tclABSTRACT  None*)
                (Tacticals.New.tclTHEN tac_arith tac)) in 

       Tacticals.New.tclTHENS
         (Tactics.forward true (Some None) (ipat_of_name goal_name) arith_goal)
         [
           kill_arith;
           (Tacticals.New.tclTHENLIST
            [(Tactics.generalize (List.map EConstr.mkVar ids));
             Tactics.exact_check (EConstr.applist (EConstr.mkVar goal_name, arith_args))
            ] )
         ]

    with
    | ParseError  -> Tacticals.New.tclFAIL 0 (Pp.str "Bad logical fragment")
    | Mfourier.TimeOut  -> Tacticals.New.tclFAIL 0 (Pp.str "Timeout")
    | CsdpNotFound -> flush stdout ;
     Tacticals.New.tclFAIL 0 (Pp.str 
                           (" Skipping what remains of this tactic: the complexity of the goal requires "
                            ^ "the use of a specialized external tool called csdp. \n\n" 
                            ^ "Unfortunately Coq isn't aware of the presence of any \"csdp\" executable in the path. \n\n"
                            ^ "Csdp packages are provided by some OS distributions; binaries and source code can be downloaded from https://projects.coin-or.org/Csdp"))
  end




let micromega_genr prover  = (micromega_genr prover)


let lift_ratproof  prover l =
 match prover l with
  | None -> None
  | Some c -> Some (Mc.RatProof( c,Mc.DoneProof))

type micromega_polys = (Micromega.q Mc.pol * Mc.op1) list

[@@@ocaml.warning "-37"]
type csdp_certificate = S of Sos_types.positivstellensatz option | F of string
(* Used to read the result of the execution of csdpcert *)

type provername = string * int option

(**
  * The caching mechanism.
  *)

open Persistent_cache

module Cache = PHashtable(struct
  type t = (provername * micromega_polys)
  let equal = Pervasives.(=)
  let hash  = Hashtbl.hash
end)

let csdp_cache = ".csdp.cache"

(**
  * Build the command to call csdpcert, and launch it. This in turn will call
  * the sos driver to the csdp executable.
  * Throw CsdpNotFound if Coq isn't aware of any csdp executable.
  *)

let require_csdp =
  if System.is_in_system_path "csdp" 
  then lazy ()
  else lazy (raise CsdpNotFound)

let really_call_csdpcert : provername -> micromega_polys -> Sos_types.positivstellensatz option  =
  fun provername poly ->

  Lazy.force require_csdp;

  let cmdname =
    List.fold_left Filename.concat (Envars.coqlib ())
      ["plugins"; "micromega"; "csdpcert" ^ Coq_config.exec_extension] in

    match ((command cmdname [|cmdname|] (provername,poly)) : csdp_certificate) with
      | F str -> failwith str
      | S res -> res

(**
  * Check the cache before calling the prover.
  *)

let xcall_csdpcert =
  Cache.memo csdp_cache (fun (prover,pb) -> really_call_csdpcert prover pb)

(**
  * Prover callback functions.
  *)

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
     else ((print_string "buggy certificate") ;None)

let call_csdpcert_z provername poly =
 let l = List.map (fun (e,o) -> (z_to_q_pol e,o)) poly in
  match call_csdpcert provername l with
   | None -> None
   | Some cert ->
      let cert = Certificate.z_cert_of_pos cert in
      if Mc.zWeakChecker poly cert
      then Some cert
      else ((print_string "buggy certificate" ; flush stdout) ;None)

let xhyps_of_cone base acc prf =
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
    else (f (x-ofset) + ofset) in

  let rec compact_pt ofset pt =
    match pt with
      | Mc.DoneProof -> Mc.DoneProof
      | Mc.RatProof(c,pt) -> Mc.RatProof(compact_cone c (translate (ofset)), compact_pt (ofset+1) pt )
      | Mc.CutProof(c,pt) -> Mc.CutProof(compact_cone c (translate (ofset)), compact_pt (ofset+1) pt )
      | Mc.EnumProof(c1,c2,l) -> Mc.EnumProof(compact_cone c1 (translate (ofset)), compact_cone c2 (translate (ofset)),
						   Mc.map (fun x -> compact_pt (ofset+1) x) l) in
    compact_pt 0 pt

(** 
  * Definition of provers.
  * Instantiates the type ('a,'prf) prover defined above.
  *)

let lift_pexpr_prover p l =  p (List.map (fun (e,o) -> Mc.denorm e , o) l)

module CacheZ = PHashtable(struct
 type prover_option = bool * int

 type t = prover_option * ((Mc.z Mc.pol * Mc.op1) list)
  let equal = (=)
  let hash  = Hashtbl.hash
end)

module CacheQ = PHashtable(struct
  type t = int * ((Mc.q Mc.pol * Mc.op1) list)
  let equal = (=)
  let hash  = Hashtbl.hash
end)

let memo_zlinear_prover = CacheZ.memo ".lia.cache" (fun ((ce,b),s) -> lift_pexpr_prover (Certificate.lia ce b) s)
let memo_nlia = CacheZ.memo ".nia.cache" (fun ((ce,b),s) -> lift_pexpr_prover (Certificate.nlia ce b) s)
let memo_nra = CacheQ.memo ".nra.cache" (fun (o,s) -> lift_pexpr_prover (Certificate.nlinear_prover o) s)


 
let linear_prover_Q = {
 name    = "linear prover";
 get_option = get_lra_option ; 
 prover  = (fun (o,l) -> lift_pexpr_prover (Certificate.linear_prover_with_cert o Certificate.q_spec) l) ;
 hyps    = hyps_of_cone ;
 compact = compact_cone ;
 pp_prf  = pp_psatz pp_q ;
 pp_f   = fun o x -> pp_pol pp_q o  (fst x)
}


let linear_prover_R = {
  name    = "linear prover";
 get_option = get_lra_option ; 
 prover  = (fun (o,l) -> lift_pexpr_prover (Certificate.linear_prover_with_cert o Certificate.q_spec) l) ;
  hyps    = hyps_of_cone ;
  compact = compact_cone ;
  pp_prf  = pp_psatz pp_q ;
  pp_f    =  fun o x -> pp_pol pp_q o (fst x)
}

let nlinear_prover_R = {
  name    = "nra";
 get_option = get_lra_option;
 prover  = memo_nra ;
  hyps    = hyps_of_cone ;
  compact = compact_cone ;
  pp_prf  = pp_psatz pp_q ;
  pp_f    =  fun o x -> pp_pol pp_q o (fst x)
}

let non_linear_prover_Q str o = {
  name    = "real nonlinear prover";
 get_option = (fun () -> (str,o));
 prover  = (fun (o,l) -> call_csdpcert_q o l);
  hyps    = hyps_of_cone;
  compact = compact_cone ;
  pp_prf  = pp_psatz pp_q ;
  pp_f    = fun o x -> pp_pol pp_q o  (fst x)
}

let non_linear_prover_R str o = {
  name    = "real nonlinear prover";
 get_option = (fun () -> (str,o));
 prover  = (fun (o,l) -> call_csdpcert_q o l);
  hyps    = hyps_of_cone;
  compact = compact_cone;
  pp_prf  = pp_psatz pp_q;
  pp_f    = fun o x -> pp_pol pp_q o  (fst x)
}

let non_linear_prover_Z str o  = {
  name    = "real nonlinear prover";
 get_option = (fun () -> (str,o));
 prover  = (fun (o,l) -> lift_ratproof (call_csdpcert_z o) l);
  hyps    = hyps_of_pt;
  compact = compact_pt;
  pp_prf  = pp_proof_term;
  pp_f    =  fun o x -> pp_pol pp_z o (fst x)
}

let linear_Z =   {
  name    = "lia";
 get_option = get_lia_option;
 prover  = memo_zlinear_prover ;
  hyps    = hyps_of_pt;
  compact = compact_pt;
  pp_prf  = pp_proof_term;
  pp_f    = fun o x -> pp_pol pp_z o (fst x)
}

let nlinear_Z =   {
  name    = "nlia";
 get_option = get_lia_option;
 prover  = memo_nlia ;
  hyps    = hyps_of_pt;
  compact = compact_pt;
  pp_prf  = pp_proof_term;
  pp_f    = fun o x -> pp_pol pp_z o (fst x)
}

(** 
  * Functions instantiating micromega_gen with the appropriate theories and
  * solvers
  *)

let lra_Q =
 micromega_gen parse_qarith Mc.qnegate Mc.qnormalise Mc.qunsat Mc.qdeduce qq_domain_spec dump_qexpr
  [ linear_prover_Q ] 

let psatz_Q i  =
 micromega_gen parse_qarith Mc.qnegate Mc.qnormalise Mc.qunsat Mc.qdeduce qq_domain_spec dump_qexpr
  [ non_linear_prover_Q "real_nonlinear_prover" (Some i) ]

let lra_R  =
 micromega_genr [ linear_prover_R ]

let psatz_R i  =
 micromega_genr  [ non_linear_prover_R "real_nonlinear_prover" (Some i) ] 


let psatz_Z i  =
    micromega_gen parse_zarith Mc.negate Mc.normalise Mc.zunsat Mc.zdeduce zz_domain_spec dump_zexpr
      [ non_linear_prover_Z "real_nonlinear_prover" (Some i) ] 

let sos_Z  =
 micromega_gen parse_zarith Mc.negate Mc.normalise  Mc.zunsat Mc.zdeduce zz_domain_spec dump_zexpr
  [ non_linear_prover_Z "pure_sos" None ] 

let sos_Q  =
 micromega_gen parse_qarith Mc.qnegate Mc.qnormalise  Mc.qunsat Mc.qdeduce qq_domain_spec dump_qexpr
  [ non_linear_prover_Q "pure_sos" None ] 


let sos_R  =
 micromega_genr  [ non_linear_prover_R "pure_sos" None ] 


let xlia  =  micromega_gen parse_zarith Mc.negate Mc.normalise Mc.zunsat Mc.zdeduce zz_domain_spec dump_zexpr
      [ linear_Z ] 

let xnlia  =
    micromega_gen parse_zarith Mc.negate Mc.normalise Mc.zunsat Mc.zdeduce zz_domain_spec dump_zexpr
      [ nlinear_Z ] 

let nra  = 
 micromega_genr  [ nlinear_prover_R ] 

let nqa  =
 micromega_gen parse_qarith Mc.qnegate Mc.qnormalise Mc.qunsat Mc.qdeduce qq_domain_spec dump_qexpr
  [ nlinear_prover_R ]

   

(* Local Variables: *)
(* coding: utf-8 *)
(* End: *)
