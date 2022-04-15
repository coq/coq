(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
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
(* - Modules Mc, Env, Cache, CacheZ                                  *)
(*                                                                      *)
(*  Frédéric Besson (Irisa/Inria) 2006-2019                             *)
(*                                                                      *)
(************************************************************************)

open Pp
open Names
open Goptions
open Mutils
open Constr
open Context
open Tactypes
open McPrinter

(**
  * Debug flag
  *)

let debug = false

(* Limit the proof search *)

let max_depth = max_int

(* Search limit for provers over Q R *)
let lra_proof_depth =
  declare_int_option_and_ref ~depr:true ~key:["Lra"; "Depth"] ~value:max_depth

(* Search limit for provers over Z *)
let lia_enum =
  declare_bool_option_and_ref ~depr:true ~key:["Lia"; "Enum"] ~value:true

let lia_proof_depth =
  declare_int_option_and_ref ~depr:true ~key:["Lia"; "Depth"] ~value:max_depth

let get_lia_option () =
  (true, lia_enum (), lia_proof_depth ())

(* Enable/disable caches *)

let use_lia_cache =
  declare_bool_option_and_ref ~depr:false ~key:["Lia"; "Cache"] ~value:true

let use_nia_cache =
  declare_bool_option_and_ref ~depr:false ~key:["Nia"; "Cache"] ~value:true

let use_nra_cache =
  declare_bool_option_and_ref ~depr:false ~key:["Nra"; "Cache"] ~value:true

let use_csdp_cache () = true

(**
  * Initialize a tag type to the Tag module declaration (see Mutils).
  *)

type tag = Tag.t

module Mc = Micromega

(**
  * An atom is of the form:
  *   pExpr1 \{<,>,=,<>,<=,>=\} pExpr2
  * where pExpr1, pExpr2 are polynomial expressions (see Micromega). pExprs are
  * parametrized by 'cst, which is used as the type of constants.
  *)

type 'cst atom = 'cst Mc.formula

type 'cst formula =
  ('cst atom, EConstr.constr, tag * EConstr.constr, Names.Id.t) Mc.gFormula

type 'cst clause = ('cst Mc.nFormula, tag * EConstr.constr) Mc.clause
type 'cst cnf = ('cst Mc.nFormula, tag * EConstr.constr) Mc.cnf

let pp_kind o = function
  | Mc.IsProp -> output_string o "Prop"
  | Mc.IsBool -> output_string o "bool"

let kind_is_prop = function Mc.IsProp -> true | Mc.IsBool -> false

let rec pp_formula o (f : 'cst formula) =
  Mc.(
    match f with
    | TT k -> output_string o (if kind_is_prop k then "True" else "true")
    | FF k -> output_string o (if kind_is_prop k then "False" else "false")
    | X (k, c) -> Printf.fprintf o "X %a" pp_kind k
    | A (_, _, (t, _)) -> Printf.fprintf o "A(%a)" Tag.pp t
    | AND (_, f1, f2) ->
      Printf.fprintf o "AND(%a,%a)" pp_formula f1 pp_formula f2
    | OR (_, f1, f2) -> Printf.fprintf o "OR(%a,%a)" pp_formula f1 pp_formula f2
    | IMPL (_, f1, n, f2) ->
      Printf.fprintf o "IMPL(%a,%s,%a)" pp_formula f1
        (match n with Some id -> Names.Id.to_string id | None -> "")
        pp_formula f2
    | NOT (_, f) -> Printf.fprintf o "NOT(%a)" pp_formula f
    | IFF (_, f1, f2) ->
      Printf.fprintf o "IFF(%a,%a)" pp_formula f1 pp_formula f2
    | EQ (f1, f2) -> Printf.fprintf o "EQ(%a,%a)" pp_formula f1 pp_formula f2)

(**
  * Given a set of integers s=\{i0,...,iN\} and a list m, return the list of
  * elements of m that are at position i0,...,iN.
  *)

let selecti s m =
  let rec xselecti i m =
    match m with
    | [] -> []
    | e :: m ->
      if ISet.mem i s then e :: xselecti (i + 1) m else xselecti (i + 1) m
  in
  xselecti 0 m

(**
  * MODULE: Mapping of the Coq data-strustures into Caml and Caml extracted
  * code. This includes initializing Caml variables based on Coq terms, parsing
  * various Coq expressions into Caml, and dumping Caml expressions into Coq.
  *
  * Opened here and in csdpcert.ml.
  *)

(**
    * Initialization : a large amount of Caml symbols are derived from
    * ZMicromega.v
    *)

let constr_of_ref str =
  EConstr.of_constr (UnivGen.constr_of_monomorphic_global (Global.env ()) (Coqlib.lib_ref str))

let coq_and = lazy (constr_of_ref "core.and.type")
let coq_or = lazy (constr_of_ref "core.or.type")
let coq_not = lazy (constr_of_ref "core.not.type")
let coq_iff = lazy (constr_of_ref "core.iff.type")
let coq_True = lazy (constr_of_ref "core.True.type")
let coq_False = lazy (constr_of_ref "core.False.type")
let coq_bool = lazy (constr_of_ref "core.bool.type")
let coq_true = lazy (constr_of_ref "core.bool.true")
let coq_false = lazy (constr_of_ref "core.bool.false")
let coq_andb = lazy (constr_of_ref "core.bool.andb")
let coq_orb = lazy (constr_of_ref "core.bool.orb")
let coq_implb = lazy (constr_of_ref "core.bool.implb")
let coq_eqb = lazy (constr_of_ref "core.bool.eqb")
let coq_negb = lazy (constr_of_ref "core.bool.negb")
let coq_cons = lazy (constr_of_ref "core.list.cons")
let coq_nil = lazy (constr_of_ref "core.list.nil")
let coq_list = lazy (constr_of_ref "core.list.type")
let coq_O = lazy (constr_of_ref "num.nat.O")
let coq_S = lazy (constr_of_ref "num.nat.S")
let coq_nat = lazy (constr_of_ref "num.nat.type")
let coq_unit = lazy (constr_of_ref "core.unit.type")

(*  let coq_option = lazy (init_constant "option")*)
let coq_None = lazy (constr_of_ref "core.option.None")
let coq_tt = lazy (constr_of_ref "core.unit.tt")
let coq_Inl = lazy (constr_of_ref "core.sum.inl")
let coq_Inr = lazy (constr_of_ref "core.sum.inr")
let coq_N0 = lazy (constr_of_ref "num.N.N0")
let coq_Npos = lazy (constr_of_ref "num.N.Npos")
let coq_xH = lazy (constr_of_ref "num.pos.xH")
let coq_xO = lazy (constr_of_ref "num.pos.xO")
let coq_xI = lazy (constr_of_ref "num.pos.xI")
let coq_Z = lazy (constr_of_ref "num.Z.type")
let coq_ZERO = lazy (constr_of_ref "num.Z.Z0")
let coq_POS = lazy (constr_of_ref "num.Z.Zpos")
let coq_NEG = lazy (constr_of_ref "num.Z.Zneg")
let coq_Q = lazy (constr_of_ref "rat.Q.type")
let coq_Qmake = lazy (constr_of_ref "rat.Q.Qmake")
let coq_R = lazy (constr_of_ref "reals.R.type")
let coq_Rcst = lazy (constr_of_ref "micromega.Rcst.type")
let coq_C0 = lazy (constr_of_ref "micromega.Rcst.C0")
let coq_C1 = lazy (constr_of_ref "micromega.Rcst.C1")
let coq_CQ = lazy (constr_of_ref "micromega.Rcst.CQ")
let coq_CZ = lazy (constr_of_ref "micromega.Rcst.CZ")
let coq_CPlus = lazy (constr_of_ref "micromega.Rcst.CPlus")
let coq_CMinus = lazy (constr_of_ref "micromega.Rcst.CMinus")
let coq_CMult = lazy (constr_of_ref "micromega.Rcst.CMult")
let coq_CPow = lazy (constr_of_ref "micromega.Rcst.CPow")
let coq_CInv = lazy (constr_of_ref "micromega.Rcst.CInv")
let coq_COpp = lazy (constr_of_ref "micromega.Rcst.COpp")
let coq_R0 = lazy (constr_of_ref "reals.R.R0")
let coq_R1 = lazy (constr_of_ref "reals.R.R1")
let coq_proofTerm = lazy (constr_of_ref "micromega.ZArithProof.type")
let coq_doneProof = lazy (constr_of_ref "micromega.ZArithProof.DoneProof")
let coq_ratProof = lazy (constr_of_ref "micromega.ZArithProof.RatProof")
let coq_cutProof = lazy (constr_of_ref "micromega.ZArithProof.CutProof")
let coq_splitProof = lazy (constr_of_ref "micromega.ZArithProof.SplitProof")
let coq_enumProof = lazy (constr_of_ref "micromega.ZArithProof.EnumProof")
let coq_ExProof = lazy (constr_of_ref "micromega.ZArithProof.ExProof")
let coq_IsProp = lazy (constr_of_ref "micromega.kind.isProp")
let coq_IsBool = lazy (constr_of_ref "micromega.kind.isBool")
let coq_Zgt = lazy (constr_of_ref "num.Z.gt")
let coq_Zge = lazy (constr_of_ref "num.Z.ge")
let coq_Zle = lazy (constr_of_ref "num.Z.le")
let coq_Zlt = lazy (constr_of_ref "num.Z.lt")
let coq_Zgtb = lazy (constr_of_ref "num.Z.gtb")
let coq_Zgeb = lazy (constr_of_ref "num.Z.geb")
let coq_Zleb = lazy (constr_of_ref "num.Z.leb")
let coq_Zltb = lazy (constr_of_ref "num.Z.ltb")
let coq_Zeqb = lazy (constr_of_ref "num.Z.eqb")
let coq_eq = lazy (constr_of_ref "core.eq.type")
let coq_Zplus = lazy (constr_of_ref "num.Z.add")
let coq_Zminus = lazy (constr_of_ref "num.Z.sub")
let coq_Zopp = lazy (constr_of_ref "num.Z.opp")
let coq_Zmult = lazy (constr_of_ref "num.Z.mul")
let coq_Zpower = lazy (constr_of_ref "num.Z.pow")
let coq_Qle = lazy (constr_of_ref "rat.Q.Qle")
let coq_Qlt = lazy (constr_of_ref "rat.Q.Qlt")
let coq_Qeq = lazy (constr_of_ref "rat.Q.Qeq")
let coq_Qplus = lazy (constr_of_ref "rat.Q.Qplus")
let coq_Qminus = lazy (constr_of_ref "rat.Q.Qminus")
let coq_Qopp = lazy (constr_of_ref "rat.Q.Qopp")
let coq_Qmult = lazy (constr_of_ref "rat.Q.Qmult")
let coq_Qpower = lazy (constr_of_ref "rat.Q.Qpower")
let coq_Rgt = lazy (constr_of_ref "reals.R.Rgt")
let coq_Rge = lazy (constr_of_ref "reals.R.Rge")
let coq_Rle = lazy (constr_of_ref "reals.R.Rle")
let coq_Rlt = lazy (constr_of_ref "reals.R.Rlt")
let coq_Rplus = lazy (constr_of_ref "reals.R.Rplus")
let coq_Rminus = lazy (constr_of_ref "reals.R.Rminus")
let coq_Ropp = lazy (constr_of_ref "reals.R.Ropp")
let coq_Rmult = lazy (constr_of_ref "reals.R.Rmult")
let coq_Rinv = lazy (constr_of_ref "reals.R.Rinv")
let coq_Rpower = lazy (constr_of_ref "reals.R.pow")
let coq_powerZR = lazy (constr_of_ref "reals.R.powerRZ")
let coq_IZR = lazy (constr_of_ref "reals.R.IZR")
let coq_IQR = lazy (constr_of_ref "reals.R.Q2R")
let coq_PEX = lazy (constr_of_ref "micromega.PExpr.PEX")
let coq_PEc = lazy (constr_of_ref "micromega.PExpr.PEc")
let coq_PEadd = lazy (constr_of_ref "micromega.PExpr.PEadd")
let coq_PEopp = lazy (constr_of_ref "micromega.PExpr.PEopp")
let coq_PEmul = lazy (constr_of_ref "micromega.PExpr.PEmul")
let coq_PEsub = lazy (constr_of_ref "micromega.PExpr.PEsub")
let coq_PEpow = lazy (constr_of_ref "micromega.PExpr.PEpow")
let coq_PX = lazy (constr_of_ref "micromega.Pol.PX")
let coq_Pc = lazy (constr_of_ref "micromega.Pol.Pc")
let coq_Pinj = lazy (constr_of_ref "micromega.Pol.Pinj")
let coq_OpEq = lazy (constr_of_ref "micromega.Op2.OpEq")
let coq_OpNEq = lazy (constr_of_ref "micromega.Op2.OpNEq")
let coq_OpLe = lazy (constr_of_ref "micromega.Op2.OpLe")
let coq_OpLt = lazy (constr_of_ref "micromega.Op2.OpLt")
let coq_OpGe = lazy (constr_of_ref "micromega.Op2.OpGe")
let coq_OpGt = lazy (constr_of_ref "micromega.Op2.OpGt")
let coq_PsatzLet = lazy (constr_of_ref "micromega.Psatz.PsatzLet")
let coq_PsatzIn = lazy (constr_of_ref "micromega.Psatz.PsatzIn")
let coq_PsatzSquare = lazy (constr_of_ref "micromega.Psatz.PsatzSquare")
let coq_PsatzMulE = lazy (constr_of_ref "micromega.Psatz.PsatzMulE")
let coq_PsatzMultC = lazy (constr_of_ref "micromega.Psatz.PsatzMulC")
let coq_PsatzAdd = lazy (constr_of_ref "micromega.Psatz.PsatzAdd")
let coq_PsatzC = lazy (constr_of_ref "micromega.Psatz.PsatzC")
let coq_PsatzZ = lazy (constr_of_ref "micromega.Psatz.PsatzZ")

(*  let coq_GT     = lazy (m_constant "GT")*)

let coq_DeclaredConstant =
  lazy (constr_of_ref "micromega.DeclaredConstant.type")

let coq_TT = lazy (constr_of_ref "micromega.GFormula.TT")
let coq_FF = lazy (constr_of_ref "micromega.GFormula.FF")
let coq_AND = lazy (constr_of_ref "micromega.GFormula.AND")
let coq_OR = lazy (constr_of_ref "micromega.GFormula.OR")
let coq_NOT = lazy (constr_of_ref "micromega.GFormula.NOT")
let coq_Atom = lazy (constr_of_ref "micromega.GFormula.A")
let coq_X = lazy (constr_of_ref "micromega.GFormula.X")
let coq_IMPL = lazy (constr_of_ref "micromega.GFormula.IMPL")
let coq_IFF = lazy (constr_of_ref "micromega.GFormula.IFF")
let coq_EQ = lazy (constr_of_ref "micromega.GFormula.EQ")
let coq_Formula = lazy (constr_of_ref "micromega.BFormula.type")
let coq_eKind = lazy (constr_of_ref "micromega.eKind")

(**
    * Initialization : a few Caml symbols are derived from other libraries;
    * QMicromega, ZArithRing, RingMicromega.
    *)

let coq_QWitness = lazy (constr_of_ref "micromega.QWitness.type")
let coq_Build = lazy (constr_of_ref "micromega.Formula.Build_Formula")
let coq_Cstr = lazy (constr_of_ref "micromega.Formula.type")

(**
    * Parsing and dumping : transformation functions between Caml and Coq
    * data-structures.
    *
    * dump_*    functions go from Micromega to Coq terms
    * undump_*  functions go from Coq to Micromega terms (reverse of dump_)
    * parse_*   functions go from Coq to Micromega terms
    * pp_*      functions pretty-print Coq terms.
    *)

exception ParseError

(* A simple but useful getter function *)

let get_left_construct sigma term =
  match EConstr.kind sigma term with
  | Construct ((_, i), _) -> (i, [||])
  | App (l, rst) -> (
    match EConstr.kind sigma l with
    | Construct ((_, i), _) -> (i, rst)
    | _ -> raise ParseError )
  | _ -> raise ParseError

(* Access the Micromega module *)

(* parse/dump/print from numbers up to expressions and formulas *)

let rec parse_nat sigma term =
  let i, c = get_left_construct sigma term in
  match i with
  | 1 -> Mc.O
  | 2 -> Mc.S (parse_nat sigma c.(0))
  | i -> raise ParseError

let rec dump_nat x =
  match x with
  | Mc.O -> Lazy.force coq_O
  | Mc.S p -> EConstr.mkApp (Lazy.force coq_S, [|dump_nat p|])

let rec parse_positive sigma term =
  let i, c = get_left_construct sigma term in
  match i with
  | 1 -> Mc.XI (parse_positive sigma c.(0))
  | 2 -> Mc.XO (parse_positive sigma c.(0))
  | 3 -> Mc.XH
  | i -> raise ParseError

let rec dump_positive x =
  match x with
  | Mc.XH -> Lazy.force coq_xH
  | Mc.XO p -> EConstr.mkApp (Lazy.force coq_xO, [|dump_positive p|])
  | Mc.XI p -> EConstr.mkApp (Lazy.force coq_xI, [|dump_positive p|])

let parse_n sigma term =
  let i, c = get_left_construct sigma term in
  match i with
  | 1 -> Mc.N0
  | 2 -> Mc.Npos (parse_positive sigma c.(0))
  | i -> raise ParseError

let dump_n x =
  match x with
  | Mc.N0 -> Lazy.force coq_N0
  | Mc.Npos p -> EConstr.mkApp (Lazy.force coq_Npos, [|dump_positive p|])

(** [is_ground_term env sigma term] holds if the term [term]
      is an instance of the typeclass [DeclConstant.GT term]
      i.e. built from user-defined constants and functions.
      NB: This mechanism can be used to customise the reification process to decide
      what to consider as a constant (see [parse_constant])
   *)

let is_declared_term env evd t =
  match EConstr.kind evd t with
  | Const _ | Construct _ -> (
    (* Restrict typeclass resolution to trivial cases *)
    let typ = Retyping.get_type_of env evd t in
    try
      ignore
        (Typeclasses.resolve_one_typeclass env evd
           (EConstr.mkApp (Lazy.force coq_DeclaredConstant, [|typ; t|])));
      true
    with Not_found -> false )
  | _ -> false

let rec is_ground_term env evd term =
  match EConstr.kind evd term with
  | App (c, args) ->
    is_declared_term env evd c && Array.for_all (is_ground_term env evd) args
  | Const _ | Construct _ -> is_declared_term env evd term
  | _ -> false

let parse_z sigma term =
  let i, c = get_left_construct sigma term in
  match i with
  | 1 -> Mc.Z0
  | 2 -> Mc.Zpos (parse_positive sigma c.(0))
  | 3 -> Mc.Zneg (parse_positive sigma c.(0))
  | i -> raise ParseError

let dump_z x =
  match x with
  | Mc.Z0 -> Lazy.force coq_ZERO
  | Mc.Zpos p -> EConstr.mkApp (Lazy.force coq_POS, [|dump_positive p|])
  | Mc.Zneg p -> EConstr.mkApp (Lazy.force coq_NEG, [|dump_positive p|])


let dump_q q =
  EConstr.mkApp
    ( Lazy.force coq_Qmake
    , [|dump_z q.Micromega.qnum; dump_positive q.Micromega.qden|] )

let parse_q sigma term =
  match EConstr.kind sigma term with
  | App (c, args) ->
    if EConstr.eq_constr sigma c (Lazy.force coq_Qmake) then
      {Mc.qnum = parse_z sigma args.(0); Mc.qden = parse_positive sigma args.(1)}
    else raise ParseError
  | _ -> raise ParseError

let rec pp_Rcst o cst =
  match cst with
  | Mc.C0 -> output_string o "C0"
  | Mc.C1 -> output_string o "C1"
  | Mc.CQ q -> output_string o "CQ _"
  | Mc.CZ z -> pp_z o z
  | Mc.CPlus (x, y) -> Printf.fprintf o "(%a + %a)" pp_Rcst x pp_Rcst y
  | Mc.CMinus (x, y) -> Printf.fprintf o "(%a - %a)" pp_Rcst x pp_Rcst y
  | Mc.CMult (x, y) -> Printf.fprintf o "(%a * %a)" pp_Rcst x pp_Rcst y
  | Mc.CPow (x, y) -> Printf.fprintf o "(%a ^ _)" pp_Rcst x
  | Mc.CInv t -> Printf.fprintf o "(/ %a)" pp_Rcst t
  | Mc.COpp t -> Printf.fprintf o "(- %a)" pp_Rcst t

let rec dump_Rcst cst =
  match cst with
  | Mc.C0 -> Lazy.force coq_C0
  | Mc.C1 -> Lazy.force coq_C1
  | Mc.CQ q -> EConstr.mkApp (Lazy.force coq_CQ, [|dump_q q|])
  | Mc.CZ z -> EConstr.mkApp (Lazy.force coq_CZ, [|dump_z z|])
  | Mc.CPlus (x, y) ->
    EConstr.mkApp (Lazy.force coq_CPlus, [|dump_Rcst x; dump_Rcst y|])
  | Mc.CMinus (x, y) ->
    EConstr.mkApp (Lazy.force coq_CMinus, [|dump_Rcst x; dump_Rcst y|])
  | Mc.CMult (x, y) ->
    EConstr.mkApp (Lazy.force coq_CMult, [|dump_Rcst x; dump_Rcst y|])
  | Mc.CPow (x, y) ->
    EConstr.mkApp
      ( Lazy.force coq_CPow
      , [| dump_Rcst x
         ; ( match y with
           | Mc.Inl z ->
             EConstr.mkApp
               ( Lazy.force coq_Inl
               , [|Lazy.force coq_Z; Lazy.force coq_nat; dump_z z|] )
           | Mc.Inr n ->
             EConstr.mkApp
               ( Lazy.force coq_Inr
               , [|Lazy.force coq_Z; Lazy.force coq_nat; dump_nat n|] ) ) |] )
  | Mc.CInv t -> EConstr.mkApp (Lazy.force coq_CInv, [|dump_Rcst t|])
  | Mc.COpp t -> EConstr.mkApp (Lazy.force coq_COpp, [|dump_Rcst t|])

let rec dump_list typ dump_elt l =
  match l with
  | [] -> EConstr.mkApp (Lazy.force coq_nil, [|typ|])
  | e :: l ->
    EConstr.mkApp
      (Lazy.force coq_cons, [|typ; dump_elt e; dump_list typ dump_elt l|])


let undump_var = parse_positive

let dump_var = dump_positive

let undump_expr undump_constant sigma e =
  let is c c' = EConstr.eq_constr sigma c (Lazy.force c') in
  let rec xundump e =
    match EConstr.kind sigma e with
    | App (c, [|_; n|]) when is c coq_PEX -> Mc.PEX (undump_var sigma n)
    | App (c, [|_; z|]) when is c coq_PEc -> Mc.PEc (undump_constant sigma z)
    | App (c, [|_; e1; e2|]) when is c coq_PEadd ->
      Mc.PEadd (xundump e1, xundump e2)
    | App (c, [|_; e1; e2|]) when is c coq_PEsub ->
      Mc.PEsub (xundump e1, xundump e2)
    | App (c, [|_; e|]) when is c coq_PEopp -> Mc.PEopp (xundump e)
    | App (c, [|_; e1; e2|]) when is c coq_PEmul ->
      Mc.PEmul (xundump e1, xundump e2)
    | App (c, [|_; e; n|]) when is c coq_PEpow ->
      Mc.PEpow (xundump e, parse_n sigma n)
    | _ -> raise ParseError
  in
  xundump e

let dump_expr typ dump_z e =
  let rec dump_expr e =
    match e with
    | Mc.PEX n -> EConstr.mkApp (Lazy.force coq_PEX, [|typ; dump_var n|])
    | Mc.PEc z -> EConstr.mkApp (Lazy.force coq_PEc, [|typ; dump_z z|])
    | Mc.PEadd (e1, e2) ->
      EConstr.mkApp (Lazy.force coq_PEadd, [|typ; dump_expr e1; dump_expr e2|])
    | Mc.PEsub (e1, e2) ->
      EConstr.mkApp (Lazy.force coq_PEsub, [|typ; dump_expr e1; dump_expr e2|])
    | Mc.PEopp e -> EConstr.mkApp (Lazy.force coq_PEopp, [|typ; dump_expr e|])
    | Mc.PEmul (e1, e2) ->
      EConstr.mkApp (Lazy.force coq_PEmul, [|typ; dump_expr e1; dump_expr e2|])
    | Mc.PEpow (e, n) ->
      EConstr.mkApp (Lazy.force coq_PEpow, [|typ; dump_expr e; dump_n n|])
  in
  dump_expr e

let dump_pol typ dump_c e =
  let rec dump_pol e =
    match e with
    | Mc.Pc n -> EConstr.mkApp (Lazy.force coq_Pc, [|typ; dump_c n|])
    | Mc.Pinj (p, pol) ->
      EConstr.mkApp (Lazy.force coq_Pinj, [|typ; dump_positive p; dump_pol pol|])
    | Mc.PX (pol1, p, pol2) ->
      EConstr.mkApp
        ( Lazy.force coq_PX
        , [|typ; dump_pol pol1; dump_positive p; dump_pol pol2|] )
  in
  dump_pol e


(* let pp_clause pp_c o (f: 'cst clause) =
   List.iter (fun ((p,_),(t,_)) -> Printf.fprintf o "(%a @%a)" (pp_pol pp_c)  p Tag.pp t) f *)

let pp_clause_tag o (f : 'cst clause) =
  List.iter (fun ((p, _), (t, _)) -> Printf.fprintf o "(_ @%a)" Tag.pp t) f

(* let pp_cnf pp_c o (f:'cst cnf) =
   List.iter (fun l -> Printf.fprintf o "[%a]" (pp_clause pp_c) l) f *)

let pp_cnf_tag o (f : 'cst cnf) =
  List.iter (fun l -> Printf.fprintf o "[%a]" pp_clause_tag l) f

let dump_psatz typ dump_z e =
  let z = Lazy.force typ in
  let rec dump_cone e =
    match e with
    | Mc.PsatzLet (e1, e2) ->
      EConstr.mkApp (Lazy.force coq_PsatzLet, [|z; dump_cone e1; dump_cone e2|])
    | Mc.PsatzIn n -> EConstr.mkApp (Lazy.force coq_PsatzIn, [|z; dump_nat n|])
    | Mc.PsatzMulC (e, c) ->
      EConstr.mkApp
        (Lazy.force coq_PsatzMultC, [|z; dump_pol z dump_z e; dump_cone c|])
    | Mc.PsatzSquare e ->
      EConstr.mkApp (Lazy.force coq_PsatzSquare, [|z; dump_pol z dump_z e|])
    | Mc.PsatzAdd (e1, e2) ->
      EConstr.mkApp (Lazy.force coq_PsatzAdd, [|z; dump_cone e1; dump_cone e2|])
    | Mc.PsatzMulE (e1, e2) ->
      EConstr.mkApp (Lazy.force coq_PsatzMulE, [|z; dump_cone e1; dump_cone e2|])
    | Mc.PsatzC p -> EConstr.mkApp (Lazy.force coq_PsatzC, [|z; dump_z p|])
    | Mc.PsatzZ -> EConstr.mkApp (Lazy.force coq_PsatzZ, [|z|])
  in
  dump_cone e

let undump_op sigma c =
  let i, c = get_left_construct sigma c in
  match i with
  | 1 -> Mc.OpEq
  | 2 -> Mc.OpNEq
  | 3 -> Mc.OpLe
  | 4 -> Mc.OpGe
  | 5 -> Mc.OpLt
  | 6 -> Mc.OpGt
  | _ -> raise ParseError

let dump_op = function
  | Mc.OpEq -> Lazy.force coq_OpEq
  | Mc.OpNEq -> Lazy.force coq_OpNEq
  | Mc.OpLe -> Lazy.force coq_OpLe
  | Mc.OpGe -> Lazy.force coq_OpGe
  | Mc.OpGt -> Lazy.force coq_OpGt
  | Mc.OpLt -> Lazy.force coq_OpLt

let undump_cstr undump_constant sigma c =
  let is c c' = EConstr.eq_constr sigma c (Lazy.force c') in
  match EConstr.kind sigma c with
  | App (c, [|_; e1; o; e2|]) when is c coq_Build ->
    {Mc.flhs = undump_expr undump_constant sigma e1;
     Mc.fop = undump_op sigma o;
     Mc.frhs = undump_expr undump_constant sigma e2}
  | _ -> raise ParseError

let dump_cstr typ dump_constant {Mc.flhs = e1; Mc.fop = o; Mc.frhs = e2} =
  EConstr.mkApp
    ( Lazy.force coq_Build
    , [| typ
       ; dump_expr typ dump_constant e1
       ; dump_op o
       ; dump_expr typ dump_constant e2 |] )

let assoc_const sigma x l =
  try
    snd (List.find (fun (x', y) -> EConstr.eq_constr sigma x (Lazy.force x')) l)
  with Not_found -> raise ParseError

let zop_table_prop =
  [ (coq_Zgt, Mc.OpGt)
  ; (coq_Zge, Mc.OpGe)
  ; (coq_Zlt, Mc.OpLt)
  ; (coq_Zle, Mc.OpLe) ]

let zop_table_bool =
  [ (coq_Zgtb, Mc.OpGt)
  ; (coq_Zgeb, Mc.OpGe)
  ; (coq_Zltb, Mc.OpLt)
  ; (coq_Zleb, Mc.OpLe)
  ; (coq_Zeqb, Mc.OpEq) ]

let rop_table_prop =
  [ (coq_Rgt, Mc.OpGt)
  ; (coq_Rge, Mc.OpGe)
  ; (coq_Rlt, Mc.OpLt)
  ; (coq_Rle, Mc.OpLe) ]

let rop_table_bool = []
let qop_table_prop = [(coq_Qlt, Mc.OpLt); (coq_Qle, Mc.OpLe); (coq_Qeq, Mc.OpEq)]
let qop_table_bool = []

type gl = Environ.env * Evd.evar_map

let is_convertible env sigma t1 t2 = Reductionops.is_conv env sigma t1 t2

let parse_operator table_prop table_bool has_equality typ (env, sigma) k
    (op, args) =
  match args with
  | [|a1; a2|] ->
    ( assoc_const sigma op
        (match k with Mc.IsProp -> table_prop | Mc.IsBool -> table_bool)
    , a1
    , a2 )
  | [|ty; a1; a2|] ->
    if
      has_equality
      && EConstr.eq_constr sigma op (Lazy.force coq_eq)
      && is_convertible env sigma ty (Lazy.force typ)
    then (Mc.OpEq, args.(1), args.(2))
    else raise ParseError
  | _ -> raise ParseError

let parse_zop = parse_operator zop_table_prop zop_table_bool true coq_Z
let parse_rop = parse_operator rop_table_prop [] true coq_R
let parse_qop = parse_operator qop_table_prop [] false coq_R

type 'a op =
  | Binop of ('a Mc.pExpr -> 'a Mc.pExpr -> 'a Mc.pExpr)
  | Opp
  | Power
  | Ukn of string

let assoc_ops sigma x l =
  try
    snd (List.find (fun (x', y) -> EConstr.eq_constr sigma x (Lazy.force x')) l)
  with Not_found -> Ukn "Oups"

(**
    * MODULE: Env is for environment.
    *)

module Env = struct
  type t =
    { vars : (EConstr.t * Mc.kind) list
    ; (* The list represents a mapping from EConstr.t to indexes. *)
      gl : gl (* The evar_map may be updated due to unification of universes *)
    }

  let empty gl = {vars = []; gl}

  (** [eq_constr gl x y] returns an updated [gl] if x and y can be unified *)
  let eq_constr (env, sigma) x y =
    match EConstr.eq_constr_universes_proj env sigma x y with
    | Some csts -> (
      let csts = UnivProblem.Set.force csts in
      match Evd.add_universe_constraints sigma csts with
      | sigma -> Some (env, sigma)
      | exception UGraph.UniverseInconsistency _ -> None )
    | None -> None

  let compute_rank_add env v is_prop =
    let rec _add gl vars n v =
      match vars with
      | [] -> (gl, [(v, is_prop)], n)
      | (e, b) :: l -> (
        match eq_constr gl e v with
        | Some gl' -> (gl', vars, n)
        | None ->
          let gl, l', n = _add gl l (n + 1) v in
          (gl, (e, b) :: l', n) )
    in
    let gl', vars', n = _add env.gl env.vars 1 v in
    ({vars = vars'; gl = gl'}, CamlToCoq.positive n)

  let get_rank env v =
    let gl = env.gl in
    let rec _get_rank env n =
      match env with
      | [] -> raise (Invalid_argument "get_rank")
      | (e, _) :: l -> (
        match eq_constr gl e v with Some _ -> n | None -> _get_rank l (n + 1) )
    in
    _get_rank env.vars 1

  let elements env = env.vars

  (* let string_of_env gl env =
     let rec string_of_env i env acc =
       match env with
       | [] -> acc
       | e::env -> string_of_env (i+1) env
                     (IMap.add i
                             (Pp.string_of_ppcmds
                                   (Printer.pr_econstr_env gl.env gl.sigma e)) acc) in
     string_of_env 1 env IMap.empty
  *)
  let pp (genv, sigma) env =
    let ppl =
      List.mapi
        (fun i (e, _) ->
          Pp.str "x"
          ++ Pp.int (i + 1)
          ++ Pp.str ":"
          ++ Printer.pr_econstr_env genv sigma e)
        env
    in
    List.fold_right (fun e p -> e ++ Pp.str " ; " ++ p) ppl (Pp.str "\n")
end

(* MODULE END: Env *)

(**
    * This is the big generic function for expression parsers.
    *)

let parse_expr (genv, sigma) parse_constant parse_exp ops_spec env term =
  if debug then
    Feedback.msg_debug
      (Pp.str "parse_expr: " ++ Printer.pr_leconstr_env genv sigma term);
  let parse_variable env term =
    let env, n = Env.compute_rank_add env term Mc.IsBool in
    (Mc.PEX n, env)
  in
  let rec parse_expr env term =
    let combine env op (t1, t2) =
      let expr1, env = parse_expr env t1 in
      let expr2, env = parse_expr env t2 in
      (op expr1 expr2, env)
    in
    try (Mc.PEc (parse_constant (genv, sigma) term), env)
    with ParseError -> (
      match EConstr.kind sigma term with
      | App (t, args) -> (
        match EConstr.kind sigma t with
        | Const c -> (
          match assoc_ops sigma t ops_spec with
          | Binop f -> combine env f (args.(0), args.(1))
          | Opp ->
            let expr, env = parse_expr env args.(0) in
            (Mc.PEopp expr, env)
          | Power -> (
            try
              let expr, env = parse_expr env args.(0) in
              let power = parse_exp expr args.(1) in
              (power, env)
            with ParseError ->
              (* if the exponent is a variable *)
              let env, n = Env.compute_rank_add env term Mc.IsBool in
              (Mc.PEX n, env) )
          | Ukn s ->
            if debug then (
              Printf.printf "unknown op: %s\n" s;
              flush stdout );
            let env, n = Env.compute_rank_add env term Mc.IsBool in
            (Mc.PEX n, env) )
        | _ -> parse_variable env term )
      | _ -> parse_variable env term )
  in
  parse_expr env term

let zop_spec =
  [ (coq_Zplus, Binop (fun x y -> Mc.PEadd (x, y)))
  ; (coq_Zminus, Binop (fun x y -> Mc.PEsub (x, y)))
  ; (coq_Zmult, Binop (fun x y -> Mc.PEmul (x, y)))
  ; (coq_Zopp, Opp)
  ; (coq_Zpower, Power) ]

let qop_spec =
  [ (coq_Qplus, Binop (fun x y -> Mc.PEadd (x, y)))
  ; (coq_Qminus, Binop (fun x y -> Mc.PEsub (x, y)))
  ; (coq_Qmult, Binop (fun x y -> Mc.PEmul (x, y)))
  ; (coq_Qopp, Opp)
  ; (coq_Qpower, Power) ]

let rop_spec =
  [ (coq_Rplus, Binop (fun x y -> Mc.PEadd (x, y)))
  ; (coq_Rminus, Binop (fun x y -> Mc.PEsub (x, y)))
  ; (coq_Rmult, Binop (fun x y -> Mc.PEmul (x, y)))
  ; (coq_Ropp, Opp)
  ; (coq_Rpower, Power) ]

let parse_constant parse ((genv : Environ.env), sigma) t = parse sigma t

(** [parse_more_constant parse gl t] returns the reification of term [t].
      If [t] is a ground term, then it is first reduced to normal form
      before using a 'syntactic' parser *)
let parse_more_constant parse (genv, sigma) t =
  try parse (genv, sigma) t
  with ParseError ->
    if debug then Feedback.msg_debug Pp.(str "try harder");
    if is_ground_term genv sigma t then
      parse (genv, sigma) (Redexpr.cbv_vm genv sigma t)
    else raise ParseError

let zconstant = parse_constant parse_z
let qconstant = parse_constant parse_q
let nconstant = parse_constant parse_nat

(** [parse_more_zexpr parse_constant gl] improves the parsing of exponent
      which can be arithmetic expressions (without variables).
      [parse_constant_expr] returns a constant if the argument is an expression without variables. *)

let rec parse_zexpr gl =
  parse_expr gl zconstant
    (fun expr (x : EConstr.t) ->
      let z = parse_zconstant gl x in
      match z with
      | Mc.Zneg _ -> Mc.PEc Mc.Z0
      | _ -> Mc.PEpow (expr, Mc.Z.to_N z))
    zop_spec

and parse_zconstant gl e =
  let e, _ = parse_zexpr gl (Env.empty gl) e in
  match Mc.zeval_const e with None -> raise ParseError | Some z -> z

(* NB: R is a different story.
   Because it is axiomatised, reducing would not be effective.
   Therefore, there is a specific parser for constant over R
*)

let rconst_assoc =
  [ (coq_Rplus, fun x y -> Mc.CPlus (x, y))
  ; (coq_Rminus, fun x y -> Mc.CMinus (x, y))
  ; (coq_Rmult, fun x y -> Mc.CMult (x, y))
    (*      coq_Rdiv   , (fun x y -> Mc.CMult(x,Mc.CInv y)) ;*) ]

let rconstant (genv, sigma) term =
  let rec rconstant term =
    match EConstr.kind sigma term with
    | Const x ->
      if EConstr.eq_constr sigma term (Lazy.force coq_R0) then Mc.C0
      else if EConstr.eq_constr sigma term (Lazy.force coq_R1) then Mc.C1
      else raise ParseError
    | App (op, args) -> (
      try
        (* the evaluation order is important in the following *)
        let f = assoc_const sigma op rconst_assoc in
        let a = rconstant args.(0) in
        let b = rconstant args.(1) in
        f a b
      with ParseError -> (
        match op with
        | op when EConstr.eq_constr sigma op (Lazy.force coq_Rinv) ->
          let arg = rconstant args.(0) in
          if Mc.qeq_bool (Mc.q_of_Rcst arg) {Mc.qnum = Mc.Z0; Mc.qden = Mc.XH}
          then raise ParseError (* This is a division by zero -- no semantics *)
          else Mc.CInv arg
        | op when EConstr.eq_constr sigma op (Lazy.force coq_Rpower) ->
          Mc.CPow
            ( rconstant args.(0)
            , Mc.Inr (parse_more_constant nconstant (genv, sigma) args.(1)) )
        | op when EConstr.eq_constr sigma op (Lazy.force coq_IQR) ->
          Mc.CQ (qconstant (genv, sigma) args.(0))
        | op when EConstr.eq_constr sigma op (Lazy.force coq_IZR) ->
          Mc.CZ (parse_more_constant zconstant (genv, sigma) args.(0))
        | _ -> raise ParseError ) )
    | _ -> raise ParseError
  in
  rconstant term

let rconstant (genv, sigma) term =
  if debug then
    Feedback.msg_debug
      (Pp.str "rconstant: " ++ Printer.pr_leconstr_env genv sigma term ++ fnl ());
  let res = rconstant (genv, sigma) term in
  if debug then (
    Printf.printf "rconstant -> %a\n" pp_Rcst res;
    flush stdout );
  res

let parse_qexpr gl =
  parse_expr gl qconstant
    (fun expr x ->
      let exp = zconstant gl x in
      match exp with
      | Mc.Zneg _ -> (
        match expr with
        | Mc.PEc q -> Mc.PEc (Mc.qpower q exp)
        | _ -> raise ParseError )
      | _ ->
        let exp = Mc.Z.to_N exp in
        Mc.PEpow (expr, exp))
    qop_spec

let parse_rexpr (genv, sigma) =
  parse_expr (genv, sigma) rconstant
    (fun expr x ->
      let exp = Mc.N.of_nat (parse_nat sigma x) in
      Mc.PEpow (expr, exp))
    rop_spec

let parse_arith parse_op parse_expr (k : Mc.kind) env cstr (genv, sigma) =
  if debug then
    Feedback.msg_debug
      ( Pp.str "parse_arith: "
      ++ Printer.pr_leconstr_env genv sigma cstr
      ++ fnl () );
  match EConstr.kind sigma cstr with
  | App (op, args) ->
    let op, lhs, rhs = parse_op (genv, sigma) k (op, args) in
    let e1, env = parse_expr (genv, sigma) env lhs in
    let e2, env = parse_expr (genv, sigma) env rhs in
    ({Mc.flhs = e1; Mc.fop = op; Mc.frhs = e2}, env)
  | _ -> failwith "error : parse_arith(2)"

let parse_zarith = parse_arith parse_zop parse_zexpr
let parse_qarith = parse_arith parse_qop parse_qexpr
let parse_rarith = parse_arith parse_rop parse_rexpr

(* generic parsing of arithmetic expressions *)

let mkAND b f1 f2 = Mc.AND (b, f1, f2)
let mkOR b f1 f2 = Mc.OR (b, f1, f2)
let mkIff b f1 f2 = Mc.IFF (b, f1, f2)
let mkIMPL b f1 f2 = Mc.IMPL (b, f1, None, f2)
let mkEQ f1 f2 = Mc.EQ (f1, f2)

let mkformula_binary b g term f1 f2 =
  match (f1, f2) with
  | Mc.X (b1, _), Mc.X (b2, _) -> Mc.X (b, term)
  | _ -> g f1 f2

(**
    * This is the big generic function for formula parsers.
    *)

let is_prop env sigma term =
  let sort = Retyping.get_sort_of env sigma term in
  Sorts.is_prop sort

type formula_op =
  { op_impl : EConstr.t option (* only for booleans *)
  ; op_and : EConstr.t
  ; op_or : EConstr.t
  ; op_iff : EConstr.t
  ; op_not : EConstr.t
  ; op_tt : EConstr.t
  ; op_ff : EConstr.t }

let prop_op =
  lazy
    { op_impl = None (* implication is Prod *)
    ; op_and = Lazy.force coq_and
    ; op_or = Lazy.force coq_or
    ; op_iff = Lazy.force coq_iff
    ; op_not = Lazy.force coq_not
    ; op_tt = Lazy.force coq_True
    ; op_ff = Lazy.force coq_False }

let bool_op =
  lazy
    { op_impl = Some (Lazy.force coq_implb)
    ; op_and = Lazy.force coq_andb
    ; op_or = Lazy.force coq_orb
    ; op_iff = Lazy.force coq_eqb
    ; op_not = Lazy.force coq_negb
    ; op_tt = Lazy.force coq_true
    ; op_ff = Lazy.force coq_false }

let is_implb sigma l o =
  match o with None -> false | Some c -> EConstr.eq_constr sigma l c

let parse_formula (genv, sigma) parse_atom env tg term =
  let parse_atom b env tg t =
    try
      let at, env = parse_atom b env t (genv, sigma) in
      (Mc.A (b, at, (tg, t)), env, Tag.next tg)
    with ParseError -> (Mc.X (b, t), env, tg)
  in
  let prop_op = Lazy.force prop_op in
  let bool_op = Lazy.force bool_op in
  let eq = Lazy.force coq_eq in
  let bool = Lazy.force coq_bool in
  let rec xparse_formula op k env tg term =
    match EConstr.kind sigma term with
    | App (l, rst) -> (
      match rst with
      | [|a; b|] when is_implb sigma l op.op_impl ->
        let f, env, tg = xparse_formula op k env tg a in
        let g, env, tg = xparse_formula op k env tg b in
        (mkformula_binary k (mkIMPL k) term f g, env, tg)
      | [|a; b|] when EConstr.eq_constr sigma l op.op_and ->
        let f, env, tg = xparse_formula op k env tg a in
        let g, env, tg = xparse_formula op k env tg b in
        (mkformula_binary k (mkAND k) term f g, env, tg)
      | [|a; b|] when EConstr.eq_constr sigma l op.op_or ->
        let f, env, tg = xparse_formula op k env tg a in
        let g, env, tg = xparse_formula op k env tg b in
        (mkformula_binary k (mkOR k) term f g, env, tg)
      | [|a; b|] when EConstr.eq_constr sigma l op.op_iff ->
        let f, env, tg = xparse_formula op k env tg a in
        let g, env, tg = xparse_formula op k env tg b in
        (mkformula_binary k (mkIff k) term f g, env, tg)
      | [|ty; a; b|]
        when EConstr.eq_constr sigma l eq && is_convertible genv sigma ty bool
        ->
        let f, env, tg = xparse_formula bool_op Mc.IsBool env tg a in
        let g, env, tg = xparse_formula bool_op Mc.IsBool env tg b in
        (mkformula_binary Mc.IsProp mkEQ term f g, env, tg)
      | [|a|] when EConstr.eq_constr sigma l op.op_not ->
        let f, env, tg = xparse_formula op k env tg a in
        (Mc.NOT (k, f), env, tg)
      | _ -> parse_atom k env tg term )
    | Prod (typ, a, b)
      when kind_is_prop k
           && (typ.binder_name = Anonymous || EConstr.Vars.noccurn sigma 1 b) ->
      let f, env, tg = xparse_formula op k env tg a in
      let g, env, tg = xparse_formula op k env tg b in
      (mkformula_binary Mc.IsProp (mkIMPL Mc.IsProp) term f g, env, tg)
    | _ ->
      if EConstr.eq_constr sigma term op.op_tt then (Mc.TT k, env, tg)
      else if EConstr.eq_constr sigma term op.op_ff then Mc.(FF k, env, tg)
      else (Mc.X (k, term), env, tg)
  in
  xparse_formula prop_op Mc.IsProp env tg (*Reductionops.whd_zeta*) term

(*  let dump_bool b = Lazy.force (if b then coq_true else coq_false)*)

let undump_kind sigma k =
  if EConstr.eq_constr sigma k (Lazy.force coq_IsProp) then Mc.IsProp
  else Mc.IsBool

let dump_kind k =
  Lazy.force (match k with Mc.IsProp -> coq_IsProp | Mc.IsBool -> coq_IsBool)

let undump_formula undump_atom tg sigma f =
  let is c c' = EConstr.eq_constr sigma c (Lazy.force c') in
  let kind k = undump_kind sigma k in
  let rec xundump f =
    match EConstr.kind sigma f with
    | App (c, [|_; _; _; _; k|]) when is c coq_TT -> Mc.TT (kind k)
    | App (c, [|_; _; _; _; k|]) when is c coq_FF -> Mc.FF (kind k)
    | App (c, [|_; _; _; _; k; f1; f2|]) when is c coq_AND ->
      Mc.AND (kind k, xundump f1, xundump f2)
    | App (c, [|_; _; _; _; k; f1; f2|]) when is c coq_OR ->
      Mc.OR (kind k, xundump f1, xundump f2)
    | App (c, [|_; _; _; _; k; f1; _; f2|]) when is c coq_IMPL ->
      Mc.IMPL (kind k, xundump f1, None, xundump f2)
    | App (c, [|_; _; _; _; k; f|]) when is c coq_NOT ->
      Mc.NOT (kind k, xundump f)
    | App (c, [|_; _; _; _; k; f1; f2|]) when is c coq_IFF ->
      Mc.IFF (kind k, xundump f1, xundump f2)
    | App (c, [|_; _; _; _; f1; f2|]) when is c coq_EQ ->
      Mc.EQ (xundump f1, xundump f2)
    | App (c, [|_; _; _; _; k; x; _|]) when is c coq_Atom ->
      Mc.A (kind k, undump_atom sigma x, tg)
    | App (c, [|_; _; _; _; k; x|]) when is c coq_X ->
      Mc.X (kind k, x)
    | _ -> raise ParseError
  in
  xundump f

let dump_formula typ dump_atom f =
  let app_ctor c args =
    EConstr.mkApp
      ( Lazy.force c
      , Array.of_list
          ( typ :: Lazy.force coq_eKind :: Lazy.force coq_unit
          :: Lazy.force coq_unit :: args ) )
  in
  let rec xdump f =
    match f with
    | Mc.TT k -> app_ctor coq_TT [dump_kind k]
    | Mc.FF k -> app_ctor coq_FF [dump_kind k]
    | Mc.AND (k, x, y) -> app_ctor coq_AND [dump_kind k; xdump x; xdump y]
    | Mc.OR (k, x, y) -> app_ctor coq_OR [dump_kind k; xdump x; xdump y]
    | Mc.IMPL (k, x, _, y) ->
      app_ctor coq_IMPL
        [ dump_kind k
        ; xdump x
        ; EConstr.mkApp (Lazy.force coq_None, [|Lazy.force coq_unit|])
        ; xdump y ]
    | Mc.NOT (k, x) -> app_ctor coq_NOT [dump_kind k; xdump x]
    | Mc.IFF (k, x, y) -> app_ctor coq_IFF [dump_kind k; xdump x; xdump y]
    | Mc.EQ (x, y) -> app_ctor coq_EQ [xdump x; xdump y]
    | Mc.A (k, x, _) ->
      app_ctor coq_Atom [dump_kind k; dump_atom x; Lazy.force coq_tt]
    | Mc.X (k, t) -> app_ctor coq_X [dump_kind k; t]
  in
  xdump f

let prop_env_of_formula gl form =
  Mc.(
    let rec doit env = function
      | TT _ | FF _ | A (_, _, _) -> env
      | X (b, t) -> fst (Env.compute_rank_add env t b)
      | AND (b, f1, f2) | OR (b, f1, f2) | IMPL (b, f1, _, f2) | IFF (b, f1, f2)
        ->
        doit (doit env f1) f2
      | NOT (b, f) -> doit env f
      | EQ (f1, f2) -> doit (doit env f1) f2
    in
    doit (Env.empty gl) form)

let var_env_of_formula form =
  let rec vars_of_expr = function
    | Mc.PEX n -> ISet.singleton (CoqToCaml.positive n)
    | Mc.PEc z -> ISet.empty
    | Mc.PEadd (e1, e2) | Mc.PEmul (e1, e2) | Mc.PEsub (e1, e2) ->
      ISet.union (vars_of_expr e1) (vars_of_expr e2)
    | Mc.PEopp e | Mc.PEpow (e, _) -> vars_of_expr e
  in
  let vars_of_atom {Mc.flhs; Mc.fop; Mc.frhs} =
    ISet.union (vars_of_expr flhs) (vars_of_expr frhs)
  in
  Mc.(
    let rec doit = function
      | TT _ | FF _ | X _ -> ISet.empty
      | A (_, a, (t, c)) -> vars_of_atom a
      | AND (_, f1, f2)
       |OR (_, f1, f2)
       |IMPL (_, f1, _, f2)
       |IFF (_, f1, f2)
       |EQ (f1, f2) ->
        ISet.union (doit f1) (doit f2)
      | NOT (_, f) -> doit f
    in
    doit form)

type 'cst dump_expr =
  { (* 'cst is the type of the syntactic constants *)
    interp_typ : EConstr.constr
  ; dump_cst : 'cst -> EConstr.constr
  ; dump_add : EConstr.constr
  ; dump_sub : EConstr.constr
  ; dump_opp : EConstr.constr
  ; dump_mul : EConstr.constr
  ; dump_pow : EConstr.constr
  ; dump_pow_arg : Mc.n -> EConstr.constr
  ; dump_op_prop : (Mc.op2 * EConstr.constr) list
  ; dump_op_bool : (Mc.op2 * EConstr.constr) list }

let dump_zexpr =
  lazy
    { interp_typ = Lazy.force coq_Z
    ; dump_cst = dump_z
    ; dump_add = Lazy.force coq_Zplus
    ; dump_sub = Lazy.force coq_Zminus
    ; dump_opp = Lazy.force coq_Zopp
    ; dump_mul = Lazy.force coq_Zmult
    ; dump_pow = Lazy.force coq_Zpower
    ; dump_pow_arg = (fun n -> dump_z (CamlToCoq.z (CoqToCaml.n n)))
    ; dump_op_prop = List.map (fun (x, y) -> (y, Lazy.force x)) zop_table_prop
    ; dump_op_bool = List.map (fun (x, y) -> (y, Lazy.force x)) zop_table_bool
    }

let dump_qexpr =
  lazy
    { interp_typ = Lazy.force coq_Q
    ; dump_cst = dump_q
    ; dump_add = Lazy.force coq_Qplus
    ; dump_sub = Lazy.force coq_Qminus
    ; dump_opp = Lazy.force coq_Qopp
    ; dump_mul = Lazy.force coq_Qmult
    ; dump_pow = Lazy.force coq_Qpower
    ; dump_pow_arg = (fun n -> dump_z (CamlToCoq.z (CoqToCaml.n n)))
    ; dump_op_prop = List.map (fun (x, y) -> (y, Lazy.force x)) qop_table_prop
    ; dump_op_bool = List.map (fun (x, y) -> (y, Lazy.force x)) qop_table_bool
    }

let rec dump_Rcst_as_R cst =
  match cst with
  | Mc.C0 -> Lazy.force coq_R0
  | Mc.C1 -> Lazy.force coq_R1
  | Mc.CQ q -> EConstr.mkApp (Lazy.force coq_IQR, [|dump_q q|])
  | Mc.CZ z -> EConstr.mkApp (Lazy.force coq_IZR, [|dump_z z|])
  | Mc.CPlus (x, y) ->
    EConstr.mkApp (Lazy.force coq_Rplus, [|dump_Rcst_as_R x; dump_Rcst_as_R y|])
  | Mc.CMinus (x, y) ->
    EConstr.mkApp (Lazy.force coq_Rminus, [|dump_Rcst_as_R x; dump_Rcst_as_R y|])
  | Mc.CMult (x, y) ->
    EConstr.mkApp (Lazy.force coq_Rmult, [|dump_Rcst_as_R x; dump_Rcst_as_R y|])
  | Mc.CPow (x, y) -> (
    match y with
    | Mc.Inl z ->
      EConstr.mkApp (Lazy.force coq_powerZR, [|dump_Rcst_as_R x; dump_z z|])
    | Mc.Inr n ->
      EConstr.mkApp (Lazy.force coq_Rpower, [|dump_Rcst_as_R x; dump_nat n|]) )
  | Mc.CInv t -> EConstr.mkApp (Lazy.force coq_Rinv, [|dump_Rcst_as_R t|])
  | Mc.COpp t -> EConstr.mkApp (Lazy.force coq_Ropp, [|dump_Rcst_as_R t|])

let dump_rexpr =
  lazy
    { interp_typ = Lazy.force coq_R
    ; dump_cst = dump_Rcst_as_R
    ; dump_add = Lazy.force coq_Rplus
    ; dump_sub = Lazy.force coq_Rminus
    ; dump_opp = Lazy.force coq_Ropp
    ; dump_mul = Lazy.force coq_Rmult
    ; dump_pow = Lazy.force coq_Rpower
    ; dump_pow_arg = (fun n -> dump_nat (CamlToCoq.nat (CoqToCaml.n n)))
    ; dump_op_prop = List.map (fun (x, y) -> (y, Lazy.force x)) rop_table_prop
    ; dump_op_bool = List.map (fun (x, y) -> (y, Lazy.force x)) rop_table_bool
    }

let prodn n env b =
  let rec prodrec = function
    | 0, env, b -> b
    | n, (v, t) :: l, b ->
      prodrec (n - 1, l, EConstr.mkProd (make_annot v Sorts.Relevant, t, b))
    | _ -> assert false
  in
  prodrec (n, env, b)

(** [make_goal_of_formula depxr vars props form] where
     - vars is an environment for the arithmetic variables occurring in form
     - props is an environment for the propositions occurring in form
    @return a goal where all the variables and propositions of the formula are quantified

*)

let eKind = function
  | Mc.IsProp -> EConstr.mkProp
  | Mc.IsBool -> Lazy.force coq_bool

let make_goal_of_formula gl dexpr form =
  let vars_idx =
    List.mapi (fun i v -> (v, i + 1)) (ISet.elements (var_env_of_formula form))
  in
  (*  List.iter (fun (v,i) -> Printf.fprintf stdout "var %i has index %i\n" v i) vars_idx ;*)
  let props = prop_env_of_formula gl form in
  let fresh_var str i = Names.Id.of_string (str ^ string_of_int i) in
  let fresh_prop str i = Names.Id.of_string (str ^ string_of_int i) in
  let vars_n =
    List.map (fun (_, i) -> (fresh_var "__x" i, dexpr.interp_typ)) vars_idx
  in
  let props_n =
    List.mapi
      (fun i (_, k) -> (fresh_prop "__p" (i + 1), eKind k))
      (Env.elements props)
  in
  let var_name_pos =
    List.map2 (fun (idx, _) (id, _) -> (id, idx)) vars_idx vars_n
  in
  let dump_expr i e =
    let rec dump_expr = function
      | Mc.PEX n ->
        EConstr.mkRel (i + List.assoc (CoqToCaml.positive n) vars_idx)
      | Mc.PEc z -> dexpr.dump_cst z
      | Mc.PEadd (e1, e2) ->
        EConstr.mkApp (dexpr.dump_add, [|dump_expr e1; dump_expr e2|])
      | Mc.PEsub (e1, e2) ->
        EConstr.mkApp (dexpr.dump_sub, [|dump_expr e1; dump_expr e2|])
      | Mc.PEopp e -> EConstr.mkApp (dexpr.dump_opp, [|dump_expr e|])
      | Mc.PEmul (e1, e2) ->
        EConstr.mkApp (dexpr.dump_mul, [|dump_expr e1; dump_expr e2|])
      | Mc.PEpow (e, n) ->
        EConstr.mkApp (dexpr.dump_pow, [|dump_expr e; dexpr.dump_pow_arg n|])
    in
    dump_expr e
  in
  let mkop_prop op e1 e2 =
    try EConstr.mkApp (List.assoc op dexpr.dump_op_prop, [|e1; e2|])
    with Not_found ->
      EConstr.mkApp (Lazy.force coq_eq, [|dexpr.interp_typ; e1; e2|])
  in
  let dump_cstr_prop i {Mc.flhs; Mc.fop; Mc.frhs} =
    mkop_prop fop (dump_expr i flhs) (dump_expr i frhs)
  in
  let mkop_bool op e1 e2 =
    try EConstr.mkApp (List.assoc op dexpr.dump_op_bool, [|e1; e2|])
    with Not_found ->
      EConstr.mkApp (Lazy.force coq_eq, [|dexpr.interp_typ; e1; e2|])
  in
  let dump_cstr_bool i {Mc.flhs; Mc.fop; Mc.frhs} =
    mkop_bool fop (dump_expr i flhs) (dump_expr i frhs)
  in
  let rec xdump_prop pi xi f =
    match f with
    | Mc.TT _ -> Lazy.force coq_True
    | Mc.FF _ -> Lazy.force coq_False
    | Mc.AND (_, x, y) ->
      EConstr.mkApp
        (Lazy.force coq_and, [|xdump_prop pi xi x; xdump_prop pi xi y|])
    | Mc.OR (_, x, y) ->
      EConstr.mkApp
        (Lazy.force coq_or, [|xdump_prop pi xi x; xdump_prop pi xi y|])
    | Mc.IFF (_, x, y) ->
      EConstr.mkApp
        (Lazy.force coq_iff, [|xdump_prop pi xi x; xdump_prop pi xi y|])
    | Mc.IMPL (_, x, _, y) ->
      EConstr.mkArrow (xdump_prop pi xi x) Sorts.Relevant
        (xdump_prop (pi + 1) (xi + 1) y)
    | Mc.NOT (_, x) ->
      EConstr.mkArrow (xdump_prop pi xi x) Sorts.Relevant (Lazy.force coq_False)
    | Mc.EQ (x, y) ->
      EConstr.mkApp
        ( Lazy.force coq_eq
        , [|Lazy.force coq_bool; xdump_bool pi xi x; xdump_bool pi xi y|] )
    | Mc.A (_, x, _) -> dump_cstr_prop xi x
    | Mc.X (_, t) ->
      let idx = Env.get_rank props t in
      EConstr.mkRel (pi + idx)
  and xdump_bool pi xi f =
    match f with
    | Mc.TT _ -> Lazy.force coq_true
    | Mc.FF _ -> Lazy.force coq_false
    | Mc.AND (_, x, y) ->
      EConstr.mkApp
        (Lazy.force coq_andb, [|xdump_bool pi xi x; xdump_bool pi xi y|])
    | Mc.OR (_, x, y) ->
      EConstr.mkApp
        (Lazy.force coq_orb, [|xdump_bool pi xi x; xdump_bool pi xi y|])
    | Mc.IFF (_, x, y) ->
      EConstr.mkApp
        (Lazy.force coq_eqb, [|xdump_bool pi xi x; xdump_bool pi xi y|])
    | Mc.IMPL (_, x, _, y) ->
      EConstr.mkApp
        (Lazy.force coq_implb, [|xdump_bool pi xi x; xdump_bool pi xi y|])
    | Mc.NOT (_, x) ->
      EConstr.mkApp (Lazy.force coq_negb, [|xdump_bool pi xi x|])
    | Mc.EQ (x, y) -> assert false
    | Mc.A (_, x, _) -> dump_cstr_bool xi x
    | Mc.X (_, t) ->
      let idx = Env.get_rank props t in
      EConstr.mkRel (pi + idx)
  in
  let nb_vars = List.length vars_n in
  let nb_props = List.length props_n in
  (*  Printf.fprintf stdout "NBProps : %i\n" nb_props ;*)
  let subst_prop p =
    let idx = Env.get_rank props p in
    EConstr.mkVar (Names.Id.of_string (Printf.sprintf "__p%i" idx))
  in
  let form' = Mc.mapX (fun _ p -> subst_prop p) Mc.IsProp form in
  ( prodn nb_props
      (List.map (fun (x, y) -> (Name.Name x, y)) props_n)
      (prodn nb_vars
         (List.map (fun (x, y) -> (Name.Name x, y)) vars_n)
         (xdump_prop (List.length vars_n) 0 form))
  , List.rev props_n
  , List.rev var_name_pos
  , form' )

(**
     * Given a conclusion and a list of affectations, rebuild a term prefixed by
     * the appropriate letins.
     * TODO: reverse the list of bindings!
  *)

let set l concl =
  let rec xset acc = function
    | [] -> acc
    | e :: l ->
      let name, expr, typ = e in
      xset
        (EConstr.mkNamedLetIn
           (make_annot (Names.Id.of_string name) Sorts.Relevant)
           expr typ acc)
        l
  in
  xset concl l

let coq_Branch = lazy (constr_of_ref "micromega.VarMap.Branch")
let coq_Elt = lazy (constr_of_ref "micromega.VarMap.Elt")
let coq_Empty = lazy (constr_of_ref "micromega.VarMap.Empty")
let coq_VarMap = lazy (constr_of_ref "micromega.VarMap.type")

let rec dump_varmap typ m =
  match m with
  | Mc.Empty -> EConstr.mkApp (Lazy.force coq_Empty, [|typ|])
  | Mc.Elt v -> EConstr.mkApp (Lazy.force coq_Elt, [|typ; v|])
  | Mc.Branch (l, o, r) ->
    EConstr.mkApp
      (Lazy.force coq_Branch, [|typ; dump_varmap typ l; o; dump_varmap typ r|])

let vm_of_list env =
  match env with
  | [] -> Mc.Empty
  | (d, _) :: _ ->
    List.fold_left
      (fun vm (c, i) -> Mc.vm_add d (CamlToCoq.positive i) c vm)
      Mc.Empty env

let rec dump_proof_term = function
  | Micromega.DoneProof -> Lazy.force coq_doneProof
  | Micromega.RatProof (cone, rst) ->
    EConstr.mkApp
      ( Lazy.force coq_ratProof
      , [|dump_psatz coq_Z dump_z cone; dump_proof_term rst|] )
  | Micromega.CutProof (cone, prf) ->
    EConstr.mkApp
      ( Lazy.force coq_cutProof
      , [|dump_psatz coq_Z dump_z cone; dump_proof_term prf|] )
  | Micromega.SplitProof (p, prf1, prf2) ->
    EConstr.mkApp
      ( Lazy.force coq_splitProof
      , [| dump_pol (Lazy.force coq_Z) dump_z p
         ; dump_proof_term prf1
         ; dump_proof_term prf2 |] )
  | Micromega.EnumProof (c1, c2, prfs) ->
    EConstr.mkApp
      ( Lazy.force coq_enumProof
      , [| dump_psatz coq_Z dump_z c1
         ; dump_psatz coq_Z dump_z c2
         ; dump_list (Lazy.force coq_proofTerm) dump_proof_term prfs |] )
  | Micromega.ExProof (p, prf) ->
    EConstr.mkApp
      (Lazy.force coq_ExProof, [|dump_positive p; dump_proof_term prf|])

let rec size_of_psatz = function
  | Micromega.PsatzIn _ -> 1
  | Micromega.PsatzSquare _ -> 1
  | Micromega.PsatzMulC (_, p) -> 1 + size_of_psatz p
  | Micromega.PsatzLet (p1, p2)
   |Micromega.PsatzMulE (p1, p2)
   |Micromega.PsatzAdd (p1, p2) ->
    size_of_psatz p1 + size_of_psatz p2
  | Micromega.PsatzC _ -> 1
  | Micromega.PsatzZ -> 1

let rec size_of_pf = function
  | Micromega.DoneProof -> 1
  | Micromega.RatProof (p, a) -> size_of_pf a + size_of_psatz p
  | Micromega.CutProof (p, a) -> size_of_pf a + size_of_psatz p
  | Micromega.SplitProof (_, p1, p2) -> size_of_pf p1 + size_of_pf p2
  | Micromega.EnumProof (p1, p2, l) ->
    size_of_psatz p1 + size_of_psatz p2
    + List.fold_left (fun acc p -> size_of_pf p + acc) 0 l
  | Micromega.ExProof (_, a) -> size_of_pf a + 1

let dump_proof_term t =
  if debug then Printf.printf "dump_proof_term %i\n" (size_of_pf t);
  dump_proof_term t

let pp_q o q =
  Printf.fprintf o "%a/%a" pp_z q.Micromega.qnum pp_positive q.Micromega.qden


let rec parse_hyps (genv, sigma) parse_arith env tg hyps =
  match hyps with
  | [] -> ([], env, tg)
  | (i, t) :: l ->
    let lhyps, env, tg = parse_hyps (genv, sigma) parse_arith env tg l in
    if is_prop genv sigma t then
      try
        let c, env, tg = parse_formula (genv, sigma) parse_arith env tg t in
        ((i, c) :: lhyps, env, tg)
      with ParseError -> (lhyps, env, tg)
    else (lhyps, env, tg)

let parse_goal gl parse_arith (env : Env.t) hyps term =
  let f, env, tg = parse_formula gl parse_arith env (Tag.from 0) term in
  let lhyps, env, tg = parse_hyps gl parse_arith env tg hyps in
  (lhyps, f, env)

(**
  * The datastructures that aggregate theory-dependent proof values.
  *)
type ('synt_c, 'prf) domain_spec =
  { typ : EConstr.constr
  ; (* is the type of the interpretation domain - Z, Q, R*)
    coeff : EConstr.constr
  ; (* is the type of the syntactic coeffs - Z , Q , Rcst *)
    dump_coeff : 'synt_c -> EConstr.constr
  ; undump_coeff : Evd.evar_map -> EConstr.constr -> 'synt_c
  ; proof_typ : EConstr.constr
  ; dump_proof : 'prf -> EConstr.constr
  ; coeff_eq : 'synt_c -> 'synt_c -> bool }

let zz_domain_spec =
  lazy
    { typ = Lazy.force coq_Z
    ; coeff = Lazy.force coq_Z
    ; dump_coeff = dump_z
    ; undump_coeff = parse_z
    ; proof_typ = Lazy.force coq_proofTerm
    ; dump_proof = dump_proof_term
    ; coeff_eq = Mc.zeq_bool }

let qq_domain_spec =
  lazy
    { typ = Lazy.force coq_Q
    ; coeff = Lazy.force coq_Q
    ; dump_coeff = dump_q
    ; undump_coeff = parse_q
    ; proof_typ = Lazy.force coq_QWitness
    ; dump_proof = dump_psatz coq_Q dump_q
    ; coeff_eq = Mc.qeq_bool }

let max_tag f =
  1
  + Tag.to_int
      (Mc.foldA (fun t1 (t2, _) -> Tag.max t1 t2) Mc.IsProp f (Tag.from 0))

(** Naive topological sort of constr according to the subterm-ordering *)

(* An element is minimal x is minimal w.r.t y if
   x <= y or (x and y are incomparable) *)

(**
  * Instantiate the current Coq goal with a Micromega formula, a varmap, and a
  * witness.
  *)

let micromega_order_change spec cert cert_typ env ff (*: unit Proofview.tactic*)
    =
  (* let ids = Util.List.map_i (fun i _ -> (Names.Id.of_string ("__v"^(string_of_int i)))) 0 env in *)
  let formula_typ = EConstr.mkApp (Lazy.force coq_Cstr, [|spec.coeff|]) in
  let ff = dump_formula formula_typ (dump_cstr spec.coeff spec.dump_coeff) ff in
  let vm = dump_varmap spec.typ (vm_of_list env) in
  (* todo : directly generate the proof term - or generalize before conversion? *)
  Proofview.Goal.enter (fun gl ->
      Tacticals.tclTHENLIST
        [ Tactics.change_concl
            (set
               [ ( "__ff"
                 , ff
                 , EConstr.mkApp
                     ( Lazy.force coq_Formula
                     , [|formula_typ; Lazy.force coq_IsProp|] ) )
               ; ( "__varmap"
                 , vm
                 , EConstr.mkApp (Lazy.force coq_VarMap, [|spec.typ|]) )
               ; ("__wit", cert, cert_typ) ]
               (Tacmach.pf_concl gl)) ])

(**
  * The datastructures that aggregate prover attributes.
  *)

open Certificate

type ('option, 'a, 'prf, 'model) prover =
  { name : string
  ; (* name of the prover *)
    get_option : unit -> 'option
  ; (* find the options of the prover *)
    prover : 'option * 'a list -> ('prf, 'model) Certificate.res
  ; (* the prover itself *)
    hyps : 'prf -> ISet.t
  ; (* extract the indexes of the hypotheses really used in the proof *)
    compact : 'prf -> (int -> int) -> 'prf
  ; (* remap the hyp indexes according to function *)
    pp_prf : out_channel -> 'prf -> unit
  ; (* pretting printing of proof *)
    pp_f : out_channel -> 'a -> unit
        (* pretty printing of the formulas (polynomials)*) }

(**
  * Given a  prover and a disjunction of atoms, find a proof of any of
  * the atoms.  Returns an (optional) pair of a proof and a prover
  * datastructure.
  *)

let find_witness p polys1 =
  try
  let polys1 = List.map fst polys1 in
  p.prover (p.get_option (), polys1)
  with e ->
    begin
    Printf.printf "find_witness %s" (Printexc.to_string e);
    raise e
  end

(**
  * Given a prover and a CNF, find a proof for each of the clauses.
  * Return the proofs as a list.
  *)

let witness_list prover l =
  let rec xwitness_list l =
    match l with
    | [] -> Prf []
    | e :: l -> (
      match xwitness_list l with
      | Model (m, e) -> Model (m, e)
      | Unknown -> Unknown
      | Prf l -> (
        match find_witness prover e with
        | Model m -> Model (m, e)
        | Unknown -> Unknown
        | Prf w -> Prf (w :: l) ) )
  in
  xwitness_list l

(*  let t1 = System.get_time () in
  let res = witness_list p g in
  let t2 = System.get_time () in
  Feedback.msg_info Pp.(str "Witness generation "++int (List.length g) ++ str " "++System.fmt_time_difference t1 t2) ;
  res
 *)

(**
  * Prune the proof object, according to the 'diff' between two cnf formulas.
  *)

let compact_proofs prover (eq_cst : 'cst -> 'cst -> bool) (cnf_ff : 'cst cnf) res
    (cnf_ff' : 'cst cnf) =
  let eq_formula (p1, o1) (p2, o2) =
    let open Mutils.Hash in
    eq_pol eq_cst p1 p2 && eq_op1 o1 o2
  in
  let compact_proof (old_cl : 'cst clause) prf (new_cl : 'cst clause)
      =
    let new_cl = List.mapi (fun i (f, _) -> (f, i)) new_cl in
    let remap i =
      let formula =
        try fst (List.nth old_cl i) with Failure _ -> failwith "bad old index"
      in
      CList.assoc_f eq_formula formula new_cl
    in
    (* if debug then
       begin
         Printf.printf "\ncompact_proof : %a %a %a"
           (pp_ml_list prover.pp_f) (List.map fst old_cl)
           prover.pp_prf prf
           (pp_ml_list prover.pp_f) (List.map fst new_cl)   ;
           flush stdout
       end ; *)
    let res =
      try prover.compact prf remap
      with x when CErrors.noncritical x -> (
        if debug then
          Printf.fprintf stdout "Proof compaction %s" (Printexc.to_string x);
        (* This should not happen -- this is the recovery plan... *)
        match prover.prover (prover.get_option (), List.map fst new_cl) with
        | Unknown | Model _ -> failwith "proof compaction error"
        | Prf p -> p )
    in
    if debug then begin
      Printf.printf " -> %a\n" prover.pp_prf res;
      flush stdout
    end;
    res
  in
  let is_proof_compatible (hyps, (old_cl : 'cst clause), prf) (new_cl : 'cst clause) =
    let eq (f1, (t1, e1)) (f2, (t2, e2)) =
      Int.equal (Tag.compare t1 t2) 0
      && eq_formula f1 f2
      (* We do not have to compare [e1] with [e2] because [t1 = t2] ensures
         by uid generation that they must be the same *)
    in
    is_sublist eq (Lazy.force hyps) new_cl
  in
  let map cl prf =
    let hyps = lazy (selecti (prover.hyps prf) cl) in
    hyps, cl, prf
  in
  let cnf_res = List.map2 map cnf_ff res in
  (* we get pairs clause * proof *)
  if debug then begin
    Printf.printf "CNFRES\n";
    flush stdout;
    Printf.printf "CNFOLD %a\n" pp_cnf_tag cnf_ff;
    List.iter
      (fun (lazy hyps, cl, prf) ->
        Printf.printf "\nProver %a -> %a\n" pp_clause_tag cl pp_clause_tag hyps;
        flush stdout)
      cnf_res;
    Printf.printf "CNFNEW %a\n" pp_cnf_tag cnf_ff'
  end;
  List.map
    (fun x ->
      let _, o, p =
        try List.find (fun p -> is_proof_compatible p x) cnf_res
        with Not_found ->
          Printf.printf "ERROR: no compatible proof";
          flush stdout;
          failwith "Cannot find compatible proof"
      in
      compact_proof o p x)
    cnf_ff'

(**
  * "Hide out" tagged atoms of a formula by transforming them into generic
  * variables. See the Tag module in mutils.ml for more.
  *)

let abstract_formula : TagSet.t -> 'a formula -> 'a formula =
 fun hyps f ->
  let to_constr =
    Mc.
      { mkTT =
          (let coq_True = Lazy.force coq_True in
           let coq_true = Lazy.force coq_true in
           function Mc.IsProp -> coq_True | Mc.IsBool -> coq_true)
      ; mkFF =
          (let coq_False = Lazy.force coq_False in
           let coq_false = Lazy.force coq_false in
           function Mc.IsProp -> coq_False | Mc.IsBool -> coq_false)
      ; mkA = (fun k a (tg, t) -> t)
      ; mkAND =
          (let coq_and = Lazy.force coq_and in
           let coq_andb = Lazy.force coq_andb in
           fun k x y ->
             EConstr.mkApp
               ( (match k with Mc.IsProp -> coq_and | Mc.IsBool -> coq_andb)
               , [|x; y|] ))
      ; mkOR =
          (let coq_or = Lazy.force coq_or in
           let coq_orb = Lazy.force coq_orb in
           fun k x y ->
             EConstr.mkApp
               ( (match k with Mc.IsProp -> coq_or | Mc.IsBool -> coq_orb)
               , [|x; y|] ))
      ; mkIMPL =
          (fun k x y ->
            match k with
            | Mc.IsProp -> EConstr.mkArrow x Sorts.Relevant y
            | Mc.IsBool -> EConstr.mkApp (Lazy.force coq_implb, [|x; y|]))
      ; mkIFF =
          (let coq_iff = Lazy.force coq_iff in
           let coq_eqb = Lazy.force coq_eqb in
           fun k x y ->
             EConstr.mkApp
               ( (match k with Mc.IsProp -> coq_iff | Mc.IsBool -> coq_eqb)
               , [|x; y|] ))
      ; mkNOT =
          (let coq_not = Lazy.force coq_not in
           let coq_negb = Lazy.force coq_negb in
           fun k x ->
             EConstr.mkApp
               ( (match k with Mc.IsProp -> coq_not | Mc.IsBool -> coq_negb)
               , [|x|] ))
      ; mkEQ =
          (let coq_eq = Lazy.force coq_eq in
           fun x y -> EConstr.mkApp (coq_eq, [|Lazy.force coq_bool; x; y|])) }
  in
  Mc.abst_form to_constr (fun (t, _) -> TagSet.mem t hyps) true Mc.IsProp f

(* [abstract_wrt_formula] is used in contexts whre f1 is already an abstraction of f2   *)
let rec abstract_wrt_formula f1 f2 =
  Mc.(
    match (f1, f2) with
    | X (b, c), _ -> X (b, c)
    | A _, A _ -> f2
    | AND (b, f1, f2), AND (_, f1', f2') ->
      AND (b, abstract_wrt_formula f1 f1', abstract_wrt_formula f2 f2')
    | OR (b, f1, f2), OR (_, f1', f2') ->
      OR (b, abstract_wrt_formula f1 f1', abstract_wrt_formula f2 f2')
    | IMPL (b, f1, _, f2), IMPL (_, f1', x, f2') ->
      IMPL (b, abstract_wrt_formula f1 f1', x, abstract_wrt_formula f2 f2')
    | IFF (b, f1, f2), IFF (_, f1', f2') ->
      IFF (b, abstract_wrt_formula f1 f1', abstract_wrt_formula f2 f2')
    | EQ (f1, f2), EQ (f1', f2') ->
      EQ (abstract_wrt_formula f1 f1', abstract_wrt_formula f2 f2')
    | FF b, FF _ -> FF b
    | TT b, TT _ -> TT b
    | NOT (b, x), NOT (_, y) -> NOT (b, abstract_wrt_formula x y)
    | _ -> failwith "abstract_wrt_formula")

(**
  * This exception is raised by really_call_csdpcert if Coq's configure didn't
  * find a CSDP executable.
  *)

exception CsdpNotFound

let fail_csdp_not_found () =
  flush stdout;
  let s =
    "Skipping the rest of this tactic: the complexity of the \
     goal requires the use of an external tool called CSDP. \n\n\
     However, the \"csdp\" binary is not present in the search path. \n\n\
     Some OS distributions include CSDP (package \"coinor-csdp\" on Debian \
     for instance). You can download binaries \
     and source code from <https://github.com/coin-or/csdp>." in
  Tacticals.tclFAIL (Pp.str s)

(**
  * This is the core of Micromega: apply the prover, analyze the result and
  * prune unused fomulas, and finally modify the proof state.
  *)

let formula_hyps_concl hyps concl =
  List.fold_right
    (fun (id, f) (cc, ids) ->
      match f with
      | Mc.X _ -> (cc, ids)
      | _ -> (Mc.IMPL (Mc.IsProp, f, Some id, cc), id :: ids))
    hyps (concl, [])

(* let time str f x =
  let t1 = System.get_time () in
  let res = f x in
  let t2 = System.get_time () in
  Feedback.msg_info (Pp.str str ++ Pp.str " " ++ System.fmt_time_difference t1 t2) ;
  res
 *)

let rec fold_trace f accu = function
  | Micromega.Null -> accu
  | Micromega.Merge (t1, t2) -> fold_trace f (fold_trace f accu t1) t2
  | Micromega.Push (x, t) -> fold_trace f (f accu x) t

let micromega_tauto ?(abstract=true) pre_process cnf spec prover
    (polys1 : (Names.Id.t * 'cst formula) list) (polys2 : 'cst formula) =
  (* Express the goal as one big implication *)
  let ff, ids = formula_hyps_concl polys1 polys2 in
  let mt = CamlToCoq.positive (max_tag ff) in
  (* Construction of cnf *)
  let pre_ff = pre_process mt (ff : 'a formula) in
  let cnf_ff, cnf_ff_tags = cnf Mc.IsProp pre_ff in
  match witness_list prover cnf_ff with
  | Model m -> Model m
  | Unknown -> Unknown
  | Prf res ->
    (*Printf.printf "\nList %i" (List.length `res); *)
    let deps =
      List.fold_left
        (fun s (cl, prf) ->
          let tags =
            ISet.fold
              (fun i s ->
                let t = fst (snd (List.nth cl i)) in
                if debug then Printf.fprintf stdout "T : %i -> %a" i Tag.pp t;
                (*try*) TagSet.add t s
                (* with Invalid_argument _ -> s*))
              (prover.hyps prf) TagSet.empty
          in
          TagSet.union s tags)
        (fold_trace (fun s (i, _) -> TagSet.add i s) TagSet.empty cnf_ff_tags)
        (List.combine cnf_ff res)
    in
    let ff' = if abstract then abstract_formula deps ff else ff in
    let pre_ff' = pre_process mt ff' in
    let cnf_ff', _ = cnf Mc.IsProp pre_ff' in
    if debug then begin
      output_string stdout "\n";
      Printf.printf "TForm    : %a\n" pp_formula ff;
      flush stdout;
      Printf.printf "CNF    : %a\n" pp_cnf_tag cnf_ff;
      flush stdout;
      Printf.printf "TFormAbs : %a\n" pp_formula ff';
      flush stdout;
      Printf.printf "TFormPre : %a\n" pp_formula pre_ff;
      flush stdout;
      Printf.printf "TFormPreAbs : %a\n" pp_formula pre_ff';
      flush stdout;
      Printf.printf "CNF    : %a\n" pp_cnf_tag cnf_ff';
      flush stdout
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
    let res' = compact_proofs prover spec.coeff_eq cnf_ff res cnf_ff' in
    let ff', res', ids = (ff', res', Mc.ids_of_formula Mc.IsProp ff') in
    let res' = dump_list spec.proof_typ spec.dump_proof res' in
    Prf (ids, ff', res')

let micromega_tauto ?abstract pre_process cnf spec prover
    (polys1 : (Names.Id.t * 'cst formula) list) (polys2 : 'cst formula) =
  try micromega_tauto ?abstract pre_process cnf spec prover polys1 polys2
  with Not_found ->
    Printexc.print_backtrace stdout;
    flush stdout;
    Unknown

(**
  * Parse the proof environment, and call micromega_tauto
  *)
let fresh_id avoid id gl =
  Tactics.fresh_id_in_env avoid id (Proofview.Goal.env gl)

let clear_all_no_check =
  Proofview.Goal.enter (fun gl ->
      let concl = Tacmach.pf_concl gl in
      let env =
        Environ.reset_with_named_context Environ.empty_named_context_val
          (Tacmach.pf_env gl)
      in
      Refine.refine ~typecheck:false (fun sigma ->
          Evarutil.new_evar env sigma ~principal:true concl))

let micromega_gen parse_arith pre_process cnf spec dumpexpr prover tac =
  Proofview.Goal.enter (fun gl ->
      let sigma = Tacmach.project gl in
      let genv = Tacmach.pf_env gl in
      let concl = Tacmach.pf_concl gl in
      let hyps = Tacmach.pf_hyps_types gl in
      try
        let hyps, concl, env =
          parse_goal (genv, sigma) parse_arith
            (Env.empty (genv, sigma))
            hyps concl
        in
        let env = Env.elements env in
        let spec = Lazy.force spec in
        let dumpexpr = Lazy.force dumpexpr in
        if debug then
          Feedback.msg_debug (Pp.str "Env " ++ Env.pp (genv, sigma) env);
        match
          micromega_tauto pre_process cnf spec prover hyps concl
        with
        | Unknown ->
          flush stdout;
          Tacticals.tclFAIL (Pp.str " Cannot find witness")
        | Model (m, e) ->
          Tacticals.tclFAIL (Pp.str " Cannot find witness")
        | Prf (ids, ff', res') ->
          let arith_goal, props, vars, ff_arith =
            make_goal_of_formula (genv, sigma) dumpexpr ff'
          in
          let intro (id, _) = Tactics.introduction id in
          let intro_vars = Tacticals.tclTHENLIST (List.map intro vars) in
          let intro_props = Tacticals.tclTHENLIST (List.map intro props) in
          (*       let ipat_of_name id = Some (CAst.make @@ IntroNaming (Namegen.IntroIdentifier id)) in*)
          let goal_name =
            fresh_id Id.Set.empty (Names.Id.of_string "__arith") gl
          in
          let env' = List.map (fun (id, i) -> (EConstr.mkVar id, i)) vars in
          let tac_arith =
            Tacticals.tclTHENLIST
              [ clear_all_no_check
              ; intro_props
              ; intro_vars
              ; micromega_order_change spec res'
                  (EConstr.mkApp (Lazy.force coq_list, [|spec.proof_typ|]))
                  env' ff_arith ]
          in
          let goal_props =
            List.rev
              (List.map fst
                 (Env.elements (prop_env_of_formula (genv, sigma) ff')))
          in
          let goal_vars =
            List.map (fun (_, i) -> fst (List.nth env (i - 1))) vars
          in
          let arith_args = goal_props @ goal_vars in
          let kill_arith = Tacticals.tclTHEN tac_arith tac in
          (*
(*tclABSTRACT fails in certain corner cases.*)
Tacticals.tclTHEN
           clear_all_no_check
           (Abstract.tclABSTRACT ~opaque:false None (Tacticals.tclTHEN tac_arith tac)) in *)
          Tacticals.tclTHEN
            (Tactics.assert_by (Names.Name goal_name) arith_goal
               (*Proofview.tclTIME  (Some "kill_arith")*) kill_arith)
            ((*Proofview.tclTIME  (Some "apply_arith") *)
             Tactics.exact_check
               (EConstr.applist
                  ( EConstr.mkVar goal_name
                  , arith_args @ List.map EConstr.mkVar ids )))
      with
      | CsdpNotFound -> fail_csdp_not_found ()
      | x ->
        if debug then
          Tacticals.tclFAIL (Pp.str (Printexc.get_backtrace ()))
        else raise x)

let micromega_wit_gen pre_process cnf spec prover wit_id ff =
  Proofview.Goal.enter (fun gl ->
      let sigma = Tacmach.project gl in
      try
        let spec = Lazy.force spec in
        let undump_cstr = undump_cstr spec.undump_coeff in
        let tg = Tag.from 0, Lazy.force coq_tt in
        let ff = undump_formula undump_cstr tg sigma ff in
        match
          micromega_tauto ~abstract:false pre_process cnf spec prover [] ff
        with
        | Unknown ->
          flush stdout;
          Tacticals.tclFAIL (Pp.str " Cannot find witness")
        | Model (m, e) ->
          Tacticals.tclFAIL (Pp.str " Cannot find witness")
        | Prf (_ids, _ff', res') ->
          let tres' = EConstr.mkApp (Lazy.force coq_list, [|spec.proof_typ|]) in
          Tactics.letin_tac
            None (Names.Name wit_id) res' (Some tres') Locusops.nowhere
      with
      | CsdpNotFound -> fail_csdp_not_found ()
      | x ->
        if debug then
          Tacticals.tclFAIL (Pp.str (Printexc.get_backtrace ()))
        else raise x)

let micromega_order_changer cert env ff =
  (*let ids = Util.List.map_i (fun i _ -> (Names.Id.of_string ("__v"^(string_of_int i)))) 0 env in *)
  let coeff = Lazy.force coq_Rcst in
  let dump_coeff = dump_Rcst in
  let typ = Lazy.force coq_R in
  let cert_typ =
    EConstr.mkApp (Lazy.force coq_list, [|Lazy.force coq_QWitness|])
  in
  let formula_typ = EConstr.mkApp (Lazy.force coq_Cstr, [|coeff|]) in
  let ff = dump_formula formula_typ (dump_cstr coeff dump_coeff) ff in
  let vm = dump_varmap typ (vm_of_list env) in
  Proofview.Goal.enter (fun gl ->
      Tacticals.tclTHENLIST
        [ Tactics.change_concl
            (set
               [ ( "__ff"
                 , ff
                 , EConstr.mkApp
                     ( Lazy.force coq_Formula
                     , [|formula_typ; Lazy.force coq_IsProp|] ) )
               ; ("__varmap", vm, EConstr.mkApp (Lazy.force coq_VarMap, [|typ|]))
               ; ("__wit", cert, cert_typ) ]
               (Tacmach.pf_concl gl))
          (*      Tacticals.tclTHENLIST (List.map (fun id ->  (Tactics.introduction id)) ids)*)
        ])

let micromega_genr prover tac =
  let parse_arith = parse_rarith in
  let spec =
    lazy
      { typ = Lazy.force coq_R
      ; coeff = Lazy.force coq_Rcst
      ; dump_coeff = dump_q
      ; undump_coeff = parse_q
      ; proof_typ = Lazy.force coq_QWitness
      ; dump_proof = dump_psatz coq_Q dump_q
      ; coeff_eq = Mc.qeq_bool }
  in
  Proofview.Goal.enter (fun gl ->
      let sigma = Tacmach.project gl in
      let genv = Tacmach.pf_env gl in
      let concl = Tacmach.pf_concl gl in
      let hyps = Tacmach.pf_hyps_types gl in
      try
        let hyps, concl, env =
          parse_goal (genv, sigma) parse_arith
            (Env.empty (genv, sigma))
            hyps concl
        in
        let env = Env.elements env in
        let spec = Lazy.force spec in
        let hyps' =
          List.map
            (fun (n, f) ->
              ( n
              , Mc.map_bformula Mc.IsProp
                  (Micromega.map_Formula Micromega.q_of_Rcst)
                  f ))
            hyps
        in
        let concl' =
          Mc.map_bformula Mc.IsProp
            (Micromega.map_Formula Micromega.q_of_Rcst)
            concl
        in
        match
          micromega_tauto
            (fun _ x -> x)
            Mc.cnfQ spec prover hyps' concl'
        with
        | Unknown | Model _ ->
          flush stdout;
          Tacticals.tclFAIL (Pp.str " Cannot find witness")
        | Prf (ids, ff', res') ->
          let ff, ids =
            formula_hyps_concl
              (List.filter (fun (n, _) -> CList.mem_f Id.equal n ids) hyps)
              concl
          in
          let ff' = abstract_wrt_formula ff' ff in
          let arith_goal, props, vars, ff_arith =
            make_goal_of_formula (genv, sigma) (Lazy.force dump_rexpr) ff'
          in
          let intro (id, _) = Tactics.introduction id in
          let intro_vars = Tacticals.tclTHENLIST (List.map intro vars) in
          let intro_props = Tacticals.tclTHENLIST (List.map intro props) in
          let ipat_of_name id =
            Some (CAst.make @@ IntroNaming (Namegen.IntroIdentifier id))
          in
          let goal_name =
            fresh_id Id.Set.empty (Names.Id.of_string "__arith") gl
          in
          let env' = List.map (fun (id, i) -> (EConstr.mkVar id, i)) vars in
          let tac_arith =
            Tacticals.tclTHENLIST
              [ clear_all_no_check
              ; intro_props
              ; intro_vars
              ; micromega_order_changer res' env' ff_arith ]
          in
          let goal_props =
            List.rev
              (List.map fst
                 (Env.elements (prop_env_of_formula (genv, sigma) ff')))
          in
          let goal_vars =
            List.map (fun (_, i) -> fst (List.nth env (i - 1))) vars
          in
          let arith_args = goal_props @ goal_vars in
          let kill_arith = Tacticals.tclTHEN tac_arith tac in
          (* Tacticals.tclTHEN
             (Tactics.keep [])
             (Tactics.tclABSTRACT  None*)
          Tacticals.tclTHENS
            (Tactics.forward true (Some None) (ipat_of_name goal_name)
               arith_goal)
            [ kill_arith
            ; Tacticals.tclTHENLIST
                [ Tactics.generalize (List.map EConstr.mkVar ids)
                ; Tactics.exact_check
                    (EConstr.applist (EConstr.mkVar goal_name, arith_args)) ] ]
      with
      | CsdpNotFound -> fail_csdp_not_found ())

let lift_ratproof prover l =
  match prover l with
  | Unknown | Model _ -> Unknown
  | Prf c -> Prf (Mc.RatProof (c, Mc.DoneProof))

type micromega_polys = (Micromega.q Mc.pol * Mc.op1) list

[@@@ocaml.warning "-37"]

type csdp_certificate = S of Sos_types.positivstellensatz option | F of string

(* Used to read the result of the execution of csdpcert *)

type provername = string * int option

(**
  * The caching mechanism.
  *)

module MakeCache (T : sig
  type prover_option
  type coeff

  val hash_prover_option : int -> prover_option -> int
  val hash_coeff : int -> coeff -> int
  val eq_prover_option : prover_option -> prover_option -> bool
  val eq_coeff : coeff -> coeff -> bool
end) : sig
  type key = T.prover_option * (T.coeff Mc.pol * Mc.op1) list

  val memo_opt : (unit -> bool) -> string -> (key -> 'a) -> key -> 'a
end = struct
  module E = struct
    type t = T.prover_option * (T.coeff Mc.pol * Mc.op1) list

    let equal =
      Hash.(
        eq_pair T.eq_prover_option
          (CList.equal (eq_pair (eq_pol T.eq_coeff) Hash.eq_op1)))

    let hash =
      let hash_cstr = Hash.(hash_pair (hash_pol T.hash_coeff) hash_op1) in
      Hash.((hash_pair T.hash_prover_option (List.fold_left hash_cstr)) 0)
  end

  include Persistent_cache.PHashtable (E)

  let memo_opt use_cache cache_file f =
    let memof = memo cache_file f in
    fun x -> if use_cache () then memof x else f x
end

module CacheCsdp = MakeCache (struct
  type prover_option = provername
  type coeff = Mc.q

  let hash_prover_option =
    Hash.(hash_pair hash_string (hash_elt (Option.hash (fun x -> x))))

  let eq_prover_option = Hash.(eq_pair String.equal (Option.equal Int.equal))
  let hash_coeff = Hash.hash_q
  let eq_coeff = Hash.eq_q
end)

(**
  * Build the command to call csdpcert, and launch it. This in turn will call
  * the sos driver to the csdp executable.
  * Throw CsdpNotFound if Coq isn't aware of any csdp executable.
  *)

let require_csdp =
  if System.is_in_system_path "csdp" then lazy () else lazy (raise CsdpNotFound)

let really_call_csdpcert :
    provername -> micromega_polys -> Sos_types.positivstellensatz option =
 fun provername poly ->
  Lazy.force require_csdp;
  let cmdname =
    let env = Boot.Env.init () in
    let plugin_dir = Boot.Env.plugins env |> Boot.Path.to_string in
    List.fold_left Filename.concat plugin_dir
      ["micromega"; "csdpcert" ^ Coq_config.exec_extension]
  in
  let cmdname = if Sys.file_exists cmdname then cmdname else "csdpcert" in
  match (command cmdname [|cmdname|] (provername, poly) : csdp_certificate) with
  | F str ->
    if debug then Printf.fprintf stdout "really_call_csdpcert : %s\n" str;
    raise (failwith str)
  | S res -> res

(**
  * Check the cache before calling the prover.
  *)

let xcall_csdpcert =
  CacheCsdp.memo_opt use_csdp_cache ".csdp.cache" (fun (prover, pb) ->
      really_call_csdpcert prover pb)

(**
  * Prover callback functions.
  *)

let call_csdpcert prover pb = xcall_csdpcert (prover, pb)

let rec z_to_q_pol e =
  match e with
  | Mc.Pc z -> Mc.Pc {Mc.qnum = z; Mc.qden = Mc.XH}
  | Mc.Pinj (p, pol) -> Mc.Pinj (p, z_to_q_pol pol)
  | Mc.PX (pol1, p, pol2) -> Mc.PX (z_to_q_pol pol1, p, z_to_q_pol pol2)

let call_csdpcert_q provername poly =
  match call_csdpcert provername poly with
  | None -> Unknown
  | Some cert ->
    let cert = Certificate.q_cert_of_pos cert in
    if Mc.qWeakChecker poly cert then Prf cert
    else (
      print_string "buggy certificate";
      Unknown )

let call_csdpcert_z provername poly =
  let l = List.map (fun (e, o) -> (z_to_q_pol e, o)) poly in
  match call_csdpcert provername l with
  | None -> Unknown
  | Some cert ->
    let cert = Certificate.z_cert_of_pos cert in
    if Mc.zWeakChecker poly cert then Prf cert
    else (
      print_string "buggy certificate";
      flush stdout;
      Unknown )

let rec xhyps_of_cone base acc prf =
  match prf with
  | Mc.PsatzC _ | Mc.PsatzZ | Mc.PsatzSquare _ -> acc
  | Mc.PsatzIn n ->
    let n = CoqToCaml.nat n in
    if n >= base then ISet.add (n - base) acc else acc
  | Mc.PsatzLet (e1, e2) ->
    xhyps_of_cone (base + 1) (xhyps_of_cone base acc e1) e2
  | Mc.PsatzMulC (_, c) -> xhyps_of_cone base acc c
  | Mc.PsatzAdd (e1, e2) | Mc.PsatzMulE (e1, e2) ->
    xhyps_of_cone base (xhyps_of_cone base acc e2) e1

let hyps_of_cone prf = xhyps_of_cone 0 ISet.empty prf

let hyps_of_pt pt =
  let rec xhyps base pt acc =
    match pt with
    | Mc.DoneProof -> acc
    | Mc.RatProof (c, pt) -> xhyps (base + 1) pt (xhyps_of_cone base acc c)
    | Mc.CutProof (c, pt) -> xhyps (base + 1) pt (xhyps_of_cone base acc c)
    | Mc.SplitProof (p, p1, p2) -> xhyps (base + 1) p1 (xhyps (base + 1) p2 acc)
    | Mc.EnumProof (c1, c2, l) ->
      let s = xhyps_of_cone base (xhyps_of_cone base acc c2) c1 in
      List.fold_left (fun s x -> xhyps (base + 1) x s) s l
    | Mc.ExProof (_, pt) -> xhyps (base + 3) pt acc
  in
  xhyps 0 pt ISet.empty

let compact_cone prf f =
  let translate ofset x = if x < ofset then x else f (x - ofset) + ofset in
  let np ofset n = CamlToCoq.nat (translate ofset (CoqToCaml.nat n)) in
  let rec xinterp ofset prf =
    match prf with
    | Mc.PsatzC _ | Mc.PsatzZ | Mc.PsatzSquare _ -> prf
    | Mc.PsatzIn n -> Mc.PsatzIn (np ofset n)
    | Mc.PsatzLet (e1, e2) ->
      Mc.PsatzLet (xinterp ofset e1, xinterp (ofset + 1) e2)
    | Mc.PsatzMulC (e, c) -> Mc.PsatzMulC (e, xinterp ofset c)
    | Mc.PsatzAdd (e1, e2) -> Mc.PsatzAdd (xinterp ofset e1, xinterp ofset e2)
    | Mc.PsatzMulE (e1, e2) -> Mc.PsatzMulE (xinterp ofset e1, xinterp ofset e2)
  in
  xinterp 0 prf

let compact_pt pt f =
  let translate ofset x = if x < ofset then x else f (x - ofset) + ofset in
  let rec compact_pt ofset pt =
    match pt with
    | Mc.DoneProof -> Mc.DoneProof
    | Mc.RatProof (c, pt) ->
      Mc.RatProof (compact_cone c (translate ofset), compact_pt (ofset + 1) pt)
    | Mc.CutProof (c, pt) ->
      Mc.CutProof (compact_cone c (translate ofset), compact_pt (ofset + 1) pt)
    | Mc.SplitProof (p, p1, p2) ->
      Mc.SplitProof (p, compact_pt (ofset + 1) p1, compact_pt (ofset + 1) p2)
    | Mc.EnumProof (c1, c2, l) ->
      Mc.EnumProof
        ( compact_cone c1 (translate ofset)
        , compact_cone c2 (translate ofset)
        , Mc.map (fun x -> compact_pt (ofset + 1) x) l )
    | Mc.ExProof (x, pt) -> Mc.ExProof (x, compact_pt (ofset + 3) pt)
  in
  compact_pt 0 pt

(**
  * Definition of provers.
  * Instantiates the type ('a,'prf) prover defined above.
  *)

let lift_pexpr_prover p l = p (List.map (fun (e, o) -> (Mc.denorm e, o)) l)

module CacheZ = MakeCache (struct
  type prover_option = bool * bool * int
  type coeff = Mc.z

  let hash_prover_option : int -> prover_option -> int =
    Hash.hash_elt Hashtbl.hash

  let eq_prover_option : prover_option -> prover_option -> bool = ( = )
  let eq_coeff = Hash.eq_z
  let hash_coeff = Hash.hash_z
end)

module CacheQ = MakeCache (struct
  type prover_option = int
  type coeff = Mc.q

  let hash_prover_option : int -> int -> int = Hash.hash_elt Hashtbl.hash
  let eq_prover_option = Int.equal
  let eq_coeff = Hash.eq_q
  let hash_coeff = Hash.hash_q
end)

let memo_lia =
  CacheZ.memo_opt use_lia_cache ".lia.cache" (fun ((_, _, b), s) ->
      lift_pexpr_prover (Certificate.lia b) s)

let memo_nlia =
  CacheZ.memo_opt use_nia_cache ".nia.cache" (fun ((_, _, b), s) ->
      lift_pexpr_prover (Certificate.nlia b) s)

let memo_nra =
  CacheQ.memo_opt use_nra_cache ".nra.cache" (fun (o, s) ->
      lift_pexpr_prover (Certificate.nlinear_prover o) s)

let linear_prover_Q =
  { name = "linear prover"
  ; get_option = lra_proof_depth
  ; prover =
      (fun (o, l) ->
        lift_pexpr_prover (Certificate.linear_prover_with_cert o) l)
  ; hyps = hyps_of_cone
  ; compact = compact_cone
  ; pp_prf = pp_psatz pp_q
  ; pp_f = (fun o x -> pp_pol pp_q o (fst x)) }

let linear_prover_R =
  { name = "linear prover"
  ; get_option = lra_proof_depth
  ; prover =
      (fun (o, l) ->
        lift_pexpr_prover (Certificate.linear_prover_with_cert o) l)
  ; hyps = hyps_of_cone
  ; compact = compact_cone
  ; pp_prf = pp_psatz pp_q
  ; pp_f = (fun o x -> pp_pol pp_q o (fst x)) }

let nlinear_prover_R =
  { name = "nra"
  ; get_option = lra_proof_depth
  ; prover = memo_nra
  ; hyps = hyps_of_cone
  ; compact = compact_cone
  ; pp_prf = pp_psatz pp_q
  ; pp_f = (fun o x -> pp_pol pp_q o (fst x)) }

let non_linear_prover_Q str o =
  { name = "real nonlinear prover"
  ; get_option = (fun () -> (str, o))
  ; prover = (fun (o, l) -> call_csdpcert_q o l)
  ; hyps = hyps_of_cone
  ; compact = compact_cone
  ; pp_prf = pp_psatz pp_q
  ; pp_f = (fun o x -> pp_pol pp_q o (fst x)) }

let non_linear_prover_R str o =
  { name = "real nonlinear prover"
  ; get_option = (fun () -> (str, o))
  ; prover = (fun (o, l) -> call_csdpcert_q o l)
  ; hyps = hyps_of_cone
  ; compact = compact_cone
  ; pp_prf = pp_psatz pp_q
  ; pp_f = (fun o x -> pp_pol pp_q o (fst x)) }

let non_linear_prover_Z str o =
  { name = "real nonlinear prover"
  ; get_option = (fun () -> (str, o))
  ; prover = (fun (o, l) -> lift_ratproof (call_csdpcert_z o) l)
  ; hyps = hyps_of_pt
  ; compact = compact_pt
  ; pp_prf = pp_proof_term
  ; pp_f = (fun o x -> pp_pol pp_z o (fst x)) }

let linear_Z =
  { name = "lia"
  ; get_option = get_lia_option
  ; prover = memo_lia
  ; hyps = hyps_of_pt
  ; compact = compact_pt
  ; pp_prf = pp_proof_term
  ; pp_f = (fun o x -> pp_pol pp_z o (fst x)) }

let nlinear_Z =
  { name = "nlia"
  ; get_option = get_lia_option
  ; prover = memo_nlia
  ; hyps = hyps_of_pt
  ; compact = compact_pt
  ; pp_prf = pp_proof_term
  ; pp_f = (fun o x -> pp_pol pp_z o (fst x)) }

(**
  * Functions instantiating micromega_gen with the appropriate theories and
  * solvers
  *)

let exfalso_if_concl_not_Prop =
  Proofview.Goal.enter (fun gl ->
      Tacmach.(
        if is_prop (pf_env gl) (project gl) (pf_concl gl) then
          Tacticals.tclIDTAC
        else Tactics.elim_type (Lazy.force coq_False)))

let micromega_gen parse_arith pre_process cnf spec dumpexpr prover tac =
  Tacticals.tclTHEN exfalso_if_concl_not_Prop
    (micromega_gen parse_arith pre_process cnf spec dumpexpr prover tac)

let micromega_genr prover tac =
  Tacticals.tclTHEN exfalso_if_concl_not_Prop (micromega_genr prover tac)

let xlra_Q =
  micromega_gen parse_qarith
    (fun _ x -> x)
    Mc.cnfQ qq_domain_spec dump_qexpr linear_prover_Q

let wlra_Q =
  micromega_wit_gen
    (fun _ x -> x)
    Mc.cnfQ qq_domain_spec linear_prover_Q

let xlra_R = micromega_genr linear_prover_R

let xlia =
  micromega_gen parse_zarith
    (fun _ x -> x)
    Mc.cnfZ zz_domain_spec dump_zexpr linear_Z

let wlia =
  micromega_wit_gen
    (fun _ x -> x)
    Mc.cnfZ zz_domain_spec linear_Z

let xnra_Q =
  micromega_gen parse_qarith
    (fun _ x -> x)
    Mc.cnfQ qq_domain_spec dump_qexpr nlinear_prover_R

let wnra_Q =
  micromega_wit_gen
    (fun _ x -> x)
    Mc.cnfQ qq_domain_spec nlinear_prover_R

let xnra_R = micromega_genr nlinear_prover_R

let xnia =
  micromega_gen parse_zarith
    (fun _ x -> x)
    Mc.cnfZ zz_domain_spec dump_zexpr nlinear_Z

let wnia =
  micromega_wit_gen
    (fun _ x -> x)
    Mc.cnfZ zz_domain_spec nlinear_Z

let xsos_Q =
  micromega_gen parse_qarith
    (fun _ x -> x)
    Mc.cnfQ qq_domain_spec dump_qexpr
    (non_linear_prover_Q "pure_sos" None)

let wsos_Q =
  micromega_wit_gen
    (fun _ x -> x)
    Mc.cnfQ qq_domain_spec
    (non_linear_prover_Q "pure_sos" None)

let xsos_R = micromega_genr (non_linear_prover_R "pure_sos" None)

let xsos_Z =
  micromega_gen parse_zarith
    (fun _ x -> x)
    Mc.cnfZ zz_domain_spec dump_zexpr
    (non_linear_prover_Z "pure_sos" None)

let wsos_Z =
  micromega_wit_gen
    (fun _ x -> x)
    Mc.cnfZ zz_domain_spec
    (non_linear_prover_Z "pure_sos" None)

let xpsatz_Q i =
  micromega_gen parse_qarith
    (fun _ x -> x)
    Mc.cnfQ qq_domain_spec dump_qexpr
    (non_linear_prover_Q "real_nonlinear_prover" (Some i))

let wpsatz_Q i =
  micromega_wit_gen
    (fun _ x -> x)
    Mc.cnfQ qq_domain_spec
    (non_linear_prover_Q "real_nonlinear_prover" (Some i))

let xpsatz_R i =
  micromega_genr (non_linear_prover_R "real_nonlinear_prover" (Some i))

let xpsatz_Z i =
  micromega_gen parse_zarith
    (fun _ x -> x)
    Mc.cnfZ zz_domain_spec dump_zexpr
    (non_linear_prover_Z "real_nonlinear_prover" (Some i))

let wpsatz_Z i =
  micromega_wit_gen
    (fun _ x -> x)
    Mc.cnfZ zz_domain_spec
    (non_linear_prover_Z "real_nonlinear_prover" (Some i))

let print_lia_profile () =
  Simplex.(
    let { number_of_successes
        ; number_of_failures
        ; success_pivots
        ; failure_pivots
        ; average_pivots
        ; maximum_pivots } =
      Simplex.get_profile_info ()
    in
    Feedback.msg_notice
      Pp.(
        (* successes *)
        str "number of successes: "
        ++ int number_of_successes ++ fnl ()
        (* success pivots *)
        ++ str "number of success pivots: "
        ++ int success_pivots ++ fnl ()
        (* failure *)
        ++ str "number of failures: "
        ++ int number_of_failures ++ fnl ()
        (* failure pivots *)
        ++ str "number of failure pivots: "
        ++ int failure_pivots ++ fnl ()
        (* Other *)
        ++ str "average number of pivots: "
        ++ int average_pivots ++ fnl ()
        ++ str "maximum number of pivots: "
        ++ int maximum_pivots ++ fnl ()))

(* Local Variables: *)
(* coding: utf-8 *)
(* End: *)
