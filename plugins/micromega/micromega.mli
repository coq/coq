
type __ = Obj.t

type unit0 =
| Tt

val negb : bool -> bool

type nat =
| O
| S of nat

type ('a, 'b) sum =
| Inl of 'a
| Inr of 'b

val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

val app : 'a1 list -> 'a1 list -> 'a1 list

type comparison =
| Eq
| Lt
| Gt

val compOpp : comparison -> comparison

val add : nat -> nat -> nat

val nth : nat -> 'a1 list -> 'a1 -> 'a1

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1

type positive =
| XI of positive
| XO of positive
| XH

type n =
| N0
| Npos of positive

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Pos :
 sig
  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg
 end

module Coq_Pos :
 sig
  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val pred_double : positive -> positive

  type mask = Pos.mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  val succ_double_mask : mask -> mask

  val double_mask : mask -> mask

  val double_pred_mask : positive -> mask

  val sub_mask : positive -> positive -> mask

  val sub_mask_carry : positive -> positive -> mask

  val sub : positive -> positive -> positive

  val mul : positive -> positive -> positive

  val iter : ('a1 -> 'a1) -> 'a1 -> positive -> 'a1

  val size_nat : positive -> nat

  val compare_cont : comparison -> positive -> positive -> comparison

  val compare : positive -> positive -> comparison

  val gcdn : nat -> positive -> positive -> positive

  val gcd : positive -> positive -> positive

  val of_succ_nat : nat -> positive
 end

module N :
 sig
  val of_nat : nat -> n
 end

val pow_pos : ('a1 -> 'a1 -> 'a1) -> 'a1 -> positive -> 'a1

module Z :
 sig
  val double : z -> z

  val succ_double : z -> z

  val pred_double : z -> z

  val pos_sub : positive -> positive -> z

  val add : z -> z -> z

  val opp : z -> z

  val sub : z -> z -> z

  val mul : z -> z -> z

  val pow_pos : z -> positive -> z

  val pow : z -> z -> z

  val compare : z -> z -> comparison

  val leb : z -> z -> bool

  val ltb : z -> z -> bool

  val gtb : z -> z -> bool

  val max : z -> z -> z

  val abs : z -> z

  val to_N : z -> n

  val of_nat : nat -> z

  val of_N : n -> z

  val pos_div_eucl : positive -> z -> z * z

  val div_eucl : z -> z -> z * z

  val div : z -> z -> z

  val gcd : z -> z -> z
 end

val zeq_bool : z -> z -> bool

type 'c pol =
| Pc of 'c
| Pinj of positive * 'c pol
| PX of 'c pol * positive * 'c pol

val p0 : 'a1 -> 'a1 pol

val p1 : 'a1 -> 'a1 pol

val peq : ('a1 -> 'a1 -> bool) -> 'a1 pol -> 'a1 pol -> bool

val mkPinj : positive -> 'a1 pol -> 'a1 pol

val mkPinj_pred : positive -> 'a1 pol -> 'a1 pol

val mkPX : 'a1 -> ('a1 -> 'a1 -> bool) -> 'a1 pol -> positive -> 'a1 pol -> 'a1 pol

val mkXi : 'a1 -> 'a1 -> positive -> 'a1 pol

val mkX : 'a1 -> 'a1 -> 'a1 pol

val popp : ('a1 -> 'a1) -> 'a1 pol -> 'a1 pol

val paddC : ('a1 -> 'a1 -> 'a1) -> 'a1 pol -> 'a1 -> 'a1 pol

val psubC : ('a1 -> 'a1 -> 'a1) -> 'a1 pol -> 'a1 -> 'a1 pol

val paddI :
  ('a1 -> 'a1 -> 'a1) -> ('a1 pol -> 'a1 pol -> 'a1 pol) -> 'a1 pol -> positive -> 'a1 pol
  -> 'a1 pol

val psubI :
  ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1) -> ('a1 pol -> 'a1 pol -> 'a1 pol) -> 'a1 pol ->
  positive -> 'a1 pol -> 'a1 pol

val paddX :
  'a1 -> ('a1 -> 'a1 -> bool) -> ('a1 pol -> 'a1 pol -> 'a1 pol) -> 'a1 pol -> positive ->
  'a1 pol -> 'a1 pol

val psubX :
  'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> ('a1 pol -> 'a1 pol -> 'a1 pol) -> 'a1
  pol -> positive -> 'a1 pol -> 'a1 pol

val padd :
  'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 pol -> 'a1 pol -> 'a1 pol

val psub :
  'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1) -> ('a1 -> 'a1 ->
  bool) -> 'a1 pol -> 'a1 pol -> 'a1 pol

val pmulC_aux :
  'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 pol -> 'a1 -> 'a1 pol

val pmulC :
  'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 pol -> 'a1 -> 'a1 pol

val pmulI :
  'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> ('a1 pol -> 'a1 pol -> 'a1
  pol) -> 'a1 pol -> positive -> 'a1 pol -> 'a1 pol

val pmul :
  'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1
  pol -> 'a1 pol -> 'a1 pol

val psquare :
  'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1
  pol -> 'a1 pol

type 'c pExpr =
| PEc of 'c
| PEX of positive
| PEadd of 'c pExpr * 'c pExpr
| PEsub of 'c pExpr * 'c pExpr
| PEmul of 'c pExpr * 'c pExpr
| PEopp of 'c pExpr
| PEpow of 'c pExpr * n

val mk_X : 'a1 -> 'a1 -> positive -> 'a1 pol

val ppow_pos :
  'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> ('a1
  pol -> 'a1 pol) -> 'a1 pol -> 'a1 pol -> positive -> 'a1 pol

val ppow_N :
  'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> ('a1
  pol -> 'a1 pol) -> 'a1 pol -> n -> 'a1 pol

val norm_aux :
  'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1
  -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 pExpr -> 'a1 pol

type ('tA, 'tX, 'aA, 'aF) gFormula =
| TT
| FF
| X of 'tX
| A of 'tA * 'aA
| Cj of ('tA, 'tX, 'aA, 'aF) gFormula * ('tA, 'tX, 'aA, 'aF) gFormula
| D of ('tA, 'tX, 'aA, 'aF) gFormula * ('tA, 'tX, 'aA, 'aF) gFormula
| N of ('tA, 'tX, 'aA, 'aF) gFormula
| I of ('tA, 'tX, 'aA, 'aF) gFormula * 'aF option * ('tA, 'tX, 'aA, 'aF) gFormula

val mapX : ('a2 -> 'a2) -> ('a1, 'a2, 'a3, 'a4) gFormula -> ('a1, 'a2, 'a3, 'a4) gFormula

val foldA : ('a5 -> 'a3 -> 'a5) -> ('a1, 'a2, 'a3, 'a4) gFormula -> 'a5 -> 'a5

val cons_id : 'a1 option -> 'a1 list -> 'a1 list

val ids_of_formula : ('a1, 'a2, 'a3, 'a4) gFormula -> 'a4 list

val collect_annot : ('a1, 'a2, 'a3, 'a4) gFormula -> 'a3 list

type 'a bFormula = ('a, __, unit0, unit0) gFormula

val map_bformula :
  ('a1 -> 'a2) -> ('a1, 'a3, 'a4, 'a5) gFormula -> ('a2, 'a3, 'a4, 'a5) gFormula

type ('x, 'annot) clause = ('x * 'annot) list

type ('x, 'annot) cnf = ('x, 'annot) clause list

val cnf_tt : ('a1, 'a2) cnf

val cnf_ff : ('a1, 'a2) cnf

val add_term :
  ('a1 -> bool) -> ('a1 -> 'a1 -> 'a1 option) -> ('a1 * 'a2) -> ('a1, 'a2) clause -> ('a1,
  'a2) clause option

val or_clause :
  ('a1 -> bool) -> ('a1 -> 'a1 -> 'a1 option) -> ('a1, 'a2) clause -> ('a1, 'a2) clause ->
  ('a1, 'a2) clause option

val or_clause_cnf :
  ('a1 -> bool) -> ('a1 -> 'a1 -> 'a1 option) -> ('a1, 'a2) clause -> ('a1, 'a2) cnf ->
  ('a1, 'a2) cnf

val or_cnf :
  ('a1 -> bool) -> ('a1 -> 'a1 -> 'a1 option) -> ('a1, 'a2) cnf -> ('a1, 'a2) cnf -> ('a1,
  'a2) cnf

val and_cnf : ('a1, 'a2) cnf -> ('a1, 'a2) cnf -> ('a1, 'a2) cnf

type ('term, 'annot, 'tX, 'aF) tFormula = ('term, 'tX, 'annot, 'aF) gFormula

val xcnf :
  ('a2 -> bool) -> ('a2 -> 'a2 -> 'a2 option) -> ('a1 -> 'a3 -> ('a2, 'a3) cnf) -> ('a1 ->
  'a3 -> ('a2, 'a3) cnf) -> bool -> ('a1, 'a3, 'a4, 'a5) tFormula -> ('a2, 'a3) cnf

val radd_term :
  ('a1 -> bool) -> ('a1 -> 'a1 -> 'a1 option) -> ('a1 * 'a2) -> ('a1, 'a2) clause ->
  (('a1, 'a2) clause, 'a2 list) sum

val ror_clause :
  ('a1 -> bool) -> ('a1 -> 'a1 -> 'a1 option) -> ('a1 * 'a2) list -> ('a1, 'a2) clause ->
  (('a1, 'a2) clause, 'a2 list) sum

val ror_clause_cnf :
  ('a1 -> bool) -> ('a1 -> 'a1 -> 'a1 option) -> ('a1 * 'a2) list -> ('a1, 'a2) clause
  list -> ('a1, 'a2) clause list * 'a2 list

val ror_cnf :
  ('a1 -> bool) -> ('a1 -> 'a1 -> 'a1 option) -> ('a1 * 'a2) list list -> ('a1, 'a2)
  clause list -> ('a1, 'a2) cnf * 'a2 list

val rxcnf :
  ('a2 -> bool) -> ('a2 -> 'a2 -> 'a2 option) -> ('a1 -> 'a3 -> ('a2, 'a3) cnf) -> ('a1 ->
  'a3 -> ('a2, 'a3) cnf) -> bool -> ('a1, 'a3, 'a4, 'a5) tFormula -> ('a2, 'a3) cnf * 'a3
  list

val cnf_checker : (('a1 * 'a2) list -> 'a3 -> bool) -> ('a1, 'a2) cnf -> 'a3 list -> bool

val tauto_checker :
  ('a2 -> bool) -> ('a2 -> 'a2 -> 'a2 option) -> ('a1 -> 'a3 -> ('a2, 'a3) cnf) -> ('a1 ->
  'a3 -> ('a2, 'a3) cnf) -> (('a2 * 'a3) list -> 'a4 -> bool) -> ('a1, __, 'a3, unit0)
  gFormula -> 'a4 list -> bool

val cneqb : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 -> bool

val cltb : ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 -> bool

type 'c polC = 'c pol

type op1 =
| Equal
| NonEqual
| Strict
| NonStrict

type 'c nFormula = 'c polC * op1

val opMult : op1 -> op1 -> op1 option

val opAdd : op1 -> op1 -> op1 option

type 'c psatz =
| PsatzIn of nat
| PsatzSquare of 'c polC
| PsatzMulC of 'c polC * 'c psatz
| PsatzMulE of 'c psatz * 'c psatz
| PsatzAdd of 'c psatz * 'c psatz
| PsatzC of 'c
| PsatzZ

val map_option : ('a1 -> 'a2 option) -> 'a1 option -> 'a2 option

val map_option2 : ('a1 -> 'a2 -> 'a3 option) -> 'a1 option -> 'a2 option -> 'a3 option

val pexpr_times_nformula :
  'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1
  polC -> 'a1 nFormula -> 'a1 nFormula option

val nformula_times_nformula :
  'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1
  nFormula -> 'a1 nFormula -> 'a1 nFormula option

val nformula_plus_nformula :
  'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 nFormula -> 'a1 nFormula ->
  'a1 nFormula option

val eval_Psatz :
  'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> ('a1
  -> 'a1 -> bool) -> 'a1 nFormula list -> 'a1 psatz -> 'a1 nFormula option

val check_inconsistent :
  'a1 -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> bool) -> 'a1 nFormula -> bool

val check_normalised_formulas :
  'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> ('a1
  -> 'a1 -> bool) -> 'a1 nFormula list -> 'a1 psatz -> bool

type op2 =
| OpEq
| OpNEq
| OpLe
| OpGe
| OpLt
| OpGt

type 't formula = { flhs : 't pExpr; fop : op2; frhs : 't pExpr }

val norm :
  'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1
  -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 pExpr -> 'a1 pol

val psub0 :
  'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1) -> ('a1 -> 'a1 ->
  bool) -> 'a1 pol -> 'a1 pol -> 'a1 pol

val padd0 :
  'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 pol -> 'a1 pol -> 'a1 pol

val xnormalise :
  'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1
  -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 formula -> 'a1 nFormula list

val cnf_normalise :
  'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1
  -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 formula -> 'a2 -> ('a1 nFormula, 'a2) cnf

val xnegate :
  'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1
  -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 formula -> 'a1 nFormula list

val cnf_negate :
  'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1
  -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 formula -> 'a2 -> ('a1 nFormula, 'a2) cnf

val xdenorm : positive -> 'a1 pol -> 'a1 pExpr

val denorm : 'a1 pol -> 'a1 pExpr

val map_PExpr : ('a2 -> 'a1) -> 'a2 pExpr -> 'a1 pExpr

val map_Formula : ('a2 -> 'a1) -> 'a2 formula -> 'a1 formula

val simpl_cone :
  'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 psatz -> 'a1 psatz

module PositiveSet :
 sig
  type tree =
  | Leaf
  | Node of tree * bool * tree
 end

type q = { qnum : z; qden : positive }

val qnum : q -> z

val qden : q -> positive

val qeq_bool : q -> q -> bool

val qle_bool : q -> q -> bool

val qplus : q -> q -> q

val qmult : q -> q -> q

val qopp : q -> q

val qminus : q -> q -> q

val qinv : q -> q

val qpower_positive : q -> positive -> q

val qpower : q -> z -> q

type 'a t =
| Empty
| Elt of 'a
| Branch of 'a t * 'a * 'a t

val find : 'a1 -> 'a1 t -> positive -> 'a1

val singleton : 'a1 -> positive -> 'a1 -> 'a1 t

val vm_add : 'a1 -> positive -> 'a1 -> 'a1 t -> 'a1 t

val zeval_const : z pExpr -> z option

type zWitness = z psatz

val zWeakChecker : z nFormula list -> z psatz -> bool

val psub1 : z pol -> z pol -> z pol

val padd1 : z pol -> z pol -> z pol

val normZ : z pExpr -> z pol

val xnormalise0 : z formula -> z nFormula list

val normalise : z formula -> 'a1 -> (z nFormula, 'a1) cnf

val xnegate0 : z formula -> z nFormula list

val negate : z formula -> 'a1 -> (z nFormula, 'a1) cnf

val zunsat : z nFormula -> bool

val zdeduce : z nFormula -> z nFormula -> z nFormula option

val cnfZ : (z formula, 'a1, 'a2, 'a3) tFormula -> (z nFormula, 'a1) cnf * 'a1 list

val ceiling : z -> z -> z

type zArithProof =
| DoneProof
| RatProof of zWitness * zArithProof
| CutProof of zWitness * zArithProof
| EnumProof of zWitness * zWitness * zArithProof list

val zgcdM : z -> z -> z

val zgcd_pol : z polC -> z * z

val zdiv_pol : z polC -> z -> z polC

val makeCuttingPlane : z polC -> z polC * z

val genCuttingPlane : z nFormula -> ((z polC * z) * op1) option

val nformula_of_cutting_plane : ((z polC * z) * op1) -> z nFormula

val is_pol_Z0 : z polC -> bool

val eval_Psatz0 : z nFormula list -> zWitness -> z nFormula option

val valid_cut_sign : op1 -> bool

module Vars :
 sig
  type elt = positive

  type tree = PositiveSet.tree =
  | Leaf
  | Node of tree * bool * tree

  type t = tree

  val empty : t

  val add : elt -> t -> t

  val singleton : elt -> t

  val union : t -> t -> t

  val rev_append : elt -> elt -> elt

  val rev : elt -> elt

  val xfold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> elt -> 'a1

  val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1
 end

val vars_of_pexpr : z pExpr -> Vars.t

val vars_of_formula : z formula -> Vars.t

val vars_of_bformula : (z formula, 'a1, 'a2, 'a3) gFormula -> Vars.t

val bound_var : positive -> z formula

val mk_eq_pos : positive -> positive -> positive -> z formula

val bound_vars :
  (positive -> positive -> bool option -> 'a2) -> positive -> Vars.t -> (z formula, 'a1,
  'a2, 'a3) gFormula

val bound_problem_fr :
  (positive -> positive -> bool option -> 'a2) -> positive -> (z formula, 'a1, 'a2, 'a3)
  gFormula -> (z formula, 'a1, 'a2, 'a3) gFormula

val zChecker : z nFormula list -> zArithProof -> bool

val zTautoChecker : z formula bFormula -> zArithProof list -> bool

type qWitness = q psatz

val qWeakChecker : q nFormula list -> q psatz -> bool

val qnormalise : q formula -> 'a1 -> (q nFormula, 'a1) cnf

val qnegate : q formula -> 'a1 -> (q nFormula, 'a1) cnf

val qunsat : q nFormula -> bool

val qdeduce : q nFormula -> q nFormula -> q nFormula option

val normQ : q pExpr -> q pol

val cnfQ : (q formula, 'a1, 'a2, 'a3) tFormula -> (q nFormula, 'a1) cnf * 'a1 list

val qTautoChecker : q formula bFormula -> qWitness list -> bool

type rcst =
| C0
| C1
| CQ of q
| CZ of z
| CPlus of rcst * rcst
| CMinus of rcst * rcst
| CMult of rcst * rcst
| CPow of rcst * (z, nat) sum
| CInv of rcst
| COpp of rcst

val z_of_exp : (z, nat) sum -> z

val q_of_Rcst : rcst -> q

type rWitness = q psatz

val rWeakChecker : q nFormula list -> q psatz -> bool

val rnormalise : q formula -> 'a1 -> (q nFormula, 'a1) cnf

val rnegate : q formula -> 'a1 -> (q nFormula, 'a1) cnf

val runsat : q nFormula -> bool

val rdeduce : q nFormula -> q nFormula -> q nFormula option

val rTautoChecker : rcst formula bFormula -> rWitness list -> bool
