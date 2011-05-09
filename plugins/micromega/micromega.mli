val negb : bool -> bool

type nat =
| O
| S of nat

type comparison =
| Eq
| Lt
| Gt

val compOpp : comparison -> comparison

val app : 'a1 list -> 'a1 list -> 'a1 list

val plus : nat -> nat -> nat

type positive =
| XI of positive
| XO of positive
| XH

val psucc : positive -> positive

val pplus : positive -> positive -> positive

val pplus_carry : positive -> positive -> positive

val p_of_succ_nat : nat -> positive

val pdouble_minus_one : positive -> positive

type positive_mask =
| IsNul
| IsPos of positive
| IsNeg

val pdouble_plus_one_mask : positive_mask -> positive_mask

val pdouble_mask : positive_mask -> positive_mask

val pdouble_minus_two : positive -> positive_mask

val pminus_mask : positive -> positive -> positive_mask

val pminus_mask_carry : positive -> positive -> positive_mask

val pminus : positive -> positive -> positive

val pmult : positive -> positive -> positive

val psize : positive -> nat

val pcompare : positive -> positive -> comparison -> comparison

type n =
| N0
| Npos of positive

val n_of_nat : nat -> n

val pow_pos : ('a1 -> 'a1 -> 'a1) -> 'a1 -> positive -> 'a1

val nth : nat -> 'a1 list -> 'a1 -> 'a1

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1

type z =
| Z0
| Zpos of positive
| Zneg of positive

val zdouble_plus_one : z -> z

val zdouble_minus_one : z -> z

val zdouble : z -> z

val zPminus : positive -> positive -> z

val zplus : z -> z -> z

val zopp : z -> z

val zminus : z -> z -> z

val zmult : z -> z -> z

val zcompare : z -> z -> comparison

val zmax : z -> z -> z

val zabs : z -> z

val zle_bool : z -> z -> bool

val zge_bool : z -> z -> bool

val zgt_bool : z -> z -> bool

val zeq_bool : z -> z -> bool

val pgcdn : nat -> positive -> positive -> positive

val pgcd : positive -> positive -> positive

val zgcd : z -> z -> z

val zdiv_eucl_POS : positive -> z -> z * z

val zdiv_eucl : z -> z -> z * z

val zdiv : z -> z -> z

type 'c pol =
| Pc of 'c
| Pinj of positive * 'c pol
| PX of 'c pol * positive * 'c pol

val p0 : 'a1 -> 'a1 pol

val p1 : 'a1 -> 'a1 pol

val peq : ('a1 -> 'a1 -> bool) -> 'a1 pol -> 'a1 pol -> bool

val mkPinj : positive -> 'a1 pol -> 'a1 pol

val mkPinj_pred : positive -> 'a1 pol -> 'a1 pol

val mkPX :
  'a1 -> ('a1 -> 'a1 -> bool) -> 'a1 pol -> positive -> 'a1 pol -> 'a1 pol

val mkXi : 'a1 -> 'a1 -> positive -> 'a1 pol

val mkX : 'a1 -> 'a1 -> 'a1 pol

val popp : ('a1 -> 'a1) -> 'a1 pol -> 'a1 pol

val paddC : ('a1 -> 'a1 -> 'a1) -> 'a1 pol -> 'a1 -> 'a1 pol

val psubC : ('a1 -> 'a1 -> 'a1) -> 'a1 pol -> 'a1 -> 'a1 pol

val paddI :
  ('a1 -> 'a1 -> 'a1) -> ('a1 pol -> 'a1 pol -> 'a1 pol) -> 'a1 pol ->
  positive -> 'a1 pol -> 'a1 pol

val psubI :
  ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1) -> ('a1 pol -> 'a1 pol -> 'a1 pol) ->
  'a1 pol -> positive -> 'a1 pol -> 'a1 pol

val paddX :
  'a1 -> ('a1 -> 'a1 -> bool) -> ('a1 pol -> 'a1 pol -> 'a1 pol) -> 'a1 pol
  -> positive -> 'a1 pol -> 'a1 pol

val psubX :
  'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> ('a1 pol -> 'a1 pol -> 'a1
  pol) -> 'a1 pol -> positive -> 'a1 pol -> 'a1 pol

val padd :
  'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 pol -> 'a1 pol ->
  'a1 pol

val psub :
  'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1) -> ('a1
  -> 'a1 -> bool) -> 'a1 pol -> 'a1 pol -> 'a1 pol

val pmulC_aux :
  'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 pol -> 'a1 -> 'a1
  pol

val pmulC :
  'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 pol -> 'a1
  -> 'a1 pol

val pmulI :
  'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> ('a1 pol ->
  'a1 pol -> 'a1 pol) -> 'a1 pol -> positive -> 'a1 pol -> 'a1 pol

val pmul :
  'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 ->
  bool) -> 'a1 pol -> 'a1 pol -> 'a1 pol

val psquare :
  'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 ->
  bool) -> 'a1 pol -> 'a1 pol

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
  'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 ->
  bool) -> ('a1 pol -> 'a1 pol) -> 'a1 pol -> 'a1 pol -> positive -> 'a1 pol

val ppow_N :
  'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 ->
  bool) -> ('a1 pol -> 'a1 pol) -> 'a1 pol -> n -> 'a1 pol

val norm_aux :
  'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 ->
  'a1) -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 pExpr -> 'a1 pol

type 'a bFormula =
| TT
| FF
| X
| A of 'a
| Cj of 'a bFormula * 'a bFormula
| D of 'a bFormula * 'a bFormula
| N of 'a bFormula
| I of 'a bFormula * 'a bFormula

type 'term' clause = 'term' list

type 'term' cnf = 'term' clause list

val tt : 'a1 cnf

val ff : 'a1 cnf

val add_term :
  ('a1 -> bool) -> ('a1 -> 'a1 -> 'a1 option) -> 'a1 -> 'a1 clause -> 'a1
  clause option

val or_clause :
  ('a1 -> bool) -> ('a1 -> 'a1 -> 'a1 option) -> 'a1 clause -> 'a1 clause ->
  'a1 clause option

val or_clause_cnf :
  ('a1 -> bool) -> ('a1 -> 'a1 -> 'a1 option) -> 'a1 clause -> 'a1 cnf -> 'a1
  cnf

val or_cnf :
  ('a1 -> bool) -> ('a1 -> 'a1 -> 'a1 option) -> 'a1 cnf -> 'a1 cnf -> 'a1
  cnf

val and_cnf : 'a1 cnf -> 'a1 cnf -> 'a1 cnf

val xcnf :
  ('a2 -> bool) -> ('a2 -> 'a2 -> 'a2 option) -> ('a1 -> 'a2 cnf) -> ('a1 ->
  'a2 cnf) -> bool -> 'a1 bFormula -> 'a2 cnf

val cnf_checker : ('a1 list -> 'a2 -> bool) -> 'a1 cnf -> 'a2 list -> bool

val tauto_checker :
  ('a2 -> bool) -> ('a2 -> 'a2 -> 'a2 option) -> ('a1 -> 'a2 cnf) -> ('a1 ->
  'a2 cnf) -> ('a2 list -> 'a3 -> bool) -> 'a1 bFormula -> 'a3 list -> bool

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

val map_option2 :
  ('a1 -> 'a2 -> 'a3 option) -> 'a1 option -> 'a2 option -> 'a3 option

val pexpr_times_nformula :
  'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 ->
  bool) -> 'a1 polC -> 'a1 nFormula -> 'a1 nFormula option

val nformula_times_nformula :
  'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 ->
  bool) -> 'a1 nFormula -> 'a1 nFormula -> 'a1 nFormula option

val nformula_plus_nformula :
  'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 nFormula -> 'a1
  nFormula -> 'a1 nFormula option

val eval_Psatz :
  'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 ->
  bool) -> ('a1 -> 'a1 -> bool) -> 'a1 nFormula list -> 'a1 psatz -> 'a1
  nFormula option

val check_inconsistent :
  'a1 -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> bool) -> 'a1 nFormula -> bool

val check_normalised_formulas :
  'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 ->
  bool) -> ('a1 -> 'a1 -> bool) -> 'a1 nFormula list -> 'a1 psatz -> bool

type op2 =
| OpEq
| OpNEq
| OpLe
| OpGe
| OpLt
| OpGt

type 'c formula = { flhs : 'c pExpr; fop : op2; frhs : 'c pExpr }

val flhs : 'a1 formula -> 'a1 pExpr

val fop : 'a1 formula -> op2

val frhs : 'a1 formula -> 'a1 pExpr

val norm :
  'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 ->
  'a1) -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 pExpr -> 'a1 pol

val psub0 :
  'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1) -> ('a1
  -> 'a1 -> bool) -> 'a1 pol -> 'a1 pol -> 'a1 pol

val padd0 :
  'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 pol -> 'a1 pol ->
  'a1 pol

val xnormalise :
  'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 ->
  'a1) -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 formula -> 'a1 nFormula
  list

val cnf_normalise :
  'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 ->
  'a1) -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 formula -> 'a1 nFormula
  cnf

val xnegate :
  'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 ->
  'a1) -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 formula -> 'a1 nFormula
  list

val cnf_negate :
  'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 ->
  'a1) -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 formula -> 'a1 nFormula
  cnf

val xdenorm : positive -> 'a1 pol -> 'a1 pExpr

val denorm : 'a1 pol -> 'a1 pExpr

val simpl_cone :
  'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 psatz ->
  'a1 psatz

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
| Leaf of 'a
| Node of 'a t * 'a * 'a t

val find : 'a1 -> 'a1 t -> positive -> 'a1

type zWitness = z psatz

val zWeakChecker : z nFormula list -> z psatz -> bool

val psub1 : z pol -> z pol -> z pol

val padd1 : z pol -> z pol -> z pol

val norm0 : z pExpr -> z pol

val xnormalise0 : z formula -> z nFormula list

val normalise : z formula -> z nFormula cnf

val xnegate0 : z formula -> z nFormula list

val negate : z formula -> z nFormula cnf

val zunsat : z nFormula -> bool

val zdeduce : z nFormula -> z nFormula -> z nFormula option

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

val zChecker : z nFormula list -> zArithProof -> bool

val zTautoChecker : z formula bFormula -> zArithProof list -> bool

val n_of_Z : z -> n

type qWitness = q psatz

val qWeakChecker : q nFormula list -> q psatz -> bool

val qnormalise : q formula -> q nFormula cnf

val qnegate : q formula -> q nFormula cnf

val qunsat : q nFormula -> bool

val qdeduce : q nFormula -> q nFormula -> q nFormula option

val qTautoChecker : q formula bFormula -> qWitness list -> bool

type rWitness = z psatz

val rWeakChecker : z nFormula list -> z psatz -> bool

val rnormalise : z formula -> z nFormula cnf

val rnegate : z formula -> z nFormula cnf

val runsat : z nFormula -> bool

val rdeduce : z nFormula -> z nFormula -> z nFormula option

val rTautoChecker : z formula bFormula -> rWitness list -> bool

