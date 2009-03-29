type __ = Obj.t

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

val nth : nat -> 'a1 list -> 'a1 -> 'a1

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

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

val pcompare : positive -> positive -> comparison -> comparison

type n =
  | N0
  | Npos of positive

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

val dcompare_inf : comparison -> bool option

val zcompare_rec : z -> z -> (__ -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1

val z_gt_dec : z -> z -> bool

val zle_bool : z -> z -> bool

val zge_bool : z -> z -> bool

val zgt_bool : z -> z -> bool

val zeq_bool : z -> z -> bool

val n_of_nat : nat -> n

val zdiv_eucl_POS : positive -> z -> z  *  z

val zdiv_eucl : z -> z -> z  *  z

type 'c pol =
  | Pc of 'c
  | Pinj of positive * 'c pol
  | PX of 'c pol * positive * 'c pol

val p0 : 'a1 -> 'a1 pol

val p1 : 'a1 -> 'a1 pol

val peq : ('a1 -> 'a1 -> bool) -> 'a1 pol -> 'a1 pol -> bool

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

val or_clause_cnf : 'a1 clause -> 'a1 cnf -> 'a1 cnf

val or_cnf : 'a1 cnf -> 'a1 cnf -> 'a1 cnf

val and_cnf : 'a1 cnf -> 'a1 cnf -> 'a1 cnf

val xcnf :
  ('a1 -> 'a2 cnf) -> ('a1 -> 'a2 cnf) -> bool -> 'a1 bFormula -> 'a2 cnf

val cnf_checker : ('a1 list -> 'a2 -> bool) -> 'a1 cnf -> 'a2 list -> bool

val tauto_checker :
  ('a1 -> 'a2 cnf) -> ('a1 -> 'a2 cnf) -> ('a2 list -> 'a3 -> bool) -> 'a1
  bFormula -> 'a3 list -> bool

type 'c pExprC = 'c pExpr

type 'c polC = 'c pol

type op1 =
  | Equal
  | NonEqual
  | Strict
  | NonStrict

type 'c nFormula = 'c pExprC  *  op1

type monoidMember = nat list

type 'c coneMember =
  | S_In of nat
  | S_Ideal of 'c pExprC * 'c coneMember
  | S_Square of 'c pExprC
  | S_Monoid of monoidMember
  | S_Mult of 'c coneMember * 'c coneMember
  | S_Add of 'c coneMember * 'c coneMember
  | S_Pos of 'c
  | S_Z

val nformula_times : 'a1 nFormula -> 'a1 nFormula -> 'a1 nFormula

val nformula_plus : 'a1 nFormula -> 'a1 nFormula -> 'a1 nFormula

val eval_monoid : 'a1 -> 'a1 nFormula list -> monoidMember -> 'a1 pExprC

val eval_cone :
  'a1 -> 'a1 -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> bool) -> 'a1 nFormula
  list -> 'a1 coneMember -> 'a1 nFormula

val normalise_pexpr :
  'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 ->
  'a1) -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 pExprC -> 'a1 polC

val check_inconsistent :
  'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 ->
  'a1) -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> bool) -> 'a1
  nFormula -> bool

val check_normalised_formulas :
  'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 ->
  'a1) -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> bool) -> 'a1
  nFormula list -> 'a1 coneMember -> bool

type op2 =
  | OpEq
  | OpNEq
  | OpLe
  | OpGe
  | OpLt
  | OpGt

type 'c formula = { flhs : 'c pExprC; fop : op2; frhs : 'c pExprC }

val flhs : 'a1 formula -> 'a1 pExprC

val fop : 'a1 formula -> op2

val frhs : 'a1 formula -> 'a1 pExprC

val xnormalise : 'a1 formula -> 'a1 nFormula list

val cnf_normalise : 'a1 formula -> 'a1 nFormula cnf

val xnegate : 'a1 formula -> 'a1 nFormula list

val cnf_negate : 'a1 formula -> 'a1 nFormula cnf

val simpl_expr : 'a1 -> ('a1 -> 'a1 -> bool) -> 'a1 pExprC -> 'a1 pExprC

val simpl_cone :
  'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 coneMember
  -> 'a1 coneMember

type q = { qnum : z; qden : positive }

val qnum : q -> z

val qden : q -> positive

val qeq_bool : q -> q -> bool

val qle_bool : q -> q -> bool

val qplus : q -> q -> q

val qmult : q -> q -> q

val qopp : q -> q

val qminus : q -> q -> q

type 'a t =
  | Empty
  | Leaf of 'a
  | Node of 'a t * 'a * 'a t

val find : 'a1 -> 'a1 t -> positive -> 'a1

type zWitness = z coneMember

val zWeakChecker : z nFormula list -> z coneMember -> bool

val xnormalise0 : z formula -> z nFormula list

val normalise : z formula -> z nFormula cnf

val xnegate0 : z formula -> z nFormula list

val negate : z formula -> z nFormula cnf

val ceiling : z -> z -> z

type proofTerm =
  | RatProof of zWitness
  | CutProof of z pExprC * q * zWitness * proofTerm
  | EnumProof of q * z pExprC * q * zWitness * zWitness * proofTerm list

val makeLb : z pExpr -> q -> z nFormula

val qceiling : q -> z

val makeLbCut : z pExprC -> q -> z nFormula

val neg_nformula : z nFormula -> z pExpr  *  op1

val cutChecker :
  z nFormula list -> z pExpr -> q -> zWitness -> z nFormula option

val zChecker : z nFormula list -> proofTerm -> bool

val zTautoChecker : z formula bFormula -> proofTerm list -> bool

val map_cone : (nat -> nat) -> zWitness -> zWitness

val indexes : zWitness -> nat list

val n_of_Z : z -> n

type qWitness = q coneMember

val qWeakChecker : q nFormula list -> q coneMember -> bool

val qTautoChecker : q formula bFormula -> qWitness list -> bool

