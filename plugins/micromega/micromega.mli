
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

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val nth : nat -> 'a1 list -> 'a1 -> 'a1

val rev_append : 'a1 list -> 'a1 list -> 'a1 list

val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1

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
  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val pred_double : positive -> positive

  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  val mul : positive -> positive -> positive

  val iter : ('a1 -> 'a1) -> 'a1 -> positive -> 'a1

  val compare_cont : comparison -> positive -> positive -> comparison

  val compare : positive -> positive -> comparison

  val eqb : positive -> positive -> bool

  val of_succ_nat : nat -> positive
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

  val compare_cont : comparison -> positive -> positive -> comparison

  val compare : positive -> positive -> comparison

  val leb : positive -> positive -> bool

  val size_nat : positive -> nat

  val max : positive -> positive -> positive

  val gcdn : nat -> positive -> positive -> positive

  val gcd : positive -> positive -> positive
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

  val eqb : z -> z -> bool

  val max : z -> z -> z

  val of_nat : nat -> z

  val of_N : n -> z

  val pos_div_eucl : positive -> z -> z * z

  val div_eucl : z -> z -> z * z

  val div : z -> z -> z

  val gtb : z -> z -> bool

  val abs : z -> z

  val to_N : z -> n

  val gcd : z -> z -> z

  val lcm : z -> z -> z
 end

type 'c pExpr =
| PEc of 'c
| PEX of positive
| PEadd of 'c pExpr * 'c pExpr
| PEsub of 'c pExpr * 'c pExpr
| PEmul of 'c pExpr * 'c pExpr
| PEopp of 'c pExpr
| PEpow of 'c pExpr * n

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

val paddI : ('a1 -> 'a1 -> 'a1) -> ('a1 pol -> 'a1 pol -> 'a1 pol) -> 'a1 pol -> positive -> 'a1 pol -> 'a1 pol

val psubI : ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1) -> ('a1 pol -> 'a1 pol -> 'a1 pol) -> 'a1 pol -> positive -> 'a1 pol -> 'a1 pol

val paddX : 'a1 -> ('a1 -> 'a1 -> bool) -> ('a1 pol -> 'a1 pol -> 'a1 pol) -> 'a1 pol -> positive -> 'a1 pol -> 'a1 pol

val psubX :
  'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> ('a1 pol -> 'a1 pol -> 'a1 pol) -> 'a1 pol -> positive -> 'a1 pol -> 'a1 pol

val padd : 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 pol -> 'a1 pol -> 'a1 pol

val psub :
  'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 pol -> 'a1 pol -> 'a1 pol

val pmulC_aux : 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 pol -> 'a1 -> 'a1 pol

val pmulC : 'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 pol -> 'a1 -> 'a1 pol

val pmulI :
  'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> ('a1 pol -> 'a1 pol -> 'a1 pol) -> 'a1 pol -> positive -> 'a1 pol ->
  'a1 pol

val pmul : 'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 pol -> 'a1 pol -> 'a1 pol

val psquare : 'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 pol -> 'a1 pol

val mk_X : 'a1 -> 'a1 -> positive -> 'a1 pol

val ppow_pos :
  'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> ('a1 pol -> 'a1 pol) -> 'a1 pol -> 'a1 pol ->
  positive -> 'a1 pol

val ppow_N :
  'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> ('a1 pol -> 'a1 pol) -> 'a1 pol -> n -> 'a1
  pol

val norm_aux :
  'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1
  pExpr -> 'a1 pol

type kind =
| IsProp
| IsBool

type 'a trace =
| Null
| Push of 'a * 'a trace
| Merge of 'a trace * 'a trace

type ('tA, 'tX, 'aA, 'aF) gFormula =
| TT of kind
| FF of kind
| X of kind * 'tX
| A of kind * 'tA * 'aA
| AND of kind * ('tA, 'tX, 'aA, 'aF) gFormula * ('tA, 'tX, 'aA, 'aF) gFormula
| OR of kind * ('tA, 'tX, 'aA, 'aF) gFormula * ('tA, 'tX, 'aA, 'aF) gFormula
| NOT of kind * ('tA, 'tX, 'aA, 'aF) gFormula
| IMPL of kind * ('tA, 'tX, 'aA, 'aF) gFormula * 'aF option * ('tA, 'tX, 'aA, 'aF) gFormula
| IFF of kind * ('tA, 'tX, 'aA, 'aF) gFormula * ('tA, 'tX, 'aA, 'aF) gFormula
| EQ of ('tA, 'tX, 'aA, 'aF) gFormula * ('tA, 'tX, 'aA, 'aF) gFormula

val mapX : (kind -> 'a2 -> 'a2) -> kind -> ('a1, 'a2, 'a3, 'a4) gFormula -> ('a1, 'a2, 'a3, 'a4) gFormula

val foldA : ('a5 -> 'a3 -> 'a5) -> kind -> ('a1, 'a2, 'a3, 'a4) gFormula -> 'a5 -> 'a5

val cons_id : 'a1 option -> 'a1 list -> 'a1 list

val ids_of_formula : kind -> ('a1, 'a2, 'a3, 'a4) gFormula -> 'a4 list

val collect_annot : kind -> ('a1, 'a2, 'a3, 'a4) gFormula -> 'a3 list

type rtyp = __

type eKind = __

type 'a bFormula = ('a, eKind, unit0, unit0) gFormula

val map_bformula : kind -> ('a1 -> 'a2) -> ('a1, 'a3, 'a4, 'a5) gFormula -> ('a2, 'a3, 'a4, 'a5) gFormula

type ('x, 'annot) clause = ('x * 'annot) list

type ('x, 'annot) cnf = ('x, 'annot) clause list

val cnf_tt : ('a1, 'a2) cnf

val cnf_ff : ('a1, 'a2) cnf

val add_term : ('a1 -> bool) -> ('a1 -> 'a1 -> 'a1 option) -> ('a1 * 'a2) -> ('a1, 'a2) clause -> ('a1, 'a2) clause option

val or_clause : ('a1 -> bool) -> ('a1 -> 'a1 -> 'a1 option) -> ('a1, 'a2) clause -> ('a1, 'a2) clause -> ('a1, 'a2) clause option

val xor_clause_cnf : ('a1 -> bool) -> ('a1 -> 'a1 -> 'a1 option) -> ('a1, 'a2) clause -> ('a1, 'a2) cnf -> ('a1, 'a2) cnf

val or_clause_cnf : ('a1 -> bool) -> ('a1 -> 'a1 -> 'a1 option) -> ('a1, 'a2) clause -> ('a1, 'a2) cnf -> ('a1, 'a2) cnf

val or_cnf : ('a1 -> bool) -> ('a1 -> 'a1 -> 'a1 option) -> ('a1, 'a2) cnf -> ('a1, 'a2) cnf -> ('a1, 'a2) cnf

val and_cnf : ('a1, 'a2) cnf -> ('a1, 'a2) cnf -> ('a1, 'a2) cnf

type ('term, 'annot, 'tX, 'aF) tFormula = ('term, 'tX, 'annot, 'aF) gFormula

val is_cnf_tt : ('a1, 'a2) cnf -> bool

val is_cnf_ff : ('a1, 'a2) cnf -> bool

val and_cnf_opt : ('a1, 'a2) cnf -> ('a1, 'a2) cnf -> ('a1, 'a2) cnf

val or_cnf_opt : ('a1 -> bool) -> ('a1 -> 'a1 -> 'a1 option) -> ('a1, 'a2) cnf -> ('a1, 'a2) cnf -> ('a1, 'a2) cnf

val mk_and :
  ('a2 -> bool) -> ('a2 -> 'a2 -> 'a2 option) -> (bool -> kind -> ('a1, 'a3, 'a4, 'a5) tFormula -> ('a2, 'a3) cnf) -> kind -> bool
  -> ('a1, 'a3, 'a4, 'a5) tFormula -> ('a1, 'a3, 'a4, 'a5) tFormula -> ('a2, 'a3) cnf

val mk_or :
  ('a2 -> bool) -> ('a2 -> 'a2 -> 'a2 option) -> (bool -> kind -> ('a1, 'a3, 'a4, 'a5) tFormula -> ('a2, 'a3) cnf) -> kind -> bool
  -> ('a1, 'a3, 'a4, 'a5) tFormula -> ('a1, 'a3, 'a4, 'a5) tFormula -> ('a2, 'a3) cnf

val mk_impl :
  ('a2 -> bool) -> ('a2 -> 'a2 -> 'a2 option) -> (bool -> kind -> ('a1, 'a3, 'a4, 'a5) tFormula -> ('a2, 'a3) cnf) -> kind -> bool
  -> ('a1, 'a3, 'a4, 'a5) tFormula -> ('a1, 'a3, 'a4, 'a5) tFormula -> ('a2, 'a3) cnf

val mk_iff :
  ('a2 -> bool) -> ('a2 -> 'a2 -> 'a2 option) -> (bool -> kind -> ('a1, 'a3, 'a4, 'a5) tFormula -> ('a2, 'a3) cnf) -> kind -> bool
  -> ('a1, 'a3, 'a4, 'a5) tFormula -> ('a1, 'a3, 'a4, 'a5) tFormula -> ('a2, 'a3) cnf

val is_bool : kind -> ('a1, 'a2, 'a3, 'a4) tFormula -> bool option

val xcnf :
  ('a2 -> bool) -> ('a2 -> 'a2 -> 'a2 option) -> ('a1 -> 'a3 -> ('a2, 'a3) cnf) -> ('a1 -> 'a3 -> ('a2, 'a3) cnf) -> bool -> kind
  -> ('a1, 'a3, 'a4, 'a5) tFormula -> ('a2, 'a3) cnf

val radd_term :
  ('a1 -> bool) -> ('a1 -> 'a1 -> 'a1 option) -> ('a1 * 'a2) -> ('a1, 'a2) clause -> (('a1, 'a2) clause, 'a2 trace) sum

val ror_clause :
  ('a1 -> bool) -> ('a1 -> 'a1 -> 'a1 option) -> ('a1 * 'a2) list -> ('a1, 'a2) clause -> (('a1, 'a2) clause, 'a2 trace) sum

val xror_clause_cnf :
  ('a1 -> bool) -> ('a1 -> 'a1 -> 'a1 option) -> ('a1 * 'a2) list -> ('a1, 'a2) clause list -> ('a1, 'a2) clause list * 'a2 trace

val ror_clause_cnf :
  ('a1 -> bool) -> ('a1 -> 'a1 -> 'a1 option) -> ('a1 * 'a2) list -> ('a1, 'a2) clause list -> ('a1, 'a2) clause list * 'a2 trace

val ror_cnf :
  ('a1 -> bool) -> ('a1 -> 'a1 -> 'a1 option) -> ('a1, 'a2) clause list -> ('a1, 'a2) clause list -> ('a1, 'a2) cnf * 'a2 trace

val ror_cnf_opt : ('a1 -> bool) -> ('a1 -> 'a1 -> 'a1 option) -> ('a1, 'a2) cnf -> ('a1, 'a2) cnf -> ('a1, 'a2) cnf * 'a2 trace

val ratom : ('a1, 'a2) cnf -> 'a2 -> ('a1, 'a2) cnf * 'a2 trace

val rxcnf_and :
  ('a2 -> bool) -> ('a2 -> 'a2 -> 'a2 option) -> (bool -> kind -> ('a1, 'a3, 'a4, 'a5) tFormula -> ('a2, 'a3) cnf * 'a3 trace) ->
  bool -> kind -> ('a1, 'a3, 'a4, 'a5) tFormula -> ('a1, 'a3, 'a4, 'a5) tFormula -> ('a2, 'a3) cnf * 'a3 trace

val rxcnf_or :
  ('a2 -> bool) -> ('a2 -> 'a2 -> 'a2 option) -> (bool -> kind -> ('a1, 'a3, 'a4, 'a5) tFormula -> ('a2, 'a3) cnf * 'a3 trace) ->
  bool -> kind -> ('a1, 'a3, 'a4, 'a5) tFormula -> ('a1, 'a3, 'a4, 'a5) tFormula -> ('a2, 'a3) cnf * 'a3 trace

val rxcnf_impl :
  ('a2 -> bool) -> ('a2 -> 'a2 -> 'a2 option) -> (bool -> kind -> ('a1, 'a3, 'a4, 'a5) tFormula -> ('a2, 'a3) cnf * 'a3 trace) ->
  bool -> kind -> ('a1, 'a3, 'a4, 'a5) tFormula -> ('a1, 'a3, 'a4, 'a5) tFormula -> ('a2, 'a3) cnf * 'a3 trace

val rxcnf_iff :
  ('a2 -> bool) -> ('a2 -> 'a2 -> 'a2 option) -> (bool -> kind -> ('a1, 'a3, 'a4, 'a5) tFormula -> ('a2, 'a3) cnf * 'a3 trace) ->
  bool -> kind -> ('a1, 'a3, 'a4, 'a5) tFormula -> ('a1, 'a3, 'a4, 'a5) tFormula -> ('a2, 'a3) cnf * 'a3 trace

val rxcnf :
  ('a2 -> bool) -> ('a2 -> 'a2 -> 'a2 option) -> ('a1 -> 'a3 -> ('a2, 'a3) cnf) -> ('a1 -> 'a3 -> ('a2, 'a3) cnf) -> bool -> kind
  -> ('a1, 'a3, 'a4, 'a5) tFormula -> ('a2, 'a3) cnf * 'a3 trace

type ('term, 'annot, 'tX) to_constrT = { mkTT : (kind -> 'tX); mkFF : (kind -> 'tX); mkA : (kind -> 'term -> 'annot -> 'tX);
                                         mkAND : (kind -> 'tX -> 'tX -> 'tX); mkOR : (kind -> 'tX -> 'tX -> 'tX);
                                         mkIMPL : (kind -> 'tX -> 'tX -> 'tX); mkIFF : (kind -> 'tX -> 'tX -> 'tX);
                                         mkNOT : (kind -> 'tX -> 'tX); mkEQ : ('tX -> 'tX -> 'tX) }

val aformula : ('a1, 'a2, 'a3) to_constrT -> kind -> ('a1, 'a2, 'a3, 'a4) tFormula -> 'a3

val is_X : kind -> ('a1, 'a2, 'a3, 'a4) tFormula -> 'a3 option

val abs_and :
  ('a1, 'a2, 'a3) to_constrT -> kind -> ('a1, 'a2, 'a3, 'a4) tFormula -> ('a1, 'a2, 'a3, 'a4) tFormula -> (kind -> ('a1, 'a2, 'a3,
  'a4) tFormula -> ('a1, 'a2, 'a3, 'a4) tFormula -> ('a1, 'a2, 'a3, 'a4) tFormula) -> ('a1, 'a3, 'a2, 'a4) gFormula

val abs_or :
  ('a1, 'a2, 'a3) to_constrT -> kind -> ('a1, 'a2, 'a3, 'a4) tFormula -> ('a1, 'a2, 'a3, 'a4) tFormula -> (kind -> ('a1, 'a2, 'a3,
  'a4) tFormula -> ('a1, 'a2, 'a3, 'a4) tFormula -> ('a1, 'a2, 'a3, 'a4) tFormula) -> ('a1, 'a3, 'a2, 'a4) gFormula

val abs_not :
  ('a1, 'a2, 'a3) to_constrT -> kind -> ('a1, 'a2, 'a3, 'a4) tFormula -> (kind -> ('a1, 'a2, 'a3, 'a4) tFormula -> ('a1, 'a2, 'a3,
  'a4) tFormula) -> ('a1, 'a3, 'a2, 'a4) gFormula

val mk_arrow : 'a4 option -> kind -> ('a1, 'a2, 'a3, 'a4) tFormula -> ('a1, 'a2, 'a3, 'a4) tFormula -> ('a1, 'a2, 'a3, 'a4) tFormula

val abst_simpl :
  ('a1, 'a2, 'a3) to_constrT -> ('a2 -> bool) -> kind -> ('a1, 'a2, 'a3, 'a4) tFormula -> ('a1, 'a2, 'a3, 'a4) tFormula

val abst_and :
  ('a1, 'a2, 'a3) to_constrT -> (bool -> kind -> ('a1, 'a2, 'a3, 'a4) tFormula -> ('a1, 'a2, 'a3, 'a4) tFormula) -> bool -> kind ->
  ('a1, 'a2, 'a3, 'a4) tFormula -> ('a1, 'a2, 'a3, 'a4) tFormula -> ('a1, 'a2, 'a3, 'a4) tFormula

val abst_or :
  ('a1, 'a2, 'a3) to_constrT -> (bool -> kind -> ('a1, 'a2, 'a3, 'a4) tFormula -> ('a1, 'a2, 'a3, 'a4) tFormula) -> bool -> kind ->
  ('a1, 'a2, 'a3, 'a4) tFormula -> ('a1, 'a2, 'a3, 'a4) tFormula -> ('a1, 'a2, 'a3, 'a4) tFormula

val abst_impl :
  ('a1, 'a2, 'a3) to_constrT -> (bool -> kind -> ('a1, 'a2, 'a3, 'a4) tFormula -> ('a1, 'a2, 'a3, 'a4) tFormula) -> bool -> 'a4
  option -> kind -> ('a1, 'a2, 'a3, 'a4) tFormula -> ('a1, 'a2, 'a3, 'a4) tFormula -> ('a1, 'a2, 'a3, 'a4) tFormula

val or_is_X : kind -> ('a1, 'a2, 'a3, 'a4) tFormula -> ('a1, 'a2, 'a3, 'a4) tFormula -> bool

val abs_iff :
  ('a1, 'a2, 'a3) to_constrT -> kind -> ('a1, 'a2, 'a3, 'a4) tFormula -> ('a1, 'a2, 'a3, 'a4) tFormula -> ('a1, 'a2, 'a3, 'a4)
  tFormula -> ('a1, 'a2, 'a3, 'a4) tFormula -> kind -> ('a1, 'a2, 'a3, 'a4) tFormula -> ('a1, 'a2, 'a3, 'a4) tFormula

val abst_iff :
  ('a1, 'a2, 'a3) to_constrT -> ('a2 -> bool) -> (bool -> kind -> ('a1, 'a2, 'a3, 'a4) tFormula -> ('a1, 'a2, 'a3, 'a4) tFormula)
  -> bool -> kind -> ('a1, 'a2, 'a3, 'a4) tFormula -> ('a1, 'a2, 'a3, 'a4) tFormula -> ('a1, 'a2, 'a3, 'a4) tFormula

val abst_eq :
  ('a1, 'a2, 'a3) to_constrT -> ('a2 -> bool) -> (bool -> kind -> ('a1, 'a2, 'a3, 'a4) tFormula -> ('a1, 'a2, 'a3, 'a4) tFormula)
  -> bool -> ('a1, 'a2, 'a3, 'a4) tFormula -> ('a1, 'a2, 'a3, 'a4) tFormula -> ('a1, 'a2, 'a3, 'a4) tFormula

val abst_form :
  ('a1, 'a2, 'a3) to_constrT -> ('a2 -> bool) -> bool -> kind -> ('a1, 'a2, 'a3, 'a4) tFormula -> ('a1, 'a2, 'a3, 'a4) tFormula

val cnf_checker : (('a1 * 'a2) list -> 'a3 -> bool) -> ('a1, 'a2) cnf -> 'a3 list -> bool

val tauto_checker :
  ('a2 -> bool) -> ('a2 -> 'a2 -> 'a2 option) -> ('a1 -> 'a3 -> ('a2, 'a3) cnf) -> ('a1 -> 'a3 -> ('a2, 'a3) cnf) -> (('a2 * 'a3)
  list -> 'a4 -> bool) -> ('a1, rtyp, 'a3, unit0) gFormula -> 'a4 list -> bool

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
| PsatzLet of 'c psatz * 'c psatz
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
  'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 polC -> 'a1 nFormula -> 'a1 nFormula
  option

val nformula_times_nformula :
  'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 nFormula -> 'a1 nFormula -> 'a1 nFormula
  option

val nformula_plus_nformula :
  'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 nFormula -> 'a1 nFormula -> 'a1 nFormula option

val eval_Psatz :
  'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> bool) -> 'a1 nFormula list ->
  'a1 psatz -> 'a1 nFormula option

val check_inconsistent : 'a1 -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> bool) -> 'a1 nFormula -> bool

val check_normalised_formulas :
  'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> bool) -> 'a1 nFormula list ->
  'a1 psatz -> bool

type op2 =
| OpEq
| OpNEq
| OpLe
| OpGe
| OpLt
| OpGt

type 't formula = { flhs : 't pExpr; fop : op2; frhs : 't pExpr }

val norm :
  'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1
  pExpr -> 'a1 pol

val psub0 :
  'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 pol -> 'a1 pol -> 'a1 pol

val padd0 : 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 pol -> 'a1 pol -> 'a1 pol

val popp0 : ('a1 -> 'a1) -> 'a1 pol -> 'a1 pol

val normalise :
  'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1
  formula -> 'a1 nFormula

val xnormalise : ('a1 -> 'a1) -> 'a1 nFormula -> 'a1 nFormula list

val xnegate : ('a1 -> 'a1) -> 'a1 nFormula -> 'a1 nFormula list

val cnf_of_list : 'a1 -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> bool) -> 'a1 nFormula list -> 'a2 -> ('a1 nFormula, 'a2) cnf

val cnf_normalise :
  'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> ('a1
  -> 'a1 -> bool) -> 'a1 formula -> 'a2 -> ('a1 nFormula, 'a2) cnf

val cnf_negate :
  'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> ('a1
  -> 'a1 -> bool) -> 'a1 formula -> 'a2 -> ('a1 nFormula, 'a2) cnf

val xdenorm : positive -> 'a1 pol -> 'a1 pExpr

val denorm : 'a1 pol -> 'a1 pExpr

val map_PExpr : ('a2 -> 'a1) -> 'a2 pExpr -> 'a1 pExpr

val map_Formula : ('a2 -> 'a1) -> 'a2 formula -> 'a1 formula

val simpl_cone : 'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 psatz -> 'a1 psatz

module PositiveSet :
 sig
  type elt = positive

  type tree =
  | Leaf
  | Node of tree * bool * tree

  type t = tree

  val empty : t

  val mem : elt -> t -> bool

  val add : elt -> t -> t
 end

type q = { qnum : z; qden : positive }

val qeq_bool : q -> q -> bool

val qle_bool : q -> q -> bool

val qplus : q -> q -> q

val qmult : q -> q -> q

val qopp : q -> q

val qminus : q -> q -> q

val qinv : q -> q

val qpower_positive : q -> positive -> q

val qpower : q -> z -> q

type 'a t0 =
| Empty
| Elt of 'a
| Branch of 'a t0 * 'a * 'a t0

val find : 'a1 -> 'a1 t0 -> positive -> 'a1

val singleton : 'a1 -> positive -> 'a1 -> 'a1 t0

val vm_add : 'a1 -> positive -> 'a1 -> 'a1 t0 -> 'a1 t0

val psub1 : z pol -> z pol -> z pol

val popp1 : z pol -> z pol

val padd1 : z pol -> z pol -> z pol

val norm0 : z pExpr -> z pol

val zunsat : z nFormula -> bool

val zdeduce : z nFormula -> z nFormula -> z nFormula option

val xnnormalise : z formula -> z nFormula

val xis_integral : (positive -> bool) -> positive -> z pol -> bool

val get : PositiveSet.t -> PositiveSet.elt -> bool

val oget : PositiveSet.t option -> positive -> bool

val is_integral : PositiveSet.t option -> z pol -> bool

val ceiling : z -> z -> z

type zWitness = z psatz

type zArithProof =
| DoneProof
| RatProof of zWitness * zArithProof
| CutProof of zWitness * zArithProof
| SplitProof of z polC * zArithProof * zArithProof
| EnumProof of zWitness * zWitness * zArithProof list
| ExProof of positive * zArithProof

val zgcdM : z -> z -> z

val zgcd_pol : z polC -> z * z

val zdiv_pol : z polC -> z -> z polC

val makeCuttingPlane : z polC -> z polC * z

val genCuttingPlane : z nFormula -> ((z polC * z) * op1) option

val nformula_of_cutting_plane : ((z polC * z) * op1) -> z nFormula

val is_pol_Z0 : z polC -> bool

val eval_Psatz0 : z nFormula list -> zWitness -> z nFormula option

val valid_cut_sign : op1 -> bool

val bound_var : positive -> z formula

val mk_eq_pos : positive -> positive -> positive -> z formula

val max_var : positive -> z pol -> positive

val max_var_nformulae : z nFormula list -> positive

val add0 : positive -> PositiveSet.t option -> PositiveSet.t option

val zChecker : PositiveSet.t option -> z nFormula list -> zArithProof -> bool

val zeval_const : z pExpr -> z option

val zWeakChecker : z nFormula list -> z psatz -> bool

val normZ : z pExpr -> z pol

val cnf_of_list0 : 'a1 -> z nFormula list -> (z nFormula * 'a1) list list

val xnormalise0 : z nFormula -> z nFormula list

val normalise0 : z formula -> 'a1 -> (z nFormula, 'a1) cnf

val xnegate0 : z nFormula -> z nFormula list

val negate : z formula -> 'a1 -> (z nFormula, 'a1) cnf

val cnfZ : kind -> (z formula, 'a1, 'a2, 'a3) tFormula -> (z nFormula, 'a1) cnf * 'a1 trace

val zTautoChecker : z formula bFormula -> zArithProof list -> bool

type qWitness = q psatz

val qWeakChecker : q nFormula list -> q psatz -> bool

val qnormalise : q formula -> 'a1 -> (q nFormula, 'a1) cnf

val qnegate : q formula -> 'a1 -> (q nFormula, 'a1) cnf

val qunsat : q nFormula -> bool

val qdeduce : q nFormula -> q nFormula -> q nFormula option

val normQ : q pExpr -> q pol

val cnfQ : kind -> (q formula, 'a1, 'a2, 'a3) tFormula -> (q nFormula, 'a1) cnf * 'a1 trace

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

type rWitness = zArithProof

val rnormalise : q formula -> 'a1 -> (q nFormula, 'a1) cnf

val rnegate : q formula -> 'a1 -> (q nFormula, 'a1) cnf

val runsat : q nFormula -> bool

val rdeduce : q nFormula -> q nFormula -> q nFormula option

type 'form eFormula =
| IsZ of bool * positive
| IsF of 'form

val map_eFormula : ('a1 -> 'a2) -> 'a1 formula eFormula -> 'a2 formula eFormula

val lcm0 : q pol -> z

val polZ : z -> q pol -> z pol

val nformulaZ : q nFormula -> z nFormula

val xcollect_isZ : PositiveSet.t -> z nFormula list -> (q nFormula eFormula * unit0) list -> PositiveSet.t * z nFormula list

val qCheck : (q nFormula eFormula * unit0) list -> zArithProof -> bool

val erunsat : q nFormula eFormula -> bool

val erdeduce : q nFormula eFormula -> q nFormula eFormula -> q nFormula eFormula option

val map_cnf : ('a2 -> 'a3) -> ('a2, 'a1) cnf -> ('a3, 'a1) cnf

val eRnormalise : q formula eFormula -> 'a1 -> (q nFormula eFormula, 'a1) cnf

val eRnegate : q formula eFormula -> 'a1 -> (q nFormula eFormula, 'a1) cnf

val cnfR : kind -> (q formula eFormula, 'a1, 'a2, 'a3) tFormula -> (q nFormula eFormula, 'a1) cnf * 'a1 trace

val rTautoChecker : rcst formula eFormula bFormula -> rWitness list -> bool
