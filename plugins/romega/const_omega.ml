(*************************************************************************

   PROJET RNRT Calife - 2001
   Author: Pierre Crégut - France Télécom R&D
   Licence : LGPL version 2.1

 *************************************************************************)

let module_refl_name = "ReflOmegaCore"
let module_refl_path = ["Coq"; "romega"; module_refl_name]

type result =
   Kvar of string
 | Kapp of string * Term.constr list
 | Kimp of Term.constr * Term.constr
 | Kufo;;

let meaningful_submodule = [ "Z"; "N"; "Pos" ]

let string_of_global r =
  let dp = Nametab.dirpath_of_global r in
  let prefix = match Names.DirPath.repr dp with
    | [] -> ""
    | m::_ ->
      let s = Names.Id.to_string m in
      if Util.String.List.mem s meaningful_submodule then s^"." else ""
  in
  prefix^(Names.Id.to_string (Nametab.basename_of_global r))

let destructurate t =
  let c, args = Term.decompose_app t in
  match Term.kind_of_term c, args with
    | Term.Const (sp,_), args ->
	Kapp (string_of_global (Globnames.ConstRef sp), args)
    | Term.Construct (csp,_) , args ->
	Kapp (string_of_global (Globnames.ConstructRef csp), args)
    | Term.Ind (isp,_), args ->
	Kapp (string_of_global (Globnames.IndRef isp), args)
    | Term.Var id,[] -> Kvar(Names.Id.to_string id)
    | Term.Prod (Names.Anonymous,typ,body), [] -> Kimp(typ,body)
    | Term.Prod (Names.Name _,_,_),[] ->
	Errors.error "Omega: Not a quantifier-free goal"
    | _ -> Kufo

exception Destruct

let dest_const_apply t =
  let f,args = Term.decompose_app t in
  let ref =
  match Term.kind_of_term f with
    | Term.Const (sp,_)      -> Globnames.ConstRef sp
    | Term.Construct (csp,_) -> Globnames.ConstructRef csp
    | Term.Ind (isp,_)       -> Globnames.IndRef isp
    | _ -> raise Destruct
  in  Nametab.basename_of_global ref, args

let logic_dir = ["Coq";"Logic";"Decidable"]

let coq_modules =
  Coqlib.init_modules @ [logic_dir] @ Coqlib.arith_modules @ Coqlib.zarith_base_modules
    @ [["Coq"; "Lists"; "List"]]
    @ [module_refl_path]
    @ [module_refl_path@["ZOmega"]]

let bin_module = [["Coq";"Numbers";"BinNums"]]
let z_module = [["Coq";"ZArith";"BinInt"]]

let init_constant = Coqlib.gen_constant_in_modules "Omega" Coqlib.init_modules
let constant = Coqlib.gen_constant_in_modules "Omega" coq_modules
let z_constant = Coqlib.gen_constant_in_modules "Omega" z_module
let bin_constant = Coqlib.gen_constant_in_modules "Omega" bin_module

(* Logic *)
let coq_refl_equal = lazy(init_constant  "eq_refl")
let coq_and = lazy(init_constant "and")
let coq_not = lazy(init_constant "not")
let coq_or = lazy(init_constant "or")
let coq_True = lazy(init_constant "True")
let coq_False = lazy(init_constant "False")
let coq_I = lazy(init_constant "I")

(* ReflOmegaCore/ZOmega *)

let coq_h_step = lazy (constant "h_step")
let coq_pair_step = lazy (constant  "pair_step")
let coq_p_left = lazy (constant  "P_LEFT")
let coq_p_right = lazy (constant  "P_RIGHT")
let coq_p_invert = lazy (constant  "P_INVERT")
let coq_p_step = lazy (constant  "P_STEP")

let coq_t_int = lazy (constant  "Tint")
let coq_t_plus = lazy (constant  "Tplus")
let coq_t_mult = lazy (constant  "Tmult")
let coq_t_opp = lazy (constant  "Topp")
let coq_t_minus = lazy (constant  "Tminus")
let coq_t_var = lazy (constant  "Tvar")

let coq_proposition = lazy (constant  "proposition")
let coq_p_eq = lazy (constant  "EqTerm")
let coq_p_leq = lazy (constant  "LeqTerm")
let coq_p_geq = lazy (constant  "GeqTerm")
let coq_p_lt = lazy (constant  "LtTerm")
let coq_p_gt = lazy (constant  "GtTerm")
let coq_p_neq = lazy (constant  "NeqTerm")
let coq_p_true = lazy (constant  "TrueTerm")
let coq_p_false = lazy (constant  "FalseTerm")
let coq_p_not = lazy (constant  "Tnot")
let coq_p_or = lazy (constant  "Tor")
let coq_p_and = lazy (constant  "Tand")
let coq_p_imp = lazy (constant  "Timp")
let coq_p_prop = lazy (constant  "Tprop")

(* Constructors for shuffle tactic *)
let coq_t_fusion =  lazy (constant  "t_fusion")
let coq_f_equal =  lazy (constant  "F_equal")
let coq_f_cancel =  lazy (constant  "F_cancel")
let coq_f_left =  lazy (constant  "F_left")
let coq_f_right =  lazy (constant  "F_right")

(* Constructors for reordering tactics *)
let coq_c_do_both = lazy (constant  "C_DO_BOTH")
let coq_c_do_left = lazy (constant  "C_LEFT")
let coq_c_do_right = lazy (constant  "C_RIGHT")
let coq_c_do_seq = lazy (constant  "C_SEQ")
let coq_c_nop = lazy (constant  "C_NOP")
let coq_c_opp_plus = lazy (constant  "C_OPP_PLUS")
let coq_c_opp_opp = lazy (constant  "C_OPP_OPP")
let coq_c_opp_mult_r = lazy (constant  "C_OPP_MULT_R")
let coq_c_opp_one = lazy (constant  "C_OPP_ONE")
let coq_c_reduce = lazy (constant  "C_REDUCE")
let coq_c_mult_plus_distr = lazy (constant  "C_MULT_PLUS_DISTR")
let coq_c_opp_left = lazy (constant  "C_MULT_OPP_LEFT")
let coq_c_mult_assoc_r = lazy (constant  "C_MULT_ASSOC_R")
let coq_c_plus_assoc_r = lazy (constant  "C_PLUS_ASSOC_R")
let coq_c_plus_assoc_l = lazy (constant  "C_PLUS_ASSOC_L")
let coq_c_plus_permute = lazy (constant  "C_PLUS_PERMUTE")
let coq_c_plus_comm = lazy (constant  "C_PLUS_COMM")
let coq_c_red0 = lazy (constant  "C_RED0")
let coq_c_red1 = lazy (constant  "C_RED1")
let coq_c_red2 = lazy (constant  "C_RED2")
let coq_c_red3 = lazy (constant  "C_RED3")
let coq_c_red4 = lazy (constant  "C_RED4")
let coq_c_red5 = lazy (constant  "C_RED5")
let coq_c_red6 = lazy (constant  "C_RED6")
let coq_c_mult_opp_left = lazy (constant  "C_MULT_OPP_LEFT")
let coq_c_mult_assoc_reduced = lazy (constant  "C_MULT_ASSOC_REDUCED")
let coq_c_minus = lazy (constant  "C_MINUS")
let coq_c_mult_comm = lazy (constant  "C_MULT_COMM")

let coq_s_constant_not_nul = lazy (constant  "O_CONSTANT_NOT_NUL")
let coq_s_constant_neg = lazy (constant  "O_CONSTANT_NEG")
let coq_s_div_approx = lazy (constant  "O_DIV_APPROX")
let coq_s_not_exact_divide = lazy (constant  "O_NOT_EXACT_DIVIDE")
let coq_s_exact_divide = lazy (constant  "O_EXACT_DIVIDE")
let coq_s_sum = lazy (constant  "O_SUM")
let coq_s_state = lazy (constant  "O_STATE")
let coq_s_contradiction = lazy (constant  "O_CONTRADICTION")
let coq_s_merge_eq = lazy (constant  "O_MERGE_EQ")
let coq_s_split_ineq =lazy (constant  "O_SPLIT_INEQ")
let coq_s_constant_nul =lazy (constant  "O_CONSTANT_NUL")
let coq_s_negate_contradict =lazy (constant  "O_NEGATE_CONTRADICT")
let coq_s_negate_contradict_inv =lazy (constant  "O_NEGATE_CONTRADICT_INV")

(* construction for the [extract_hyp] tactic *)
let coq_direction = lazy  (constant  "direction")
let coq_d_left = lazy  (constant  "D_left")
let coq_d_right = lazy  (constant  "D_right")
let coq_d_mono = lazy  (constant  "D_mono")

let coq_e_split = lazy  (constant  "E_SPLIT")
let coq_e_extract = lazy  (constant  "E_EXTRACT")
let coq_e_solve = lazy  (constant  "E_SOLVE")

let coq_interp_sequent = lazy (constant  "interp_goal_concl")
let coq_do_omega = lazy (constant  "do_omega")

(* \subsection{Construction d'expressions} *)

let do_left t =
  if Term.eq_constr t (Lazy.force coq_c_nop) then Lazy.force coq_c_nop
  else Term.mkApp (Lazy.force coq_c_do_left, [|t |] )

let do_right t =
  if Term.eq_constr t (Lazy.force coq_c_nop) then Lazy.force coq_c_nop
  else Term.mkApp (Lazy.force coq_c_do_right, [|t |])

let do_both t1 t2 =
  if Term.eq_constr t1 (Lazy.force coq_c_nop) then do_right t2
  else if Term.eq_constr t2 (Lazy.force coq_c_nop) then do_left t1
  else Term.mkApp (Lazy.force coq_c_do_both , [|t1; t2 |])

let do_seq t1 t2 =
  if Term.eq_constr t1 (Lazy.force coq_c_nop) then t2
  else if Term.eq_constr t2 (Lazy.force coq_c_nop) then t1
  else Term.mkApp (Lazy.force coq_c_do_seq, [|t1; t2 |])

let rec do_list = function
  | [] -> Lazy.force coq_c_nop
  | [x] -> x
  | (x::l) -> do_seq x (do_list l)

(* Nat *)

let coq_S = lazy(init_constant "S")
let coq_O = lazy(init_constant "O")

let rec mk_nat = function
  | 0 -> Lazy.force coq_O
  | n -> Term.mkApp (Lazy.force coq_S, [| mk_nat (n-1) |])

(* Lists *)

let mkListConst c = 
  let r = 
    Coqlib.gen_reference "" ["Init";"Datatypes"] c
  in 
  let inst = 
    if Global.is_polymorphic r then fun u -> Univ.Instance.of_array [|u|]
    else fun _ -> Univ.Instance.empty
  in
    fun u -> Term.mkConstructU (Globnames.destConstructRef r, inst u)

let coq_cons univ typ = Term.mkApp (mkListConst "cons" univ, [|typ|])
let coq_nil univ typ =  Term.mkApp (mkListConst "nil" univ, [|typ|])

let mk_list univ typ l =
  let rec loop = function
    | [] -> coq_nil univ typ
    | (step :: l) ->
	Term.mkApp (coq_cons univ typ, [| step; loop l |]) in
  loop l

let mk_plist = 
  let type1lev = Universes.new_univ_level (Global.current_dirpath ()) in
    fun l -> mk_list type1lev Term.mkProp l

let mk_list = mk_list Univ.Level.set
let mk_shuffle_list l = mk_list (Lazy.force coq_t_fusion) l


type parse_term =
  | Tplus of Term.constr * Term.constr
  | Tmult of Term.constr * Term.constr
  | Tminus of Term.constr * Term.constr
  | Topp of Term.constr
  | Tsucc of Term.constr
  | Tnum of Bigint.bigint
  | Tother

type parse_rel =
  | Req of Term.constr * Term.constr
  | Rne of Term.constr * Term.constr
  | Rlt of Term.constr * Term.constr
  | Rle of Term.constr * Term.constr
  | Rgt of Term.constr * Term.constr
  | Rge of Term.constr * Term.constr
  | Rtrue
  | Rfalse
  | Rnot of Term.constr
  | Ror of Term.constr * Term.constr
  | Rand of Term.constr * Term.constr
  | Rimp of Term.constr * Term.constr
  | Riff of Term.constr * Term.constr
  | Rother

let parse_logic_rel c =
 try match destructurate c with
   | Kapp("True",[]) -> Rtrue
   | Kapp("False",[]) -> Rfalse
   | Kapp("not",[t]) -> Rnot t
   | Kapp("or",[t1;t2]) -> Ror (t1,t2)
   | Kapp("and",[t1;t2]) -> Rand (t1,t2)
   | Kimp(t1,t2) -> Rimp (t1,t2)
   | Kapp("iff",[t1;t2]) -> Riff (t1,t2)
   | _ -> Rother
 with e when Logic.catchable_exception e -> Rother


module type Int = sig
  val typ : Term.constr Lazy.t
  val plus : Term.constr Lazy.t
  val mult : Term.constr Lazy.t
  val opp : Term.constr Lazy.t
  val minus : Term.constr Lazy.t

  val mk : Bigint.bigint -> Term.constr
  val parse_term : Term.constr -> parse_term
  val parse_rel : Proof_type.goal Tacmach.sigma -> Term.constr -> parse_rel
  (* check whether t is built only with numbers and + * - *)
  val is_scalar : Term.constr -> bool
end

module Z : Int = struct

let typ = lazy (bin_constant "Z")
let plus = lazy (z_constant "Z.add")
let mult = lazy (z_constant  "Z.mul")
let opp = lazy (z_constant "Z.opp")
let minus = lazy (z_constant "Z.sub")

let coq_xH = lazy (bin_constant "xH")
let coq_xO = lazy (bin_constant "xO")
let coq_xI = lazy (bin_constant "xI")
let coq_Z0 = lazy (bin_constant "Z0")
let coq_Zpos = lazy (bin_constant "Zpos")
let coq_Zneg = lazy (bin_constant "Zneg")

let recognize t =
  let rec loop t =
    let f,l = dest_const_apply t in
    match Names.Id.to_string f,l with
       "xI",[t] -> Bigint.add Bigint.one (Bigint.mult Bigint.two (loop t))
     | "xO",[t] -> Bigint.mult Bigint.two (loop t)
     | "xH",[] -> Bigint.one
     | _ -> failwith "not a number" in
  let f,l = dest_const_apply t in
    match Names.Id.to_string f,l with
        "Zpos",[t] -> loop t
      | "Zneg",[t] -> Bigint.neg (loop t)
      | "Z0",[] -> Bigint.zero
      | _ -> failwith "not a number";;

let rec mk_positive n =
  if n=Bigint.one then Lazy.force coq_xH
  else
    let (q,r) = Bigint.euclid n Bigint.two in
    Term.mkApp
      ((if r = Bigint.zero then Lazy.force coq_xO else Lazy.force coq_xI),
       [| mk_positive q |])

let mk_Z n =
  if n = Bigint.zero then Lazy.force coq_Z0
  else if Bigint.is_strictly_pos n then
    Term.mkApp (Lazy.force coq_Zpos, [| mk_positive n |])
  else
    Term.mkApp (Lazy.force coq_Zneg, [| mk_positive (Bigint.neg n) |])

let mk = mk_Z

let parse_term t =
  try match destructurate t with
    | Kapp("Z.add",[t1;t2]) -> Tplus (t1,t2)
    | Kapp("Z.sub",[t1;t2]) -> Tminus (t1,t2)
    | Kapp("Z.mul",[t1;t2]) -> Tmult (t1,t2)
    | Kapp("Z.opp",[t]) -> Topp t
    | Kapp("Z.succ",[t]) -> Tsucc t
    | Kapp("Z.pred",[t]) -> Tplus(t, mk_Z (Bigint.neg Bigint.one))
    | Kapp(("Zpos"|"Zneg"|"Z0"),_) ->
	(try Tnum (recognize t) with e when Errors.noncritical e -> Tother)
    | _ -> Tother
  with e when Logic.catchable_exception e -> Tother

let parse_rel gl t =
  try match destructurate t with
    | Kapp("eq",[typ;t1;t2])
      when destructurate (Tacmach.pf_nf gl typ) = Kapp("Z",[]) -> Req (t1,t2)
    | Kapp("Zne",[t1;t2]) -> Rne (t1,t2)
    | Kapp("Z.le",[t1;t2]) -> Rle (t1,t2)
    | Kapp("Z.lt",[t1;t2]) -> Rlt (t1,t2)
    | Kapp("Z.ge",[t1;t2]) -> Rge (t1,t2)
    | Kapp("Z.gt",[t1;t2]) -> Rgt (t1,t2)
    | _ -> parse_logic_rel t
  with e when Logic.catchable_exception e -> Rother

let is_scalar t =
  let rec aux t = match destructurate t with
    | Kapp(("Z.add"|"Z.sub"|"Z.mul"),[t1;t2]) -> aux t1 && aux t2
    | Kapp(("Z.opp"|"Z.succ"|"Z.pred"),[t]) -> aux t
    | Kapp(("Zpos"|"Zneg"|"Z0"),_) -> let _ = recognize t in true
    | _ -> false in
  try aux t with e when Errors.noncritical e -> false

end
