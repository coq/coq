(*************************************************************************

   PROJET RNRT Calife - 2001
   Author: Pierre Crégut - France Télécom R&D
   Licence : LGPL version 2.1

 *************************************************************************)

let module_refl_name = "ReflOmegaCore"
let module_refl_path = ["romega"; module_refl_name]

type result = 
   Kvar of string
 | Kapp of string * Term.constr list
 | Kimp of Term.constr * Term.constr
 | Kufo;;

let destructurate t =
  let c, args = Term.decompose_app t in
(*  let env = Global.env() in*)
  match Term.kind_of_term c, args with
    | Term.Const sp, args ->
	Kapp (Names.string_of_id
		(Nametab.id_of_global (Libnames.ConstRef sp)),
              args)
    | Term.Construct csp , args ->
	Kapp (Names.string_of_id
		(Nametab.id_of_global (Libnames.ConstructRef csp)),
	        args)
    | Term.Ind isp, args ->
	Kapp (Names.string_of_id
		(Nametab.id_of_global (Libnames.IndRef isp)),args)
    | Term.Var id,[] -> Kvar(Names.string_of_id id)
    | Term.Prod (Names.Anonymous,typ,body), [] -> Kimp(typ,body)
    | Term.Prod (Names.Name _,_,_),[] ->
	Util.error "Omega: Not a quantifier-free goal"
    | _ -> Kufo

exception Destruct

let dest_const_apply t = 
  let f,args = Term.decompose_app t in
  let ref = 
  match Term.kind_of_term f with 
    | Term.Const sp         -> Libnames.ConstRef sp
    | Term.Construct csp -> Libnames.ConstructRef csp
    | Term.Ind isp       -> Libnames.IndRef isp
    | _ -> raise Destruct
  in
  Nametab.id_of_global ref, args

let recognize_number t =
  let rec loop t =
    let f,l = dest_const_apply t in
    match Names.string_of_id f,l with
       "xI",[t] -> 1 + 2 * loop t
     | "xO",[t] -> 2 * loop t 
     | "xH",[] -> 1
     | _ -> failwith "not a number" in
  let f,l = dest_const_apply t in
    match Names.string_of_id f,l with
       "POS",[t] -> loop t | "NEG",[t] -> - (loop t) | "ZERO",[] -> 0
     | _ -> failwith "not a number";;

let init_dir = ["Coq";"Init"]
let arith_dir = ["Coq";"Arith"]
let logic_dir = ["Coq";"Logic"]
let zarith_dir = ["Coq";"ZArith"]
let list_dir = ["Coq";"Lists"]
let coq_modules = [
  zarith_dir@["fast_integer"];
  zarith_dir@["zarith_aux"];
  zarith_dir@["auxiliary"];
  init_dir@["Datatypes"];
  init_dir@["Peano"];
  init_dir@["Logic"];
  arith_dir@["Compare_dec"];
  arith_dir@["Peano_dec"];
  arith_dir@["Minus"];
  logic_dir@["Decidable"];
  list_dir@["PolyList"]
]

let constant = Coqlib.gen_constant_in_modules "ROmega" coq_modules

let coq_xH = lazy (constant "xH")
let coq_xO = lazy (constant "xO")
let coq_xI = lazy (constant "xI")
let coq_ZERO = lazy (constant "ZERO")
let coq_POS = lazy (constant "POS")
let coq_NEG = lazy (constant "NEG")
let coq_Z = lazy (constant "Z")
let coq_relation = lazy (constant "relation")
let coq_SUPERIEUR = lazy (constant "SUPERIEUR")
let coq_INFEEIEUR = lazy (constant "INFERIEUR")
let coq_EGAL = lazy (constant "EGAL")
let coq_Zplus = lazy (constant "Zplus")
let coq_Zmult = lazy (constant "Zmult")
let coq_Zopp = lazy (constant "Zopp")

(* auxiliaires zarith *)
let coq_Zminus = lazy (constant "Zminus")
let coq_Zs = lazy (constant "Zs")
let coq_Zgt = lazy (constant "Zgt")
let coq_Zle = lazy (constant "Zle")
let coq_inject_nat = lazy (constant "inject_nat")

(* Peano *)
let coq_le = lazy(constant "le")
let coq_gt = lazy(constant "gt")

(* Datatypes *)
let coq_nat = lazy(constant "nat")
let coq_S = lazy(constant "S")
let coq_O = lazy(constant "O")

(* Minus *)
let coq_minus = lazy(constant "minus")

(* Logic *)
let coq_eq = lazy(constant "eq")
let coq_refl_equal = lazy(constant "refl_equal")
let coq_and = lazy(constant "and")
let coq_not = lazy(constant "not")
let coq_or = lazy(constant "or")
let coq_ex = lazy(constant "ex")

(* Lists *)
let coq_cons =  lazy (constant "cons")
let coq_nil =  lazy (constant "nil")

let romega_constant = Coqlib.gen_constant "ROmega" module_refl_path

let coq_t_nat = lazy (romega_constant "Tint")
let coq_t_plus = lazy (romega_constant "Tplus")
let coq_t_mult = lazy (romega_constant "Tmult")
let coq_t_opp = lazy (romega_constant "Topp")
let coq_t_minus = lazy (romega_constant "Tminus")
let coq_t_var = lazy (romega_constant "Tvar")
let coq_t_equal = lazy (romega_constant "EqTerm")
let coq_t_leq = lazy (romega_constant "LeqTerm")
let coq_t_geq = lazy (romega_constant "GeqTerm")
let coq_t_lt = lazy (romega_constant "LtTerm")
let coq_t_gt = lazy (romega_constant "GtTerm")
let coq_t_neq = lazy (romega_constant "NeqTerm")

let coq_proposition = lazy (romega_constant "proposition")
let coq_interp_sequent = lazy (romega_constant "interp_goal")
let coq_normalize_sequent = lazy (romega_constant "normalize_goal")
let coq_execute_sequent = lazy (romega_constant "execute_goal")
let coq_sequent_to_hyps = lazy (romega_constant "goal_to_hyps")

(* Constructors for shuffle tactic *)
let coq_t_fusion =  lazy (romega_constant "t_fusion")
let coq_f_equal =  lazy (romega_constant "F_equal")
let coq_f_cancel =  lazy (romega_constant "F_cancel")
let coq_f_left =  lazy (romega_constant "F_left")
let coq_f_right =  lazy (romega_constant "F_right")

(* Constructors for reordering tactics *)
let coq_step = lazy (romega_constant "step")
let coq_c_do_both = lazy (romega_constant "C_DO_BOTH")
let coq_c_do_left = lazy (romega_constant "C_LEFT")
let coq_c_do_right = lazy (romega_constant "C_RIGHT")
let coq_c_do_seq = lazy (romega_constant "C_SEQ")
let coq_c_nop = lazy (romega_constant "C_NOP")
let coq_c_opp_plus = lazy (romega_constant "C_OPP_PLUS")
let coq_c_opp_opp = lazy (romega_constant "C_OPP_OPP")
let coq_c_opp_mult_r = lazy (romega_constant "C_OPP_MULT_R")
let coq_c_opp_one = lazy (romega_constant "C_OPP_ONE")
let coq_c_reduce = lazy (romega_constant "C_REDUCE")
let coq_c_mult_plus_distr = lazy (romega_constant "C_MULT_PLUS_DISTR")
let coq_c_opp_left = lazy (romega_constant "C_MULT_OPP_LEFT")
let coq_c_mult_assoc_r = lazy (romega_constant "C_MULT_ASSOC_R")
let coq_c_plus_assoc_r = lazy (romega_constant "C_PLUS_ASSOC_R")
let coq_c_plus_assoc_l = lazy (romega_constant "C_PLUS_ASSOC_L")
let coq_c_plus_permute = lazy (romega_constant "C_PLUS_PERMUTE")
let coq_c_plus_sym = lazy (romega_constant "C_PLUS_SYM")
let coq_c_red0 = lazy (romega_constant "C_RED0")
let coq_c_red1 = lazy (romega_constant "C_RED1")
let coq_c_red2 = lazy (romega_constant "C_RED2")
let coq_c_red3 = lazy (romega_constant "C_RED3")
let coq_c_red4 = lazy (romega_constant "C_RED4")
let coq_c_red5 = lazy (romega_constant "C_RED5")
let coq_c_red6 = lazy (romega_constant "C_RED6")
let coq_c_mult_opp_left = lazy (romega_constant "C_MULT_OPP_LEFT")
let coq_c_mult_assoc_reduced = 
  lazy (romega_constant "C_MULT_ASSOC_REDUCED")
let coq_c_minus = lazy (romega_constant "C_MINUS")
let coq_c_mult_sym = lazy (romega_constant "C_MULT_SYM")

let coq_s_constant_not_nul = lazy (romega_constant "O_CONSTANT_NOT_NUL")
let coq_s_constant_neg = lazy (romega_constant "O_CONSTANT_NEG")
let coq_s_div_approx = lazy (romega_constant "O_DIV_APPROX")
let coq_s_not_exact_divide = lazy (romega_constant "O_NOT_EXACT_DIVIDE")
let coq_s_exact_divide = lazy (romega_constant "O_EXACT_DIVIDE")
let coq_s_sum = lazy (romega_constant "O_SUM")
let coq_s_state = lazy (romega_constant "O_STATE")
let coq_s_contradiction = lazy (romega_constant "O_CONTRADICTION")
let coq_s_merge_eq = lazy (romega_constant "O_MERGE_EQ")
let coq_s_split_ineq =lazy (romega_constant "O_SPLIT_INEQ")
let coq_s_constant_nul =lazy (romega_constant "O_CONSTANT_NUL")
let coq_s_negate_contradict =lazy (romega_constant "O_NEGATE_CONTRADICT")
let coq_s_negate_contradict_inv =lazy (romega_constant "O_NEGATE_CONTRADICT_INV")

(* \subsection{Construction d'expressions} *)


let mk_var v = Term.mkVar (Names.id_of_string v)
let mk_plus t1 t2 = Term.mkApp (Lazy.force coq_Zplus,[|  t1; t2 |])
let mk_times t1 t2 = Term.mkApp (Lazy.force coq_Zmult, [| t1; t2 |])
let mk_minus t1 t2 = Term.mkApp (Lazy.force coq_Zminus, [| t1;t2 |])
let mk_eq t1 t2 = Term.mkApp (Lazy.force coq_eq, [| Lazy.force coq_Z; t1; t2 |])
let mk_le t1 t2 = Term.mkApp (Lazy.force coq_Zle, [|t1; t2 |])
let mk_gt t1 t2 = Term.mkApp (Lazy.force coq_Zgt, [|t1; t2 |])
let mk_inv t = Term.mkApp (Lazy.force coq_Zopp, [|t |])
let mk_and t1 t2 =  Term.mkApp (Lazy.force coq_and, [|t1; t2 |])
let mk_or t1 t2 =  Term.mkApp (Lazy.force coq_or, [|t1; t2 |])
let mk_not t = Term.mkApp (Lazy.force coq_not, [|t |])
let mk_eq_rel t1 t2 = Term.mkApp (Lazy.force coq_eq, [|
				Lazy.force coq_relation; t1; t2 |])
let mk_inj t = Term.mkApp (Lazy.force coq_inject_nat, [|t |])


let do_left t = 
  if t = Lazy.force coq_c_nop then Lazy.force coq_c_nop
  else Term.mkApp (Lazy.force coq_c_do_left, [|t |] )

let do_right t = 
  if t = Lazy.force coq_c_nop then Lazy.force coq_c_nop
  else Term.mkApp (Lazy.force coq_c_do_right, [|t |])

let do_both t1 t2 = 
  if t1 = Lazy.force coq_c_nop then do_right t2
  else if t2 = Lazy.force coq_c_nop then do_left t1
  else Term.mkApp (Lazy.force coq_c_do_both , [|t1; t2 |])

let do_seq t1 t2 =
  if t1 = Lazy.force coq_c_nop then t2
  else if t2 = Lazy.force coq_c_nop then t1
  else Term.mkApp (Lazy.force coq_c_do_seq, [|t1; t2 |])
  
let rec do_list = function
  | [] -> Lazy.force coq_c_nop
  | [x] -> x
  | (x::l) -> do_seq x (do_list l)

				 
let mk_integer n =
  let rec loop n = 
    if n=1 then Lazy.force coq_xH else 
      Term.mkApp ((if n mod 2 = 0 then Lazy.force coq_xO else Lazy.force coq_xI),
		 [| loop (n/2) |]) in
    
    if n = 0 then Lazy.force coq_ZERO 
    else Term.mkApp ((if n > 0 then Lazy.force coq_POS else Lazy.force coq_NEG),
		     [| loop (abs n) |])

let mk_Z = mk_integer

let rec mk_nat = function
  | 0 -> Lazy.force coq_O
  | n -> Term.mkApp (Lazy.force coq_S, [| mk_nat (n-1) |])

let mk_list typ l =
  let rec loop = function
    | [] ->
	Term.mkApp (Lazy.force coq_nil, [|typ|])
    | (step :: l) -> 
	Term.mkApp (Lazy.force coq_cons, [|typ; step; loop l |]) in
  loop l

let mk_shuffle_list l = mk_list (Lazy.force coq_t_fusion) l

