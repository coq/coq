(*************************************************************************

   PROJET RNRT Calife - 2001
   Author: Pierre Crégut - France Télécom R&D
   Licence : LGPL version 2.1

 *************************************************************************)

open Names

let module_refl_name = "ReflOmegaCore"
let module_refl_path = ["Coq"; "romega"; module_refl_name]

type result =
  | Kvar of string
  | Kapp of string * Term.constr list
  | Kimp of Term.constr * Term.constr
  | Kufo

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
  | Term.Var id, [] -> Kvar(Names.Id.to_string id)
  | Term.Prod (Anonymous,typ,body), [] -> Kimp(typ,body)
  | _ -> Kufo

exception DestConstApp

let dest_const_apply t =
  let f,args = Term.decompose_app t in
  let ref =
  match Term.kind_of_term f with
    | Term.Const (sp,_)      -> Globnames.ConstRef sp
    | Term.Construct (csp,_) -> Globnames.ConstructRef csp
    | Term.Ind (isp,_)       -> Globnames.IndRef isp
    | _ -> raise DestConstApp
  in Nametab.basename_of_global ref, args

let logic_dir = ["Coq";"Logic";"Decidable"]

let coq_modules =
  Coqlib.init_modules @ [logic_dir] @ Coqlib.arith_modules @ Coqlib.zarith_base_modules
    @ [["Coq"; "Lists"; "List"]]
    @ [module_refl_path]
    @ [module_refl_path@["ZOmega"]]

let bin_module = [["Coq";"Numbers";"BinNums"]]
let z_module = [["Coq";"ZArith";"BinInt"]]

let init_constant x = Universes.constr_of_global @@ Coqlib.gen_reference_in_modules "Omega" Coqlib.init_modules x
let constant x = Universes.constr_of_global @@ Coqlib.gen_reference_in_modules "Omega" coq_modules x
let z_constant x = Universes.constr_of_global @@ Coqlib.gen_reference_in_modules "Omega" z_module x
let bin_constant x = Universes.constr_of_global @@ Coqlib.gen_reference_in_modules "Omega" bin_module x

(* Logic *)
let coq_refl_equal = lazy(init_constant "eq_refl")
let coq_and = lazy(init_constant "and")
let coq_not = lazy(init_constant "not")
let coq_or = lazy(init_constant "or")
let coq_True = lazy(init_constant "True")
let coq_False = lazy(init_constant "False")
let coq_I = lazy(init_constant "I")

(* ReflOmegaCore/ZOmega *)

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

let coq_s_bad_constant = lazy (constant  "O_BAD_CONSTANT")
let coq_s_divide = lazy (constant  "O_DIVIDE")
let coq_s_not_exact_divide = lazy (constant  "O_NOT_EXACT_DIVIDE")
let coq_s_sum = lazy (constant  "O_SUM")
let coq_s_merge_eq = lazy (constant  "O_MERGE_EQ")
let coq_s_split_ineq =lazy (constant  "O_SPLIT_INEQ")

(* construction for the [extract_hyp] tactic *)
let coq_direction = lazy  (constant  "direction")
let coq_d_left = lazy  (constant  "D_left")
let coq_d_right = lazy  (constant  "D_right")

let coq_e_split = lazy  (constant  "E_SPLIT")
let coq_e_extract = lazy  (constant  "E_EXTRACT")
let coq_e_solve = lazy  (constant  "E_SOLVE")

let coq_interp_sequent = lazy (constant  "interp_goal_concl")
let coq_do_omega = lazy (constant  "do_omega")

(* Nat *)

let coq_S = lazy(init_constant "S")
let coq_O = lazy(init_constant "O")

let rec mk_nat = function
  | 0 -> Lazy.force coq_O
  | n -> Term.mkApp (Lazy.force coq_S, [| mk_nat (n-1) |])

(* Lists *)

let mkListConst c = 
  let r = 
    Coqlib.coq_reference "" ["Init";"Datatypes"] c
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

let parse_logic_rel c = match destructurate c with
  | Kapp("True",[]) -> Rtrue
  | Kapp("False",[]) -> Rfalse
  | Kapp("not",[t]) -> Rnot t
  | Kapp("or",[t1;t2]) -> Ror (t1,t2)
  | Kapp("and",[t1;t2]) -> Rand (t1,t2)
  | Kimp(t1,t2) -> Rimp (t1,t2)
  | Kapp("iff",[t1;t2]) -> Riff (t1,t2)
  | _ -> Rother

(* Binary numbers *)

let coq_xH = lazy (bin_constant "xH")
let coq_xO = lazy (bin_constant "xO")
let coq_xI = lazy (bin_constant "xI")
let coq_Z0 = lazy (bin_constant "Z0")
let coq_Zpos = lazy (bin_constant "Zpos")
let coq_Zneg = lazy (bin_constant "Zneg")
let coq_N0 = lazy (bin_constant "N0")
let coq_Npos = lazy (bin_constant "Npos")

let rec mk_positive n =
  if Bigint.equal n Bigint.one then Lazy.force coq_xH
  else
    let (q,r) = Bigint.euclid n Bigint.two in
    Term.mkApp
      ((if Bigint.equal r Bigint.zero
        then Lazy.force coq_xO else Lazy.force coq_xI),
       [| mk_positive q |])

let mk_N = function
  | 0 -> Lazy.force coq_N0
  | n -> Term.mkApp (Lazy.force coq_Npos,
                     [| mk_positive (Bigint.of_int n) |])

module type Int = sig
  val typ : Term.constr Lazy.t
  val plus : Term.constr Lazy.t
  val mult : Term.constr Lazy.t
  val opp : Term.constr Lazy.t
  val minus : Term.constr Lazy.t

  val mk : Bigint.bigint -> Term.constr
  val parse_term : Term.constr -> parse_term
  val parse_rel : [ `NF ] Proofview.Goal.t -> Term.constr -> parse_rel
  (* check whether t is built only with numbers and + * - *)
  val get_scalar : Term.constr -> Bigint.bigint option
end

module Z : Int = struct

let typ = lazy (bin_constant "Z")
let plus = lazy (z_constant "Z.add")
let mult = lazy (z_constant  "Z.mul")
let opp = lazy (z_constant "Z.opp")
let minus = lazy (z_constant "Z.sub")

let recognize_pos t =
  let rec loop t =
    let f,l = dest_const_apply t in
    match Id.to_string f,l with
    | "xI",[t] -> Bigint.add Bigint.one (Bigint.mult Bigint.two (loop t))
    | "xO",[t] -> Bigint.mult Bigint.two (loop t)
    | "xH",[] -> Bigint.one
    | _ -> raise DestConstApp
  in
  try Some (loop t) with DestConstApp -> None

let recognize_Z t =
  try
    let f,l = dest_const_apply t in
    match Id.to_string f,l with
    | "Zpos",[t] -> recognize_pos t
    | "Zneg",[t] -> Option.map Bigint.neg (recognize_pos t)
    | "Z0",[] -> Some Bigint.zero
    | _ -> None
  with DestConstApp -> None

let mk_Z n =
  if Bigint.equal n Bigint.zero then Lazy.force coq_Z0
  else if Bigint.is_strictly_pos n then
    Term.mkApp (Lazy.force coq_Zpos, [| mk_positive n |])
  else
    Term.mkApp (Lazy.force coq_Zneg, [| mk_positive (Bigint.neg n) |])

let mk = mk_Z

let parse_term t =
  match destructurate t with
  | Kapp("Z.add",[t1;t2]) -> Tplus (t1,t2)
  | Kapp("Z.sub",[t1;t2]) -> Tminus (t1,t2)
  | Kapp("Z.mul",[t1;t2]) -> Tmult (t1,t2)
  | Kapp("Z.opp",[t]) -> Topp t
  | Kapp("Z.succ",[t]) -> Tsucc t
  | Kapp("Z.pred",[t]) -> Tplus(t, mk_Z (Bigint.neg Bigint.one))
  | Kapp(("Zpos"|"Zneg"|"Z0"),_) ->
     (match recognize_Z t with Some t -> Tnum t | None -> Tother)
  | _ -> Tother

let pf_nf gl c =
  EConstr.Unsafe.to_constr
    (Tacmach.New.pf_apply Tacred.simpl gl (EConstr.of_constr c))

let parse_rel gl t =
  match destructurate t with
  | Kapp("eq",[typ;t1;t2]) ->
     (match destructurate (pf_nf gl typ) with
      | Kapp("Z",[]) -> Req (t1,t2)
      | _ -> Rother)
  | Kapp("Zne",[t1;t2]) -> Rne (t1,t2)
  | Kapp("Z.le",[t1;t2]) -> Rle (t1,t2)
  | Kapp("Z.lt",[t1;t2]) -> Rlt (t1,t2)
  | Kapp("Z.ge",[t1;t2]) -> Rge (t1,t2)
  | Kapp("Z.gt",[t1;t2]) -> Rgt (t1,t2)
  | _ -> parse_logic_rel t

let rec get_scalar t =
  match destructurate t with
  | Kapp("Z.add", [t1;t2]) ->
     Option.lift2 Bigint.add (get_scalar t1) (get_scalar t2)
  | Kapp ("Z.sub",[t1;t2]) ->
     Option.lift2 Bigint.sub (get_scalar t1) (get_scalar t2)
  | Kapp ("Z.mul",[t1;t2]) ->
     Option.lift2 Bigint.mult (get_scalar t1) (get_scalar t2)
  | Kapp("Z.opp", [t]) -> Option.map Bigint.neg (get_scalar t)
  | Kapp("Z.succ", [t]) -> Option.map Bigint.add_1 (get_scalar t)
  | Kapp("Z.pred", [t]) -> Option.map Bigint.sub_1 (get_scalar t)
  | Kapp(("Zpos"|"Zneg"|"Z0"),_) -> recognize_Z t
  | _ -> None

end
