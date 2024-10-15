(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open CErrors
open Names
open Constr
open Context
open Declarations
open Util
open Nativevalues
open Genlambda
open Nativelambda
open Environ

(** This file defines the mllambda code generation phase of the native
compiler. mllambda represents a fragment of ML, and can easily be printed
to OCaml code. *)

let debug_native_flag, debug_native_compiler = CDebug.create_full ~name:"native-compiler" ()

let keep_debug_files () =
  CDebug.get_flag debug_native_flag

(** Local names **)

(* The first component is there for debugging purposes only *)
type lname = { lname : Name.t; luid : int }

let eq_lname ln1 ln2 =
  Int.equal ln1.luid ln2.luid

let dummy_lname = { lname = Anonymous; luid = -1 }

module LNord =
  struct
    type t = lname
    let compare l1 l2 = l1.luid - l2.luid
  end
module LNmap = Map.Make(LNord)
module LNset = Set.Make(LNord)

let lname_ctr = ref (-1)

let fresh_lname n =
  incr lname_ctr;
  { lname = n; luid = !lname_ctr }

let rec is_lazy env t =
  match Constr.kind t with
  | App _ | LetIn _ | Case _ | Proj _ -> true
  | Array (_, t, d, _) -> Array.exists (fun t -> is_lazy env t) t || is_lazy env d
  | Cast (c, _, _) | Prod (_, c, _) -> is_lazy env c
  | Const (c, _) -> get_const_lazy env c
  | Rel _ | Meta _ | Var _ | Sort _ | Ind _ | Construct _ | Int _
  | Float _ | String _ | Lambda _ | Evar _ | Fix _ | CoFix _ ->
    false

and is_lazy_constant env cb =
  (* Bound universes are turned into lambda-abstractions *)
  UVars.AbstractContext.is_constant (Declareops.constant_polymorphic_context cb) &&
  (* So are context variables *)
  List.is_empty cb.const_hyps &&
  match cb.const_body with
  | Def body -> is_lazy env body
  | Undef _ | OpaqueDef _ | Primitive _ | Symbol _ -> false

and get_const_lazy env c =
  let cb = Environ.lookup_constant c env in
  is_lazy_constant env cb

type prefix = string

(* Linked code location utilities *)
let get_mind_prefix env mind =
   let _,name = lookup_mind_key mind env in
   match !name with
   | NotLinked -> ""
   | Linked s -> s

let get_const_prefix env c =
   let _,(nameref,_) = lookup_constant_key c env in
   match !nameref with
   | NotLinked -> ""
   | Linked s -> s

(** Global names **)
type gname =
  | Gind of string * inductive (* prefix, inductive name *)
  | Gconstant of string * Constant.t (* prefix, constant name *)
  | Gproj of string * inductive * int (* prefix, inductive, index (start from 0) *)
  | Gcase of Label.t option * int
  | Gpred of Label.t option * int
  | Gfixtype of Label.t option * int
  | Gnorm of Label.t option * int
  | Gnormtbl of Label.t option * int
  | Ginternal of string
  | Grel of int
  | Gnamed of Id.t

let eq_gname gn1 gn2 =
  match gn1, gn2 with
  | Gind (s1, ind1), Gind (s2, ind2) ->
     String.equal s1 s2 && Ind.CanOrd.equal ind1 ind2
  | Gconstant (s1, c1), Gconstant (s2, c2) ->
      String.equal s1 s2 && Constant.CanOrd.equal c1 c2
  | Gproj (s1, ind1, i1), Gproj (s2, ind2, i2) ->
    String.equal s1 s2 && Ind.CanOrd.equal ind1 ind2 && Int.equal i1 i2
  | Gcase (None, i1), Gcase (None, i2) -> Int.equal i1 i2
  | Gcase (Some l1, i1), Gcase (Some l2, i2) -> Int.equal i1 i2 && Label.equal l1 l2
  | Gpred (None, i1), Gpred (None, i2) -> Int.equal i1 i2
  | Gpred (Some l1, i1), Gpred (Some l2, i2) -> Int.equal i1 i2 && Label.equal l1 l2
  | Gfixtype (None, i1), Gfixtype (None, i2) -> Int.equal i1 i2
  | Gfixtype (Some l1, i1), Gfixtype (Some l2, i2) ->
      Int.equal i1 i2 && Label.equal l1 l2
  | Gnorm (None, i1), Gnorm (None, i2) -> Int.equal i1 i2
  | Gnorm (Some l1, i1), Gnorm (Some l2, i2) -> Int.equal i1 i2 && Label.equal l1 l2
  | Gnormtbl (None, i1), Gnormtbl (None, i2) -> Int.equal i1 i2
  | Gnormtbl (Some l1, i1), Gnormtbl (Some l2, i2) ->
      Int.equal i1 i2 && Label.equal l1 l2
  | Ginternal s1, Ginternal s2 -> String.equal s1 s2
  | Grel i1, Grel i2 -> Int.equal i1 i2
  | Gnamed id1, Gnamed id2 -> Id.equal id1 id2
  | (Gind _| Gconstant _ | Gproj _ | Gcase _ | Gpred _
    | Gfixtype _ | Gnorm _ | Gnormtbl _ | Ginternal _ | Grel _ | Gnamed _), _ ->
      false

let dummy_gname =
  Grel 0

open Hashset.Combine

let gname_hash gn = match gn with
| Gind (s, ind) ->
   combinesmall 1 (combine (String.hash s) (Ind.CanOrd.hash ind))
| Gconstant (s, c) ->
   combinesmall 2 (combine (String.hash s) (Constant.CanOrd.hash c))
| Gcase (l, i) -> combinesmall 3 (combine (Option.hash Label.hash l) (Int.hash i))
| Gpred (l, i) -> combinesmall 4 (combine (Option.hash Label.hash l) (Int.hash i))
| Gfixtype (l, i) -> combinesmall 5 (combine (Option.hash Label.hash l) (Int.hash i))
| Gnorm (l, i) -> combinesmall 6 (combine (Option.hash Label.hash l) (Int.hash i))
| Gnormtbl (l, i) -> combinesmall 7 (combine (Option.hash Label.hash l) (Int.hash i))
| Ginternal s -> combinesmall 8 (String.hash s)
| Grel i -> combinesmall 9 (Int.hash i)
| Gnamed id -> combinesmall 10 (Id.hash id)
| Gproj (s, p, i) -> combinesmall 11 (combine (String.hash s) (combine (Ind.CanOrd.hash p) i))

let case_ctr = ref (-1)

let fresh_gcase l =
  incr case_ctr;
  Gcase (l,!case_ctr)

let pred_ctr = ref (-1)

let fresh_gpred l =
  incr pred_ctr;
  Gpred (l,!pred_ctr)

let fixtype_ctr = ref (-1)

let fresh_gfixtype l =
  incr fixtype_ctr;
  Gfixtype (l,!fixtype_ctr)

let norm_ctr = ref (-1)

let fresh_gnorm l =
  incr norm_ctr;
  Gnorm (l,!norm_ctr)

let normtbl_ctr = ref (-1)

let fresh_gnormtbl l =
  incr normtbl_ctr;
  Gnormtbl (l,!normtbl_ctr)

(** Symbols (pre-computed values) **)

let dummy_symb = SymbValue (dummy_value ())

let eq_symbol sy1 sy2 =
  match sy1, sy2 with
  | SymbValue v1, SymbValue v2 -> (=) v1 v2 (** FIXME: how is this even valid? *)
  | SymbSort s1, SymbSort s2 -> Sorts.equal s1 s2
  | SymbName n1, SymbName n2 -> Name.equal n1 n2
  | SymbConst kn1, SymbConst kn2 -> Constant.CanOrd.equal kn1 kn2
  | SymbMatch sw1, SymbMatch sw2 -> eq_annot_sw sw1 sw2
  | SymbInd ind1, SymbInd ind2 -> Ind.CanOrd.equal ind1 ind2
  | SymbEvar evk1, SymbEvar evk2 -> Evar.equal evk1 evk2
  | SymbInstance u1, SymbInstance u2 -> UVars.Instance.equal u1 u2
  | SymbProj (i1, k1), SymbProj (i2, k2) -> Ind.CanOrd.equal i1 i2 && Int.equal k1 k2

  | (SymbValue _
    | SymbSort _
    | SymbName _
    | SymbConst _
    | SymbMatch _
    | SymbInd _
    | SymbEvar _
    | SymbInstance _
    | SymbProj _), _
    -> false


let hash_symbol symb =
  match symb with
  | SymbValue v -> combinesmall 1 (Hashtbl.hash v) (** FIXME *)
  | SymbSort s -> combinesmall 2 (Sorts.hash s)
  | SymbName name -> combinesmall 3 (Name.hash name)
  | SymbConst c -> combinesmall 4 (Constant.CanOrd.hash c)
  | SymbMatch sw -> combinesmall 5 (hash_annot_sw sw)
  | SymbInd ind -> combinesmall 6 (Ind.CanOrd.hash ind)
  | SymbEvar evk -> combinesmall 7 (Evar.hash evk)
  | SymbInstance u -> combinesmall 8 (UVars.Instance.hash u)
  | SymbProj (i, k) -> combinesmall 9 (combine (Ind.CanOrd.hash i) k)

module HashedTypeSymbol = struct
  type t = symbol
  let equal = eq_symbol
  let hash = hash_symbol
end

module HashtblSymbol = Hashtbl.Make(HashedTypeSymbol)

let symb_tbl = HashtblSymbol.create 211

let clear_symbols () = HashtblSymbol.clear symb_tbl

let get_value tbl i =
  match tbl.(i) with
    | SymbValue v -> v
    | _ -> anomaly (Pp.str "get_value failed.")

let get_sort tbl i =
  match tbl.(i) with
    | SymbSort s -> s
    | _ -> anomaly (Pp.str "get_sort failed.")

let get_name tbl i =
  match tbl.(i) with
    | SymbName id -> id
    | _ -> anomaly (Pp.str "get_name failed.")

let get_const tbl i =
  match tbl.(i) with
    | SymbConst kn -> kn
    | _ -> anomaly (Pp.str "get_const failed.")

let get_match tbl i =
  match tbl.(i) with
    | SymbMatch case_info -> case_info
    | _ -> anomaly (Pp.str "get_match failed.")

let get_ind tbl i =
  match tbl.(i) with
    | SymbInd ind -> ind
    | _ -> anomaly (Pp.str "get_ind failed.")

let get_evar tbl i =
  match tbl.(i) with
    | SymbEvar ev -> ev
    | _ -> anomaly (Pp.str "get_evar failed.")

let get_instance tbl i =
  match tbl.(i) with
    | SymbInstance u -> u
    | _ -> anomaly (Pp.str "get_instance failed.")

let get_proj tbl i =
  match tbl.(i) with
    | SymbProj p -> p
    | _ -> anomaly (Pp.str "get_proj failed.")

let push_symbol x =
  try HashtblSymbol.find symb_tbl x
  with Not_found ->
    let i = HashtblSymbol.length symb_tbl in
    HashtblSymbol.add symb_tbl x i; i

let symbols_tbl_name = Ginternal "symbols_tbl"

let get_symbols () =
  let tbl = Array.make (HashtblSymbol.length symb_tbl) dummy_symb in
  HashtblSymbol.iter (fun x i -> tbl.(i) <- x) symb_tbl; tbl

(** Lambda to Mllambda **)

type primitive =
  | Mk_prod
  | Mk_sort
  | Mk_ind
  | Mk_const
  | Mk_sw
  | Mk_fix of rec_pos * int
  | Mk_cofix of int
  | Mk_rel of int
  | Mk_var of Id.t
  | Mk_proj
  | Is_int
  | Is_float
  | Is_string
  | Is_parray
  | Cast_accu
  | Upd_cofix
  | Force_cofix
  | Mk_uint
  | Mk_float
  | Mk_string
  | Mk_int
  | Val_to_int
  | Mk_evar
  | MLand
  | MLnot
  | MLland
  | MLmagic
  | MLsubst_instance_instance
  | MLparray_of_array
  | Get_value
  | Get_sort
  | Get_name
  | Get_const
  | Get_match
  | Get_ind
  | Get_evar
  | Get_instance
  | Get_proj
  | Get_symbols
  | Lazy
  | Coq_primitive of CPrimitives.t * bool (* check for accu *)
  | Mk_empty_instance

let eq_primitive p1 p2 =
  match p1, p2 with
  | Mk_prod, Mk_prod
  | Mk_sort, Mk_sort
  | Mk_ind, Mk_ind
  | Mk_const, Mk_const
  | Mk_sw, Mk_sw
  | Mk_proj, Mk_proj
  | Is_int, Is_int
  | Is_float, Is_float
  | Is_string, Is_string
  | Is_parray, Is_parray
  | Cast_accu, Cast_accu
  | Upd_cofix, Upd_cofix
  | Force_cofix, Force_cofix
  | Mk_uint, Mk_uint
  | Mk_float, Mk_float
  | Mk_string, Mk_string
  | Mk_int, Mk_int
  | Val_to_int, Val_to_int
  | Mk_evar, Mk_evar
  | MLand, MLand
  | MLnot, MLnot
  | MLland, MLland
  | MLmagic, MLmagic
  | MLsubst_instance_instance, MLsubst_instance_instance
  | MLparray_of_array, MLparray_of_array
  | Get_value, Get_value
  | Get_sort, Get_sort
  | Get_name, Get_name
  | Get_const, Get_const
  | Get_match, Get_match
  | Get_ind, Get_ind
  | Get_evar, Get_evar
  | Get_instance, Get_instance
  | Get_proj, Get_proj
  | Get_symbols, Get_symbols
  | Lazy, Lazy
  | Mk_empty_instance, Mk_empty_instance
    -> true

  | Mk_fix (rp1, i1), Mk_fix (rp2, i2) -> Int.equal i1 i2 && eq_rec_pos rp1 rp2
  | Mk_cofix i1, Mk_cofix i2 -> Int.equal i1 i2
  | Mk_rel i1, Mk_rel i2 -> Int.equal i1 i2
  | Mk_var id1, Mk_var id2 -> Id.equal id1 id2
  | Coq_primitive (prim1,b1), Coq_primitive (prim2,b2) ->
    CPrimitives.equal prim1 prim2 && Bool.equal b1 b2

  | (Mk_prod
    | Mk_sort
    | Mk_ind
    | Mk_const
    | Mk_sw
    | Mk_fix _
    | Mk_cofix _
    | Mk_rel _
    | Mk_var _
    | Mk_proj
    | Is_int
    | Is_float
    | Is_string
    | Is_parray
    | Cast_accu
    | Upd_cofix
    | Force_cofix
    | Mk_uint
    | Mk_float
    | Mk_string
    | Mk_int
    | Val_to_int
    | Mk_evar
    | MLand
    | MLnot
    | MLland
    | MLmagic
    | MLsubst_instance_instance
    | MLparray_of_array
    | Get_value
    | Get_sort
    | Get_name
    | Get_const
    | Get_match
    | Get_ind
    | Get_evar
    | Get_instance
    | Get_proj
    | Get_symbols
    | Lazy
    | Coq_primitive _
    | Mk_empty_instance), _
    -> false

let primitive_hash = function
  | Mk_prod -> 1
  | Mk_sort -> 2
  | Mk_ind -> 3
  | Mk_const -> 4
  | Mk_sw -> 5
  | Mk_fix (r, i) ->
     let h = Array.fold_left (fun h i -> combine h (Int.hash i)) 0 r in
     combinesmall 6 (combine h (Int.hash i))
  | Mk_cofix i ->
     combinesmall 7 (Int.hash i)
  | Mk_rel i ->
     combinesmall 8 (Int.hash i)
  | Mk_var id ->
     combinesmall 9 (Id.hash id)
  | Is_int -> 11
  | Cast_accu -> 12
  | Upd_cofix -> 13
  | Force_cofix -> 14
  | Mk_uint -> 15
  | Mk_int -> 16
  | Val_to_int -> 17
  | Mk_evar -> 18
  | MLand -> 19
  | MLland -> 20
  | MLmagic -> 21
  | Coq_primitive (prim, b) -> combinesmall 22 (combine (CPrimitives.hash prim) (Hashtbl.hash b))
  | Mk_proj -> 23
  | MLsubst_instance_instance -> 24
  | Mk_float -> 25
  | Is_float -> 26
  | Is_string -> 27
  | Is_parray -> 28
  | MLnot -> 29
  | MLparray_of_array -> 30
  | Get_value -> 31
  | Get_sort -> 32
  | Get_name -> 33
  | Get_const -> 34
  | Get_match -> 35
  | Get_ind -> 36
  | Get_evar -> 37
  | Get_instance -> 38
  | Get_proj -> 39
  | Get_symbols -> 40
  | Lazy -> 41
  | Mk_empty_instance -> 42
  | Mk_string -> 43

type mllambda =
  | MLlocal        of lname
  | MLglobal       of gname
  | MLprimitive    of primitive * mllambda array
  | MLlam          of lname array * mllambda
  | MLletrec       of (lname * lname array * mllambda) array * mllambda
  | MLlet          of lname * mllambda * mllambda
  | MLapp          of mllambda * mllambda array
  | MLif           of mllambda * mllambda * mllambda
  | MLmatch        of annot_sw * mllambda * mllambda * mllam_branches
                              (* argument, prefix, accu branch, branches *)
  | MLconstruct    of string * inductive * int * mllambda array
                   (* prefix, inductive name, tag, arguments *)
  | MLint          of int
  | MLuint         of Uint63.t
  | MLfloat        of Float64.t
  | MLstring       of Pstring.t
  | MLsetref       of string * mllambda
  | MLsequence     of mllambda * mllambda
  | MLarray        of mllambda array
  | MLisaccu       of string * inductive * mllambda

and 'a mllam_pattern =
  | ConstPattern of int
  | NonConstPattern of tag * 'a array

and mllam_branches = (lname option mllam_pattern list * mllambda) array

let push_lnames n env lns =
  snd (Array.fold_left (fun (i,r) x -> (i+1, LNmap.add x i r)) (n,env) lns)

let opush_lnames n env lns =
  let oadd x i r = match x with Some ln -> LNmap.add ln i r | None -> r in
  snd (Array.fold_left (fun (i,r) x -> (i+1, oadd x i r)) (n,env) lns)

(* Alpha-equivalence on mllambda *)
(* eq_mllambda gn1 gn2 n env1 env2 t1 t2 tests if t1 = t2 modulo gn1 = gn2 *)
let rec eq_mllambda gn1 gn2 n env1 env2 t1 t2 =
  match t1, t2 with
  | MLlocal ln1, MLlocal ln2 ->
     (try
      Int.equal (LNmap.find ln1 env1) (LNmap.find ln2 env2)
     with Not_found ->
      eq_lname ln1 ln2)
  | MLglobal gn1', MLglobal gn2' ->
      eq_gname gn1' gn2' || (eq_gname gn1 gn1' && eq_gname gn2 gn2')
      || (eq_gname gn1 gn2' && eq_gname gn2 gn1')
  | MLprimitive (prim1, args1), MLprimitive (prim2, args2) ->
      eq_primitive prim1 prim2 &&
      Array.equal (eq_mllambda gn1 gn2 n env1 env2) args1 args2
  | MLlam (lns1, ml1), MLlam (lns2, ml2) ->
      Int.equal (Array.length lns1) (Array.length lns2) &&
      let env1 = push_lnames n env1 lns1 in
      let env2 = push_lnames n env2 lns2 in
      eq_mllambda gn1 gn2 (n+Array.length lns1) env1 env2 ml1 ml2
  | MLletrec (defs1, body1), MLletrec (defs2, body2) ->
      Int.equal (Array.length defs1) (Array.length defs2) &&
      let lns1 = Array.map (fun (x,_,_) -> x) defs1 in
      let lns2 = Array.map (fun (x,_,_) -> x) defs2 in
      let env1 = push_lnames n env1 lns1 in
      let env2 = push_lnames n env2 lns2 in
      let n = n + Array.length defs1 in
      eq_letrec gn1 gn2 n env1 env2 defs1 defs2 &&
      eq_mllambda gn1 gn2 n env1 env2 body1 body2
  | MLlet (ln1, def1, body1), MLlet (ln2, def2, body2) ->
      eq_mllambda gn1 gn2 n env1 env2 def1 def2 &&
      let env1 = LNmap.add ln1 n env1 in
      let env2 = LNmap.add ln2 n env2 in
      eq_mllambda gn1 gn2 (n+1) env1 env2 body1 body2
  | MLapp (ml1, args1), MLapp (ml2, args2) ->
      eq_mllambda gn1 gn2 n env1 env2 ml1 ml2 &&
      Array.equal (eq_mllambda gn1 gn2 n env1 env2) args1 args2
  | MLif (cond1,br1,br'1), MLif (cond2,br2,br'2) ->
      eq_mllambda gn1 gn2 n env1 env2 cond1 cond2 &&
      eq_mllambda gn1 gn2 n env1 env2 br1 br2 &&
      eq_mllambda gn1 gn2 n env1 env2 br'1 br'2
  | MLmatch (annot1, c1, accu1, br1), MLmatch (annot2, c2, accu2, br2) ->
      eq_annot_sw annot1 annot2 &&
      eq_mllambda gn1 gn2 n env1 env2 c1 c2 &&
      eq_mllambda gn1 gn2 n env1 env2 accu1 accu2 &&
      eq_mllam_branches gn1 gn2 n env1 env2 br1 br2
  | MLconstruct (pf1, ind1, tag1, args1), MLconstruct (pf2, ind2, tag2, args2) ->
      String.equal pf1 pf2 &&
      Ind.CanOrd.equal ind1 ind2 &&
      Int.equal tag1 tag2 &&
      Array.equal (eq_mllambda gn1 gn2 n env1 env2) args1 args2
  | MLint i1, MLint i2 ->
      Int.equal i1 i2
  | MLuint i1, MLuint i2 ->
      Uint63.equal i1 i2
  | MLfloat f1, MLfloat f2 ->
      Float64.equal f1 f2
  | MLstring s1, MLstring s2 ->
      Pstring.equal s1 s2
  | MLsetref (id1, ml1), MLsetref (id2, ml2) ->
      String.equal id1 id2 &&
      eq_mllambda gn1 gn2 n env1 env2 ml1 ml2
  | MLsequence (ml1, ml'1), MLsequence (ml2, ml'2) ->
      eq_mllambda gn1 gn2 n env1 env2 ml1 ml2 &&
      eq_mllambda gn1 gn2 n env1 env2 ml'1 ml'2
  | MLarray arr1, MLarray arr2 ->
      Array.equal (eq_mllambda gn1 gn2 n env1 env2) arr1 arr2

  | MLisaccu (s1, ind1, ml1), MLisaccu (s2, ind2, ml2) ->
    String.equal s1 s2 && Ind.CanOrd.equal ind1 ind2 &&
    eq_mllambda gn1 gn2 n env1 env2 ml1 ml2
  | (MLlocal _ | MLglobal _ | MLprimitive _ | MLlam _ | MLletrec _ | MLlet _ |
    MLapp _ | MLif _ | MLmatch _ | MLconstruct _ | MLint _ | MLuint _ |
    MLfloat _ | MLstring _ | MLsetref _ | MLsequence _ |
    MLarray _ | MLisaccu _), _ -> false

and eq_letrec gn1 gn2 n env1 env2 defs1 defs2 =
  let eq_def (_,args1,ml1) (_,args2,ml2) =
    Int.equal (Array.length args1) (Array.length args2) &&
    let env1 = push_lnames n env1 args1 in
    let env2 = push_lnames n env2 args2 in
    eq_mllambda gn1 gn2 (n + Array.length args1) env1 env2 ml1 ml2
  in
  Array.equal eq_def defs1 defs2

(* we require here that patterns have the same order, which may be too strong *)
and eq_mllam_branches gn1 gn2 n env1 env2 br1 br2 =
  let eq_cargs args1 args2 body1 body2 =
    Int.equal (Array.length args1) (Array.length args2) &&
    let env1 = opush_lnames n env1 args1 in
    let env2 = opush_lnames n env2 args2 in
    eq_mllambda gn1 gn2 (n + Array.length args1) env1 env2 body1 body2
  in
  let eq_pattern pat1 pat2 body1 body2 =
    match pat1, pat2 with
    | ConstPattern tag1, ConstPattern tag2 ->
      Int.equal tag1 tag2 && eq_mllambda gn1 gn2 n env1 env2 body1 body2
    | NonConstPattern (tag1,args1), NonConstPattern (tag2,args2) ->
      Int.equal tag1 tag2 && eq_cargs args1 args2 body1 body2
    | (ConstPattern _ | NonConstPattern _), _ -> false
  in
  let eq_branch (patl1,body1) (patl2,body2) =
    List.equal (fun pt1 pt2 -> eq_pattern pt1 pt2 body1 body2) patl1 patl2
  in
  Array.equal eq_branch br1 br2

(* hash_mllambda gn n env t computes the hash for t ignoring occurrences of gn *)
let rec hash_mllambda gn n env t =
  match t with
  | MLlocal ln -> combinesmall 1 (LNmap.find ln env)
  | MLglobal gn' -> combinesmall 2 (if eq_gname gn gn' then 0 else gname_hash gn')
  | MLprimitive (prim, args) ->
    let h = primitive_hash prim in
    combinesmall 3 (hash_mllambda_array gn n env h args)
  | MLlam (lns, ml) ->
      let env = push_lnames n env lns in
      combinesmall 4 (combine (Array.length lns) (hash_mllambda gn (n+1) env ml))
  | MLletrec (defs, body) ->
      let lns = Array.map (fun (x,_,_) -> x) defs in
      let env = push_lnames n env lns in
      let n = n + Array.length defs in
      let h = combine (hash_mllambda gn n env body) (Array.length defs) in
      combinesmall 5 (hash_mllambda_letrec gn n env h defs)
  | MLlet (ln, def, body) ->
      let hdef = hash_mllambda gn n env def in
      let env = LNmap.add ln n env in
      combinesmall 6 (combine hdef (hash_mllambda gn (n+1) env body))
  | MLapp (ml, args) ->
      let h = hash_mllambda gn n env ml in
      combinesmall 7 (hash_mllambda_array gn n env h args)
  | MLif (cond,br,br') ->
      let hcond = hash_mllambda gn n env cond in
      let hbr = hash_mllambda gn n env br in
      let hbr' = hash_mllambda gn n env br' in
      combinesmall 8 (combine3 hcond hbr hbr')
  | MLmatch (annot, c, accu, br) ->
      let hannot = hash_annot_sw annot in
      let hc = hash_mllambda gn n env c in
      let haccu = hash_mllambda gn n env accu in
      combinesmall 9 (hash_mllam_branches gn n env (combine3 hannot hc haccu) br)
  | MLconstruct (pf, ind, tag, args) ->
      let hpf = String.hash pf in
      let hcs = Ind.CanOrd.hash ind in
      let htag = Int.hash tag in
      combinesmall 10 (hash_mllambda_array gn n env (combine3 hpf hcs htag) args)
  | MLint i ->
      combinesmall 11 i
  | MLuint i ->
      combinesmall 12 (Uint63.hash i)
  | MLsetref (id, ml) ->
      let hid = String.hash id in
      let hml = hash_mllambda gn n env ml in
      combinesmall 13 (combine hid hml)
  | MLsequence (ml, ml') ->
      let hml = hash_mllambda gn n env ml in
      let hml' = hash_mllambda gn n env ml' in
      combinesmall 14 (combine hml hml')
  | MLarray arr ->
      combinesmall 15 (hash_mllambda_array gn n env 1 arr)
  | MLisaccu (s, ind, c) ->
      combinesmall 16 (combine (String.hash s) (combine (Ind.CanOrd.hash ind) (hash_mllambda gn n env c)))
  | MLfloat f ->
      combinesmall 17 (Float64.hash f)
  | MLstring s ->
      combinesmall 18 (Pstring.hash s)

and hash_mllambda_letrec gn n env init defs =
  let hash_def (_,args,ml) =
    let env = push_lnames n env args in
    let nargs = Array.length args in
    combine nargs (hash_mllambda gn (n + nargs) env ml)
  in
  Array.fold_left (fun acc t -> combine (hash_def t) acc) init defs

and hash_mllambda_array gn n env init arr =
  Array.fold_left (fun acc t -> combine (hash_mllambda gn n env t) acc) init arr

and hash_mllam_branches gn n env init br =
  let hash_cargs args body =
    let nargs = Array.length args in
    let env = opush_lnames n env args in
    let hbody = hash_mllambda gn (n + nargs) env body in
    combine nargs hbody
  in
  let hash_pattern pat body = match pat with
    | ConstPattern i -> combinesmall 1 (Int.hash i)
    | NonConstPattern (tag,args) -> combinesmall 2 (combine (Int.hash tag) (hash_cargs args body))
  in
  let hash_branch acc (ptl,body) =
    List.fold_left (fun acc t -> combine (hash_pattern t body) acc) acc ptl
  in
  Array.fold_left hash_branch init br

let fv_lam l =
  let rec aux l bind fv =
    match l with
    | MLlocal l ->
        if LNset.mem l bind then fv else LNset.add l fv
    | MLglobal _ | MLint _ | MLuint _ | MLfloat _ | MLstring _ -> fv
    | MLprimitive (_, args) ->
        let fv_arg arg fv = aux arg bind fv in
        Array.fold_right fv_arg args fv
    | MLlam (ln,body) ->
        let bind = Array.fold_right LNset.add ln bind in
        aux body bind fv
    | MLletrec(bodies,def) ->
        let bind =
          Array.fold_right (fun (id,_,_) b -> LNset.add id b) bodies bind in
        let fv_body (_,ln,body) fv =
          let bind = Array.fold_right LNset.add ln bind in
          aux body bind fv in
        Array.fold_right fv_body bodies (aux def bind fv)
    | MLlet(l,def,body) ->
        aux body (LNset.add l bind) (aux def bind fv)
    | MLapp(f,args) ->
        let fv_arg arg fv = aux arg bind fv in
        Array.fold_right fv_arg args (aux f bind fv)
    | MLif(t,b1,b2) ->
        aux t bind (aux b1 bind (aux b2 bind fv))
    | MLmatch(_,a,p,bs) ->
      let fv = aux a bind (aux p bind fv) in
      let fv_bs (cargs, body) fv =
        let bind =
          List.fold_right (fun pat bind ->
              match pat with
              | ConstPattern _ -> bind
              | NonConstPattern(_,args) ->
                Array.fold_right
                  (fun o bind -> match o with
                     | Some l -> LNset.add l bind
                     | _ -> bind) args bind)
            cargs bind in
        aux body bind fv in
      Array.fold_right fv_bs bs fv
    (* argument, accu branch, branches *)
    | MLconstruct (_,_,_,p) ->
        Array.fold_right (fun a fv -> aux a bind fv) p fv
    | MLsetref(_,l) -> aux l bind fv
    | MLsequence(l1,l2) -> aux l1 bind (aux l2 bind fv)
    | MLarray arr -> Array.fold_right (fun a fv -> aux a bind fv) arr fv
    | MLisaccu (_, _, body) -> aux body bind fv
  in
  aux l LNset.empty LNset.empty


let mkMLlam params body =
  if Array.is_empty params then body
  else
    match body with
    | MLlam (params', body) -> MLlam(Array.append params params', body)
    | _ -> MLlam(params,body)

let mkMLapp f args =
  if Array.is_empty args then f
  else
    match f with
    | MLapp(f,args') -> MLapp(f,Array.append args' args)
    | _ -> MLapp(f,args)

let mkForceCofix prefix ind arg =
  let name = fresh_lname Anonymous in
  MLlet (name, arg,
    MLif (
      MLisaccu (prefix, ind, MLlocal name),
      MLprimitive (Force_cofix, [|MLlocal name|]),
      MLlocal name))

let empty_params = [||]

let decompose_MLlam c =
  match c with
  | MLlam(ids,c) -> ids,c
  | _ -> empty_params,c

(*s Global declaration *)
type global =
(*  | Gtblname of gname * Id.t array *)
  | Gtblnorm of gname * lname array * mllambda array
  | Gtblfixtype of gname * lname array * mllambda array
  | Glet of gname * mllambda
  | Gletcase of
      gname * lname array * annot_sw * mllambda * mllambda * mllam_branches
  | Gopen of string
  | Gtype of inductive * (tag * int) array
    (* ind name, tag and arities of constructors *)
  | Gcomment of string

(* Alpha-equivalence on globals *)
let eq_global g1 g2 =
  match g1, g2 with
  | Gtblnorm (gn1,lns1,mls1), Gtblnorm (gn2,lns2,mls2)
  | Gtblfixtype (gn1,lns1,mls1), Gtblfixtype (gn2,lns2,mls2) ->
      Int.equal (Array.length lns1) (Array.length lns2) &&
      Int.equal (Array.length mls1) (Array.length mls2) &&
      let env1 = push_lnames 0 LNmap.empty lns1 in
      let env2 = push_lnames 0 LNmap.empty lns2 in
      Array.for_all2 (eq_mllambda gn1 gn2 (Array.length lns1) env1 env2) mls1 mls2
  | Glet (gn1, def1), Glet (gn2, def2) ->
      eq_mllambda gn1 gn2 0 LNmap.empty LNmap.empty def1 def2
  | Gletcase (gn1,lns1,annot1,c1,accu1,br1),
      Gletcase (gn2,lns2,annot2,c2,accu2,br2) ->
      Int.equal (Array.length lns1) (Array.length lns2) &&
      let env1 = push_lnames 0 LNmap.empty lns1 in
      let env2 = push_lnames 0 LNmap.empty lns2 in
      let t1 = MLmatch (annot1,c1,accu1,br1) in
      let t2 = MLmatch (annot2,c2,accu2,br2) in
      eq_mllambda gn1 gn2 (Array.length lns1) env1 env2 t1 t2
  | Gopen s1, Gopen s2 -> String.equal s1 s2
  | Gtype (ind1, arr1), Gtype (ind2, arr2) ->
    Ind.CanOrd.equal ind1 ind2 &&
    Array.equal (fun (tag1,ar1) (tag2,ar2) -> Int.equal tag1 tag2 && Int.equal ar1 ar2) arr1 arr2
  | Gcomment s1, Gcomment s2 -> String.equal s1 s2
  | _, _ -> false

let hash_global g =
  match g with
  | Gtblnorm (gn,lns,mls) ->
      let nlns = Array.length lns in
      let nmls = Array.length mls in
      let env = push_lnames 0 LNmap.empty lns in
      let hmls = hash_mllambda_array gn nlns env (combine nlns nmls) mls in
      combinesmall 1 hmls
  | Gtblfixtype (gn,lns,mls) ->
      let nlns = Array.length lns in
      let nmls = Array.length mls in
      let env = push_lnames 0 LNmap.empty lns in
      let hmls = hash_mllambda_array gn nlns env (combine nlns nmls) mls in
      combinesmall 2 hmls
  | Glet (gn, def) ->
      combinesmall 3 (hash_mllambda gn 0 LNmap.empty def)
  | Gletcase (gn,lns,annot,c,accu,br) ->
      let nlns = Array.length lns in
      let env = push_lnames 0 LNmap.empty lns in
      let t = MLmatch (annot,c,accu,br) in
      combinesmall 4 (combine nlns (hash_mllambda gn nlns env t))
  | Gopen s -> combinesmall 5 (String.hash s)
  | Gtype (ind, arr) ->
    let hash_aux acc (tag,ar) =
      combine3 acc (Int.hash tag) (Int.hash ar)
    in
    combinesmall 6 (combine (Ind.CanOrd.hash ind) (Array.fold_left hash_aux 0 arr))
  | Gcomment s -> combinesmall 7 (String.hash s)

let global_stack = ref ([] : global list)

module HashedTypeGlobal = struct
  type t = global
  let equal = eq_global
  let hash = hash_global
end

module HashtblGlobal = Hashtbl.Make(HashedTypeGlobal)

let global_tbl = HashtblGlobal.create 19991

let clear_global_tbl () = HashtblGlobal.clear global_tbl

let push_global gn t =
  try HashtblGlobal.find global_tbl t
  with Not_found ->
    (global_stack := t :: !global_stack;
    HashtblGlobal.add global_tbl t gn; gn)

let push_global_let gn body =
  push_global gn (Glet (gn,body))

let push_global_fixtype gn params body =
  push_global gn (Gtblfixtype (gn,params,body))

let push_global_norm gn params body =
  push_global gn (Gtblnorm (gn, params, body))

let push_global_case gn params annot a accu bs =
  push_global gn (Gletcase (gn, params, annot, a, accu, bs))

(* Compares [t1] and [t2] up to alpha-equivalence. [t1] and [t2] may contain
   free variables. *)
let eq_mllambda t1 t2 =
  eq_mllambda dummy_gname dummy_gname 0 LNmap.empty LNmap.empty t1 t2

(*s Compilation environment *)

type env =
    { env_rel : mllambda list; (* (MLlocal lname) list *)
      env_bound : int; (* length of env_rel *)
      (* free variables *)
      env_urel : (int * mllambda) list ref; (* list of unbound rel *)
      env_named : (Id.t * mllambda) list ref;
      env_univ : lname option;
      env_const_prefix : Constant.t -> prefix;
      env_const_lazy : Constant.t -> bool;
      env_mind_prefix : MutInd.t -> prefix;
    }

let empty_env univ get_const const_lazy get_mind =
  { env_rel = [];
    env_bound = 0;
    env_urel = ref [];
    env_named = ref [];
    env_univ = univ;
    env_const_prefix = get_const;
    env_const_lazy = const_lazy;
    env_mind_prefix = get_mind;
  }

let push_rel env id =
  let local = fresh_lname id.binder_name in
  local, { env with
           env_rel = MLlocal local :: env.env_rel;
           env_bound = env.env_bound + 1
         }

let push_rels env ids =
  let lnames, env_rel =
    Array.fold_left (fun (names,env_rel) id ->
      let local = fresh_lname id.binder_name in
      (local::names, MLlocal local::env_rel)) ([],env.env_rel) ids in
  Array.of_list (List.rev lnames), { env with
                          env_rel = env_rel;
                          env_bound = env.env_bound + Array.length ids
                        }

let get_rel env id i =
  if i <= env.env_bound then
    List.nth env.env_rel (i-1)
  else
    let i = i - env.env_bound in
    try Int.List.assoc i !(env.env_urel)
    with Not_found ->
      let local = MLlocal (fresh_lname id) in
      env.env_urel := (i,local) :: !(env.env_urel);
      local

let get_var env id =
  try Id.List.assoc id !(env.env_named)
  with Not_found ->
    let local = MLlocal (fresh_lname (Name id)) in
    env.env_named := (id, local)::!(env.env_named);
    local

let fresh_univ () =
  fresh_lname (Name (Id.of_string "univ"))

(*s Traduction of lambda to mllambda *)

let get_prod_name codom =
  match codom with
  | MLlam(ids,_) -> ids.(0).lname
  | _ -> assert false

let get_lname (_,l) =
  match l with
  | MLlocal id -> id
  | _ -> invalid_arg "Nativecode.get_lname"

(* Collects free variables from env in an array of local names *)
let fv_params env =
  let fvn, fvr = !(env.env_named), !(env.env_urel) in
  let size = List.length fvn + List.length fvr in
  let start,params = match env.env_univ with
    | None -> 0, Array.make size dummy_lname
    | Some u -> 1, let t = Array.make (size + 1) dummy_lname in t.(0) <- u; t
  in
  if Array.is_empty params then empty_params
  else begin
    let fvn = ref fvn in
    let i = ref start in
    while not (List.is_empty !fvn) do
      params.(!i) <- get_lname (List.hd !fvn);
      fvn := List.tl !fvn;
      incr i
    done;
    let fvr = ref fvr in
    while not (List.is_empty !fvr) do
      params.(!i) <- get_lname (List.hd !fvr);
      fvr := List.tl !fvr;
      incr i
    done;
    params
  end

let generalize_fv env body =
  mkMLlam (fv_params env) body

let empty_args = [||]

let fv_args env fvn fvr =
  let size = List.length fvn + List.length fvr in
  let start,args = match env.env_univ with
    | None -> 0, Array.make size (MLint 0)
    | Some u -> 1, let t = Array.make (size + 1) (MLint 0) in t.(0) <- MLlocal u; t
  in
  if Array.is_empty args then empty_args
  else
    begin
      let fvn = ref fvn in
      let i = ref start in
      while not (List.is_empty !fvn) do
        args.(!i) <- get_var env (fst (List.hd !fvn));
        fvn := List.tl !fvn;
        incr i
      done;
      let fvr = ref fvr in
      while not (List.is_empty !fvr) do
        let (k,_ as kml) = List.hd !fvr in
        let n = get_lname kml in
        args.(!i) <- get_rel env n.lname k;
        fvr := List.tl !fvr;
        incr i
      done;
      args
    end

let get_value_code i =
  MLprimitive (Get_value,
    [|MLglobal symbols_tbl_name; MLint i|])

let get_sort_code i =
  MLprimitive (Get_sort,
    [|MLglobal symbols_tbl_name; MLint i|])

let get_name_code i =
  MLprimitive (Get_name,
    [|MLglobal symbols_tbl_name; MLint i|])

let get_const_code i =
  MLprimitive (Get_const,
    [|MLglobal symbols_tbl_name; MLint i|])

let get_match_code i =
  MLprimitive (Get_match,
    [|MLglobal symbols_tbl_name; MLint i|])

let get_ind_code i =
  MLprimitive (Get_ind,
    [|MLglobal symbols_tbl_name; MLint i|])

let get_evar_code i =
  MLprimitive (Get_evar,
    [|MLglobal symbols_tbl_name; MLint i|])

let get_instance_code i =
  MLprimitive (Get_instance,
    [|MLglobal symbols_tbl_name; MLint i|])

let get_proj_code i =
  MLprimitive (Get_proj,
    [|MLglobal symbols_tbl_name; MLint i|])

type rlist =
  | Rnil
  | Rcons of lname option mllam_pattern list ref * LNset.t * mllambda * rlist'
and rlist' = rlist ref

let rm_params fv params =
  Array.map (fun l -> if LNset.mem l fv then Some l else None) params

let rec insert pat body rl =
 match !rl with
 | Rnil ->
     let fv = fv_lam body in
     begin match pat with
     | ConstPattern _ as p ->
       rl:= Rcons(ref [p], fv, body, ref Rnil)
     | NonConstPattern (tag,args) ->
       let args = rm_params fv args in
       rl:= Rcons(ref [NonConstPattern (tag,args)], fv, body, ref Rnil)
     end
 | Rcons(l,fv,body',rl) ->
   if eq_mllambda body body' then
     match pat with
     | ConstPattern _ as p ->
       l := p::!l
     | NonConstPattern (tag,args) ->
       let args = rm_params fv args in
       l := NonConstPattern (tag,args)::!l
   else insert pat body rl

let rec to_list rl =
  match !rl with
  | Rnil -> []
  | Rcons(l,_,body,tl) -> (!l,body)::to_list tl

let merge_branches t =
  let newt = ref Rnil in
  Array.iter (fun (pat,body) -> insert pat body newt) t;
  Array.of_list (to_list newt)

let app_prim p args = MLprimitive (p, args)

let ml_empty_instance = MLprimitive (Mk_empty_instance, [||])

type prim_aux =
  | PAprim of string * pconstant * CPrimitives.t * prim_aux array
  | PAml of mllambda

let add_check cond targs args =
  let aux cond t a =
    match t, a with
    | CPrimitives.(PITT_type (PT_int63, _)), PAml(MLprimitive (Mk_uint, _)) -> cond
    | CPrimitives.(PITT_type (PT_array, _)), PAml(MLprimitive (MLparray_of_array, _)) -> cond
    | CPrimitives.(PITT_type (PT_array, _)), PAml(MLprimitive (Get_value ,_)) -> cond
    | CPrimitives.(PITT_type (prim_ty, _)), PAml ml ->
       (* FIXME: use explicit equality function *)
       let c = (CPrimitives.PTE prim_ty, ml) in
       if List.mem c cond then cond else c::cond
    | _ -> cond
  in
  Array.fold_left2 aux cond targs args

let extract_prim env ml_of l =
  let decl = ref [] in
  let cond = ref [] in
  let type_args p =
    let params, args_ty, _ = CPrimitives.types p in
    List.length params, Array.of_list args_ty in
  let rec aux l =
    match l with
    | Lprim (kn, p, args) ->
      let prefix = env.env_const_prefix (fst kn) in
      let nparams, targs = type_args p in
      let args = Array.map aux args in
      let checked_args = Array.init (Array.length args - nparams) (fun i -> args.(i+nparams)) in
      cond := add_check !cond targs checked_args;
      PAprim (prefix, kn, p, args)
    | Lrel _ | Lvar _ | Luint _ | Lval _ | Lconst _ -> PAml (ml_of l)
    | _ ->
      let x = fresh_lname Anonymous in
      decl := (x,ml_of l)::!decl;
      PAml (MLlocal x) in
  let res = aux l in
  (!decl, !cond, res)

let cast_to_int v =
  match v with
  | MLint _ -> v
  | _ -> MLprimitive (Val_to_int, [|v|])

let ml_of_instance instance u =
  if UVars.Instance.is_empty u then [||]
  else
    let i = push_symbol (SymbInstance u) in
    let u_code = get_instance_code i in
    let has_variable =
      let qs, us = UVars.Instance.to_array u in
      Array.exists (fun q -> Option.has_some (Sorts.Quality.var_index q)) qs
      || Array.exists (fun u -> Option.has_some (Univ.Level.var_index u)) us
    in
    let u_code =
      if has_variable then
        (* if there are variables then [instance] guaranteed non-None *)
        let univ = MLprimitive (MLmagic, [|MLlocal (Option.get instance)|]) in
        MLprimitive (MLsubst_instance_instance, [|univ; u_code|])
      else u_code
    in
    [|MLprimitive (MLmagic, [|u_code|])|]

let compile_prim env decl cond paux =

  let rec opt_prim_aux paux =
    match paux with
    | PAprim(_prefix, _kn, op, args) ->
      let n = CPrimitives.nparams op in
      let args = Array.map opt_prim_aux (Array.sub args n (Array.length args - n)) in
      app_prim (Coq_primitive(op, false)) args
    | PAml ml -> ml

  and naive_prim_aux paux =
    match paux with
    | PAprim(prefix, (kn,u), op, args) ->
      let uarg = ml_of_instance env.env_univ u in
      let prim_const = mkMLapp (MLglobal (Gconstant(prefix,kn))) uarg in
      let prim = MLprimitive ((Coq_primitive(op, true)), [|prim_const|]) in
      mkMLapp prim (Array.map naive_prim_aux args)
    | PAml ml -> ml
  in

  let compile_cond cond paux =
    match cond with
    | [] -> opt_prim_aux paux
    | [CPrimitives.(PTE PT_int63), c1] ->
      MLif(app_prim Is_int [|c1|], opt_prim_aux paux, naive_prim_aux paux)
    | _ ->
      let ci, co =
        let is_int =
          function CPrimitives.(PTE PT_int63), _ -> true | _ -> false in
        List.partition is_int cond in
      let condi =
        let cond =
          List.fold_left
            (fun ml (_, c) -> app_prim MLland [| ml; cast_to_int c|])
            (MLint 0) ci in
        app_prim MLmagic [|cond|] in
      let condo = match co with
        | [] -> MLint 0
        | (CPrimitives.PTE ty, c1) :: condo ->
          let check = match ty with
          | CPrimitives.PT_float64 -> Is_float
          | CPrimitives.PT_array -> Is_parray
          | CPrimitives.PT_int63 -> assert false
          | CPrimitives.PT_string -> Is_string
          in
           List.fold_left
             (fun ml (_, c) -> app_prim MLand [| ml; app_prim check [|c|]|])
             (app_prim check [|c1|]) condo in
      match ci, co with
      | [], [] -> opt_prim_aux paux
      | _ :: _, [] ->
         MLif(condi, naive_prim_aux paux, opt_prim_aux paux)
      | [], _ :: _ ->
         MLif(condo, opt_prim_aux paux, naive_prim_aux paux)
      | _ :: _, _ :: _ ->
         let cond = app_prim MLand [|condo; app_prim MLnot [|condi|]|] in
         MLif(cond, opt_prim_aux paux, naive_prim_aux paux) in

  let add_decl decl body =
    List.fold_left (fun body (x,d) -> MLlet(x,d,body)) body decl in

  (* The optimizations done for checking if integer values are closed are valid
     only on 64-bit architectures. So on 32-bit architectures, we fall back to less optimized checks. *)
  if max_int = 1073741823 (* 32-bits *) then
    add_decl decl (naive_prim_aux paux)
  else
    add_decl decl (compile_cond cond paux)

 let rec ml_of_lam env l t =
  match t with
  | Lrel(id ,i) -> get_rel env id i
  | Lvar id -> get_var env id
  | Levar(evk, args) ->
     let i = push_symbol (SymbEvar evk) in
     (** Arguments are *not* reversed in evar instances in native compilation *)
     let args = MLarray(Array.map (ml_of_lam env l) args) in
     MLprimitive (Mk_evar, [|get_evar_code i; args|])
  | Lprod(dom,codom) ->
      let dom = ml_of_lam env l dom in
      let codom = ml_of_lam env l codom in
      let n = get_prod_name codom in
      let i = push_symbol (SymbName n) in
      MLprimitive (Mk_prod, [|get_name_code i;dom;codom|])
  | Llam(ids,body) ->
    let lnames,env = push_rels env ids in
    MLlam(lnames, ml_of_lam env l body)
  | Llet(id,def,body) ->
      let def = ml_of_lam env l def in
      let lname, env = push_rel env id in
      let body = ml_of_lam env l body in
      MLlet(lname,def,body)
  | Lapp(f,args) ->
      MLapp(ml_of_lam env l f, Array.map (ml_of_lam env l) args)
  | Lconst (c, u) ->
     let prefix = env.env_const_prefix c in
     let args = ml_of_instance env.env_univ u in
     let ans = mkMLapp (MLglobal(Gconstant (prefix, c))) args in
     if env.env_const_lazy c then MLapp (MLglobal (Ginternal "Lazy.force"), [|ans|])
     else ans
  | Lproj (p, c) ->
    let ind = Projection.Repr.inductive p in
    let i = Projection.Repr.arg p in
    let prefix = env.env_mind_prefix (fst ind) in
    MLapp (MLglobal(Gproj (prefix, ind, i)), [| ml_of_lam env l c |])
  | Lprim _ ->
    let decl,cond,paux = extract_prim env (ml_of_lam env l) t in
    compile_prim env decl cond paux
  | Lcase (annot,p,a,bs) ->
      (* let predicate_uid fv_pred = compilation of p
         let rec case_uid fv a_uid =
           match a_uid with
           | Accu _ => mk_sw (predicate_uid fv_pred) (case_uid fv) a_uid
           | Ci argsi => compilation of branches
         compile case = case_uid fv (compilation of a) *)
      (* Compilation of the predicate *)
         (* Remark: if we do not want to compile the predicate we
            should a least compute the fv, then store the lambda representation
            of the predicate (not the mllambda) *)
      let annot =
        let (ci, tbl, knd) = annot in {
          asw_ind = ci.ci_ind;
          asw_reloc = tbl;
          asw_finite = knd <> CoFinite;
          asw_prefix = env.env_mind_prefix (fst ci.ci_ind);
      } in
      let env_p = empty_env env.env_univ env.env_const_prefix env.env_const_lazy env.env_mind_prefix in
      let pn = fresh_gpred l in
      let mlp = ml_of_lam env_p l p in
      let mlp = generalize_fv env_p mlp in
      let (pfvn,pfvr) = !(env_p.env_named), !(env_p.env_urel) in
      let pn = push_global_let pn mlp in
      (* Compilation of the case *)
      let env_c = empty_env env.env_univ env.env_const_prefix env.env_const_lazy env.env_mind_prefix in
      let a_uid = fresh_lname Anonymous in
      let la_uid = MLlocal a_uid in
      (* compilation of branches *)
      let nbconst = Array.length bs.constant_branches in
      let nbtotal = nbconst + Array.length bs.nonconstant_branches in
      let br = Array.init nbtotal (fun i -> if i < Array.length bs.constant_branches then
                                  (ConstPattern i, ml_of_lam env_c l bs.constant_branches.(i))
                                else
                                  let (params, body) = bs.nonconstant_branches.(i-nbconst) in
                                  let lnames, env_c = push_rels env_c params in
                                  (NonConstPattern (i-nbconst+1,lnames), ml_of_lam env_c l body)
                              )
      in
      let cn = fresh_gcase l in
      (* Compilation of accu branch *)
      let pred = MLapp(MLglobal pn, fv_args env_c pfvn pfvr) in
      let (fvn, fvr) = !(env_c.env_named), !(env_c.env_urel) in
      let cn_fv = mkMLapp (MLglobal cn) (fv_args env_c fvn fvr) in
         (* remark : the call to fv_args does not add free variables in env_c *)
      let i = push_symbol (SymbMatch annot) in
      let accu =
        MLprimitive (Mk_sw,
              [| get_match_code i; MLprimitive (Cast_accu, [|la_uid|]);
                 pred;
                 cn_fv |]) in
(*      let body = MLlam([|a_uid|], MLmatch(annot, la_uid, accu, bs)) in
      let case = generalize_fv env_c body in *)
      let cn = push_global_case cn (Array.append (fv_params env_c) [|a_uid|])
        annot la_uid accu (merge_branches br)
      in
      (* Final result *)
      let arg = ml_of_lam env l a in
      let force =
        if annot.asw_finite then arg
        else mkForceCofix annot.asw_prefix annot.asw_ind arg in
      mkMLapp (MLapp (MLglobal cn, fv_args env fvn fvr)) [|force|]
  | Lfix ((rec_pos, inds, start), (ids, tt, tb)) ->
      (* let type_f fvt = [| type fix |]
         let norm_f1 fv f1 .. fn params1 = body1
         ..
         let norm_fn fv f1 .. fn paramsn = bodyn
         let norm fv f1 .. fn =
            [|norm_f1 fv f1 .. fn; ..; norm_fn fv f1 .. fn|]
         compile fix =
           let rec f1 params1 =
             if is_accu rec_pos.(1) then mk_fix (type_f fvt) (norm fv) params1
             else norm_f1 fv f1 .. fn params1
           and .. and fn paramsn =
             if is_accu rec_pos.(n) then mk_fix (type_f fvt) (norm fv) paramsn
             else norm_fn fv f1 .. fv paramsn in
           start
      *)
      (* Compilation of type *)
      let env_t = empty_env env.env_univ env.env_const_prefix env.env_const_lazy env.env_mind_prefix in
      let ml_t = Array.map (ml_of_lam env_t l) tt in
      let params_t = fv_params env_t in
      let args_t = fv_args env !(env_t.env_named) !(env_t.env_urel) in
      let gft = fresh_gfixtype l in
      let gft = push_global_fixtype gft params_t ml_t in
      let mk_type = MLapp(MLglobal gft, args_t) in
      (* Compilation of norm_i *)
      let ndef = Array.length ids in
      let lf,env_n = push_rels (empty_env env.env_univ env.env_const_prefix env.env_const_lazy env.env_mind_prefix) ids in
      let t_params = Array.make ndef [||] in
      let t_norm_f = Array.make ndef (Gnorm (l,-1)) in
      let mk_let _envi (id,def) t = MLlet (id,def,t) in
      let mk_lam_or_let (params,lets,env) (id,def) =
        let ln,env' = push_rel env id in
        match def with
        | None -> (ln::params,lets,env')
        | Some lam -> (params, (ln,ml_of_lam env l lam)::lets,env')
      in
      let ml_of_fix i body =
        let varsi, bodyi = decompose_Llam_Llet body in
        let paramsi,letsi,envi =
          Array.fold_left mk_lam_or_let ([],[],env_n) varsi
        in
        let paramsi,letsi =
          Array.of_list (List.rev paramsi), Array.of_list (List.rev letsi)
        in
        t_norm_f.(i) <- fresh_gnorm l;
        let bodyi = ml_of_lam envi l bodyi in
        t_params.(i) <- paramsi;
        let bodyi = Array.fold_right (mk_let envi) letsi bodyi in
        mkMLlam paramsi bodyi
      in
      let tnorm = Array.mapi ml_of_fix tb in
      let fvn,fvr = !(env_n.env_named), !(env_n.env_urel) in
      let fv_params = fv_params env_n in
      let fv_args' = Array.map (fun id -> MLlocal id) fv_params in
      let norm_params = Array.append fv_params lf in
      let t_norm_f = Array.mapi (fun i body ->
        push_global_let (t_norm_f.(i)) (mkMLlam norm_params body)) tnorm in
      let norm = fresh_gnormtbl l in
      let norm = push_global_norm norm fv_params
         (Array.map (fun g -> mkMLapp (MLglobal g) fv_args') t_norm_f) in
      (* Compilation of fix *)
      let fv_args = fv_args env fvn fvr in
      let lf, _env = push_rels env ids in
      let lf_args = Array.map (fun id -> MLlocal id) lf in
      let mk_norm = MLapp(MLglobal norm, fv_args) in
      let mkrec i lname =
        let paramsi = t_params.(i) in
        let reci = MLlocal (paramsi.(rec_pos.(i))) in
        let pargsi = Array.map (fun id -> MLlocal id) paramsi in
        let ind = inds.(i) in
        let prefix = env.env_mind_prefix (fst ind) in
        let body =
          MLif(MLisaccu (prefix, ind, reci),
               mkMLapp
                 (MLprimitive ((Mk_fix(rec_pos,i)),
                        [|mk_type; mk_norm|]))
                 pargsi,
               MLapp(MLglobal t_norm_f.(i),
                     Array.concat [fv_args;lf_args;pargsi]))
        in
        (lname, paramsi, body) in
      MLletrec(Array.mapi mkrec lf, lf_args.(start))
  | Lcofix (start, (ids, tt, tb)) ->
      (* Compilation of type *)
      let env_t = empty_env env.env_univ env.env_const_prefix env.env_const_lazy env.env_mind_prefix in
      let ml_t = Array.map (ml_of_lam env_t l) tt in
      let params_t = fv_params env_t in
      let args_t = fv_args env !(env_t.env_named) !(env_t.env_urel) in
      let gft = fresh_gfixtype l in
      let gft = push_global_fixtype gft params_t ml_t in
      let mk_type = MLapp(MLglobal gft, args_t) in
      (* Compilation of norm_i *)
      let ndef = Array.length ids in
      let lf,env_n = push_rels (empty_env env.env_univ env.env_const_prefix env.env_const_lazy env.env_mind_prefix) ids in
      let t_params = Array.make ndef [||] in
      let t_norm_f = Array.make ndef (Gnorm (l,-1)) in
      let ml_of_fix i body =
        let idsi,bodyi = decompose_Llam body in
        let paramsi, envi = push_rels env_n idsi in
        t_norm_f.(i) <- fresh_gnorm l;
        let bodyi = ml_of_lam envi l bodyi in
        t_params.(i) <- paramsi;
        mkMLlam paramsi bodyi in
      let tnorm = Array.mapi ml_of_fix tb in
      let fvn,fvr = !(env_n.env_named), !(env_n.env_urel) in
      let fv_params = fv_params env_n in
      let fv_args' = Array.map (fun id -> MLlocal id) fv_params in
      let norm_params = Array.append fv_params lf in
      let t_norm_f = Array.mapi (fun i body ->
        push_global_let (t_norm_f.(i)) (mkMLlam norm_params body)) tnorm in
      let norm = fresh_gnormtbl l in
      let norm = push_global_norm norm fv_params
        (Array.map (fun g -> mkMLapp (MLglobal g) fv_args') t_norm_f) in
      (* Compilation of fix *)
      let fv_args = fv_args env fvn fvr in
      let mk_norm = MLapp(MLglobal norm, fv_args) in
      let lnorm = fresh_lname Anonymous in
      let ltype = fresh_lname Anonymous in
      let lf, _env = push_rels env ids in
      let lf_args = Array.map (fun id -> MLlocal id) lf in
      let upd i _lname cont =
        let paramsi = t_params.(i) in
        let pargsi = Array.map (fun id -> MLlocal id) paramsi in
        let uniti = fresh_lname Anonymous in
        let body =
          MLlam(Array.append paramsi [|uniti|],
                MLapp(MLglobal t_norm_f.(i),
                      Array.concat [fv_args;lf_args;pargsi])) in
        MLsequence(MLprimitive (Upd_cofix, [|lf_args.(i);body|]),
                   cont) in
      let upd = Array.fold_right_i upd lf lf_args.(start) in
      let mk_let i lname cont =
        MLlet(lname,
              MLprimitive ((Mk_cofix i),[| MLlocal ltype; MLlocal lnorm|]),
              cont) in
      let init = Array.fold_right_i mk_let lf upd in
      MLlet(lnorm, mk_norm, MLlet(ltype, mk_type, init))
  (*
      let mkrec i lname =
        let paramsi = t_params.(i) in
        let pargsi = Array.map (fun id -> MLlocal id) paramsi in
        let uniti = fresh_lname Anonymous in
        let body =
          MLapp( MLprimitive(Mk_cofix i),
                 [|mk_type;mk_norm;
                   MLlam([|uniti|],
                         MLapp(MLglobal t_norm_f.(i),
                               Array.concat [fv_args;lf_args;pargsi]))|]) in
        (lname, paramsi, body) in
      MLletrec(Array.mapi mkrec lf, lf_args.(start)) *)

  | Lint tag -> MLprimitive (Mk_int, [|MLint tag|])

  | Lmakeblock (cn,tag,args) ->
     let prefix = env.env_mind_prefix (fst cn) in
     let args = Array.map (ml_of_lam env l) args in
     MLconstruct(prefix,cn,tag,args)
  | Luint i -> MLprimitive (Mk_uint, [|MLuint i|])
  | Lfloat f -> MLprimitive (Mk_float, [|MLfloat f|])
  | Lstring s -> MLprimitive (Mk_string, [|MLstring s|])
  | Lparray (t,def) ->
    let def = ml_of_lam env l def in
    MLprimitive (MLparray_of_array, [| MLarray (Array.map (ml_of_lam env l) t); def |])
  | Lval v ->
      let i = push_symbol (SymbValue v) in get_value_code i
  | Lsort s ->
    let i = push_symbol (SymbSort s) in
    let uarg = match env.env_univ with
      | None -> ml_empty_instance
      | Some u -> MLlocal u
    in
    (* FIXME: use a dedicated cast function *)
    let uarg = MLprimitive (MLmagic, [|uarg|]) in
    MLprimitive (Mk_sort, [|get_sort_code i; uarg|])
  | Lind (ind, u) ->
     let prefix = env.env_mind_prefix (fst ind) in
     let uargs = ml_of_instance env.env_univ u in
     mkMLapp (MLglobal (Gind (prefix, ind))) uargs

let mllambda_of_lambda univ constpref constlazy mindpref auxdefs l t =
  let env = empty_env univ constpref constlazy mindpref in
  global_stack := auxdefs;
  let ml = ml_of_lam env l t in
  let fv_rel = !(env.env_urel) in
  let fv_named = !(env.env_named) in
  (* build the free variables *)
  let get_lname (_,t) =
   match t with
   | MLlocal x -> x
   | _ -> assert false in
  let params =
    List.append (List.map get_lname fv_rel) (List.map get_lname fv_named) in
  if List.is_empty params then
    (!global_stack, ([],[]), ml)
  (* final result : global list, fv, ml *)
  else
    (!global_stack, (fv_named, fv_rel), mkMLlam (Array.of_list params) ml)

(** Code optimization **)

(** Optimization of match and fix *)

let can_subst l =
  match l with
  | MLlocal _ | MLint _ | MLuint _ | MLglobal _ -> true
  | _ -> false

let subst s l =
  if LNmap.is_empty s then l
  else
    let rec aux l =
      match l with
      | MLlocal id -> (try LNmap.find id s with Not_found -> l)
      | MLglobal _ | MLint _ | MLuint _ | MLfloat _ | MLstring _ -> l
      | MLprimitive (p, args) -> MLprimitive (p, Array.map aux args)
      | MLlam(params,body) -> MLlam(params, aux body)
      | MLletrec(defs,body) ->
        let arec (f,params,body) = (f,params,aux body) in
        MLletrec(Array.map arec defs, aux body)
      | MLlet(id,def,body) -> MLlet(id,aux def, aux body)
      | MLapp(f,args) -> MLapp(aux f, Array.map aux args)
      | MLif(t,b1,b2) -> MLif(aux t, aux b1, aux b2)
      | MLmatch(annot,a,accu,bs) ->
          let auxb (cargs,body) = (cargs,aux body) in
          MLmatch(annot,a,aux accu, Array.map auxb bs)
      | MLconstruct(prefix,c,tag,args) -> MLconstruct(prefix,c,tag,Array.map aux args)
      | MLsetref(s,l1) -> MLsetref(s,aux l1)
      | MLsequence(l1,l2) -> MLsequence(aux l1, aux l2)
      | MLarray arr -> MLarray (Array.map aux arr)
      | MLisaccu (s, ind, l) -> MLisaccu (s, ind, aux l)
    in
    aux l

let add_subst id v s =
  match v with
  | MLlocal id' when Int.equal id.luid id'.luid -> s
  | _ -> LNmap.add id v s

let subst_norm params args s =
  let len = Array.length params in
  assert (Int.equal (Array.length args) len && Array.for_all can_subst args);
  let s = ref s in
  for i = 0 to len - 1 do
    s := add_subst params.(i) args.(i) !s
  done;
  !s

let subst_case params args s =
  let len = Array.length params in
  assert (len > 0 &&
          Int.equal (Array.length args) len &&
          let r = ref true and i = ref 0 in
          (* we test all arguments excepted the last *)
          while !i < len - 1  && !r do r := can_subst args.(!i); incr i done;
          !r);
  let s = ref s in
  for i = 0 to len - 2 do
    s := add_subst params.(i) args.(i) !s
  done;
  !s, params.(len-1), args.(len-1)

let empty_gdef = Int.Map.empty, Int.Map.empty
let get_norm (gnorm, _) i = Int.Map.find i gnorm
let get_case (_, gcase) i = Int.Map.find i gcase

let all_lam n bs =
  let f (_, l) =
    match l with
    | MLlam(params, _) -> Int.equal (Array.length params) n
    | _ -> false in
  Array.for_all f bs

let commutative_cut annot a accu bs args =
  let mkb (c,b) =
     match b with
     | MLlam(params, body) ->
         (c, Array.fold_left2 (fun body x v -> MLlet(x,v,body)) body params args)
     | _ -> assert false in
  MLmatch(annot, a, mkMLapp accu args, Array.map mkb bs)

let optimize gdef l =
  let rec optimize s l =
    match l with
    | MLlocal id -> (try LNmap.find id s with Not_found -> l)
    | MLglobal _ | MLint _ | MLuint _ | MLfloat _ | MLstring _ -> l
    | MLprimitive (p, args) ->
        MLprimitive (p, Array.map (optimize s) args)
    | MLlam(params,body) ->
        MLlam(params, optimize s body)
    | MLletrec(decls,body) ->
        let opt_rec (f,params,body) = (f,params,optimize s body ) in
        MLletrec(Array.map opt_rec decls, optimize s body)
    | MLlet(id,def,body) ->
        let def = optimize s def in
        if can_subst def then optimize (add_subst id def s) body
        else MLlet(id,def,optimize s body)
    | MLapp(f, args) ->
        let args = Array.map (optimize s) args in
        begin match f with
        | MLglobal (Gnorm (_,i)) ->
            (try
              let params,body = get_norm gdef i in
              let s = subst_norm params args s in
              optimize s body
            with Not_found -> MLapp(optimize s f, args))
        | MLglobal (Gcase (_,i)) ->
            (try
              let params,body = get_case gdef i in
              let s, id, arg = subst_case params args s in
              if can_subst arg then optimize (add_subst id arg s) body
              else MLlet(id, arg, optimize s body)
            with Not_found ->  MLapp(optimize s f, args))
        | _ ->
            let f = optimize s f in
            match f with
            | MLmatch (annot,a,accu,bs) ->
              if all_lam (Array.length args) bs then
                commutative_cut annot a accu bs args
              else MLapp(f, args)
            | _ -> MLapp(f, args)

        end
    | MLif(t,b1,b2) ->
       (* This optimization is critical: it applies to all fixpoints that start
       by matching on their recursive argument *)
        let t = optimize s t in
        let b1 = optimize s b1 in
        let b2 = optimize s b2 in
        begin match t, b2 with
        | MLisaccu (_, _, l1), MLmatch(annot, l2, _, bs)
            when eq_mllambda l1 l2 -> MLmatch(annot, l1, b1, bs)
        | _, _ -> MLif(t, b1, b2)
        end
    | MLmatch(annot,a,accu,bs) ->
        let opt_b (cargs,body) = (cargs,optimize s body) in
        MLmatch(annot, optimize s a, subst s accu, Array.map opt_b bs)
    | MLconstruct(prefix,c,tag,args) ->
        MLconstruct(prefix,c,tag,Array.map (optimize s) args)
    | MLsetref(r,l) -> MLsetref(r, optimize s l)
    | MLsequence(l1,l2) -> MLsequence(optimize s l1, optimize s l2)
    | MLarray arr -> MLarray (Array.map (optimize s) arr)
    | MLisaccu (pf, ind, l) -> MLisaccu (pf, ind, optimize s l)
  in
  optimize LNmap.empty l

let optimize_stk stk =
  let add_global gdef g =
    match g with
    | Glet (Gnorm (_,i), body) ->
        let (gnorm, gcase) = gdef in
        (Int.Map.add i (decompose_MLlam body) gnorm, gcase)
    | Gletcase(Gcase (_,i), params, annot,a,accu,bs) ->
        let (gnorm,gcase) = gdef in
        (gnorm, Int.Map.add i (params,MLmatch(annot,a,accu,bs)) gcase)
    | Gletcase _ -> assert false
    | _ -> gdef in
  let gdef = List.fold_left add_global empty_gdef stk in
  let optimize_global g =
    match g with
    | Glet(Gconstant (prefix, c), body) ->
        Glet(Gconstant (prefix, c), optimize gdef body)
    | _ -> g in
  List.map optimize_global stk

(** Printing to ocaml **)
(* Redefine a bunch of functions in module Names to generate names
   acceptable to OCaml. *)
let string_of_id s = Unicode.ascii_of_ident (Id.to_string s)
let string_of_label l = string_of_id (Label.to_id l)

let string_of_dirpath = function
  | [] -> "_"
  | sl -> String.concat "_" (List.rev_map string_of_id sl)

(* The first letter of the file name has to be a capital to be accepted by *)
(* OCaml as a module identifier.                                           *)
let string_of_dirpath s = "N"^string_of_dirpath s

let mod_uid_of_dirpath dir = string_of_dirpath (DirPath.repr dir)

let link_info_of_dirpath dir =
  Linked (mod_uid_of_dirpath dir ^ ".")

let string_of_name x =
  match x with
    | Anonymous -> "anonymous" (* assert false *)
    | Name id -> string_of_id id

let string_of_label_def l =
  match l with
    | None -> ""
    | Some l -> string_of_label l

(* Relativization of module paths *)
let rec list_of_mp acc = function
  | MPdot (mp,l) -> list_of_mp (string_of_label l::acc) mp
  | MPfile dp ->
      let dp = DirPath.repr dp in
      string_of_dirpath dp :: acc
  | MPbound mbid -> ("X"^string_of_id (MBId.to_id mbid))::acc

let list_of_mp mp = list_of_mp [] mp

let string_of_kn kn =
  let (mp,l) = KerName.repr kn in
  let mp = list_of_mp mp in
  String.concat "_" mp ^ "_" ^ string_of_label l

let string_of_con c = string_of_kn (Constant.user c)
let string_of_mind mind = string_of_kn (MutInd.user mind)
let string_of_ind (mind,i) = string_of_kn (MutInd.user mind) ^ "_" ^ string_of_int i

let string_of_gname g =
  match g with
  | Gind (prefix, (mind, i)) ->
      Format.sprintf "%sindaccu_%s_%i" prefix (string_of_mind mind) i
  | Gconstant (prefix, c) ->
      Format.sprintf "%sconst_%s" prefix (string_of_con c)
  | Gproj (prefix, (mind, n), i) ->
      Format.sprintf "%sproj_%s_%i_%i" prefix (string_of_mind mind) n i
  | Gcase (l,i) ->
      Format.sprintf "case_%s_%i" (string_of_label_def l) i
  | Gpred (l,i) ->
      Format.sprintf "pred_%s_%i" (string_of_label_def l) i
  | Gfixtype (l,i) ->
      Format.sprintf "fixtype_%s_%i" (string_of_label_def l) i
  | Gnorm (l,i) ->
      Format.sprintf "norm_%s_%i" (string_of_label_def l) i
  | Ginternal s -> Format.sprintf "%s" s
  | Gnormtbl (l,i) ->
      Format.sprintf "normtbl_%s_%i" (string_of_label_def l) i
  | Grel i ->
      Format.sprintf "rel_%i" i
  | Gnamed id ->
      Format.sprintf "named_%s" (string_of_id id)

let pp_gname fmt g =
  Format.fprintf fmt "%s" (string_of_gname g)

let pp_lname fmt ln =
  Format.fprintf fmt "x_%s_%i" (string_of_name ln.lname) ln.luid

let pp_ldecls fmt ids =
  let len = Array.length ids in
  for i = 0 to len - 1 do
    Format.fprintf fmt " (%a : Nativevalues.t)" pp_lname ids.(i)
  done

let string_of_construct prefix ~constant ind tag =
  let base = if constant then "Int" else "Construct" in
  Format.sprintf "%s%s_%s_%i" prefix base (string_of_ind ind) tag

let string_of_accu_construct prefix ind =
  Format.sprintf "%sAccu_%s" prefix (string_of_ind ind)

let pp_int fmt i =
  if i < 0 then Format.fprintf fmt "(%i)" i else Format.fprintf fmt "%i" i

let pp_mllam fmt l =

  let rec pp_mllam fmt l =
    match l with
    | MLlocal ln -> Format.fprintf fmt "@[%a@]" pp_lname ln
    | MLglobal g -> Format.fprintf fmt "@[%a@]" pp_gname g
    | MLprimitive (p, args) ->
      Format.fprintf fmt "@[%a@ %a@]" pp_primitive p (pp_args true) args
    | MLlam(ids,body) ->
        Format.fprintf fmt "@[(fun%a@ ->@\n %a)@]"
          pp_ldecls ids pp_mllam body
    | MLletrec(defs, body) ->
        Format.fprintf fmt "@[(%a@ in@\n%a)@]" pp_letrec defs
          pp_mllam body
    | MLlet(id,def,body) ->
        Format.fprintf fmt "@[(let@ %a@ =@\n %a@ in@\n%a)@]"
          pp_lname id pp_mllam def pp_mllam body
    | MLapp(f, args) ->
        Format.fprintf fmt "@[%a@ %a@]" pp_mllam f (pp_args true) args
    | MLif(t,l1,l2) ->
        Format.fprintf fmt "@[(if %a then@\n  %a@\nelse@\n  %a)@]"
          pp_mllam t pp_mllam l1 pp_mllam l2
    | MLmatch (annot, c, accu_br, br) ->
      let ind = annot.asw_ind in
      let prefix = annot.asw_prefix in
      let accu = string_of_accu_construct prefix ind in
      Format.fprintf fmt
        "@[begin match Obj.magic (%a) with@\n| %s _ ->@\n  %a@\n%aend@]"
        pp_mllam c accu pp_mllam accu_br (pp_branches prefix ind) br

    | MLconstruct(prefix,ind,tag,args) ->
        Format.fprintf fmt "@[(Obj.magic (%s%a) : Nativevalues.t)@]"
          (string_of_construct prefix ~constant:false ind tag) pp_cargs args
    | MLint i -> pp_int fmt i
    | MLuint i -> Format.fprintf fmt "(%s)" (Uint63.compile i)
    | MLfloat f -> Format.fprintf fmt "(%s)" (Float64.compile f)
    | MLstring s -> Format.fprintf fmt "(%s)" (Pstring.compile s)
    | MLsetref (s, body) ->
        Format.fprintf fmt "@[%s@ :=@\n %a@]" s pp_mllam body
    | MLsequence(l1,l2) ->
        Format.fprintf fmt "@[%a;@\n%a@]" pp_mllam l1 pp_mllam l2
    | MLarray arr ->
      (* We need to ensure that the array does not use the flat representation
          if ever the first argument is a float *)
      let len = Array.length arr in
      if Int.equal len 0 then begin
        Format.fprintf fmt "@[(Obj.magic [||])@]"
      end else if Int.equal len 1 then begin
        (* We have to emulate a 1-uplet *)
        Format.fprintf fmt "@[(Obj.magic (ref (%a)))@]" pp_mllam arr.(0)
      end else begin
        Format.fprintf fmt "@[(Obj.magic (";
        for i = 0 to len - 2 do
          Format.fprintf fmt "%a,@ " pp_mllam arr.(i)
        done;
        pp_mllam fmt arr.(len-1);
        Format.fprintf fmt "))@]"
      end;
    | MLisaccu (prefix, ind, c) ->
        let accu = string_of_accu_construct prefix ind in
        Format.fprintf fmt
          "@[begin match Obj.magic (%a) with@\n| %s _ ->@\n  true@\n| _ ->@\n  false@\nend@]"
        pp_mllam c accu

  and pp_letrec fmt defs =
    let len = Array.length defs in
    let pp_one_rec (fn, argsn, body) =
      Format.fprintf fmt "%a%a =@\n  %a"
        pp_lname fn
        pp_ldecls argsn pp_mllam body in
    Format.fprintf fmt "@[let rec ";
    pp_one_rec defs.(0);
    for i = 1 to len - 1 do
      Format.fprintf fmt "@\nand ";
      pp_one_rec defs.(i)
    done;

  and pp_blam fmt l =
    match l with
    | MLprimitive (_, _) | MLlam _ | MLletrec _ | MLlet _ | MLapp _ | MLif _ ->
        Format.fprintf fmt "(%a)" pp_mllam l
    | MLconstruct(_,_,_,args) when Array.length args > 0 ->
        Format.fprintf fmt "(%a)" pp_mllam l
    | _ -> pp_mllam fmt l

  and pp_args sep fmt args =
    let sep = if sep then " " else "," in
    let len = Array.length args in
    if len > 0 then begin
      Format.fprintf fmt "%a" pp_blam args.(0);
      for i = 1 to len - 1 do
        Format.fprintf fmt "%s%a" sep pp_blam args.(i)
      done
    end

  and pp_cargs fmt args =
    let len = Array.length args in
    match len with
    | 0 -> ()
    | 1 -> Format.fprintf fmt " %a" pp_blam args.(0)
    | _ -> Format.fprintf fmt "(%a)" (pp_args false) args

  and pp_cparam fmt param =
    match param with
    | Some l -> pp_mllam fmt (MLlocal l)
    | None -> Format.fprintf fmt "_"

  and pp_cparams fmt params =
    let len = Array.length params in
    match len with
    | 0 -> ()
    | 1 -> Format.fprintf fmt " %a" pp_cparam params.(0)
    | _ ->
        let aux fmt params =
          Format.fprintf fmt "%a" pp_cparam params.(0);
          for i = 1 to len - 1 do
            Format.fprintf fmt ",%a" pp_cparam params.(i)
          done in
        Format.fprintf fmt "(%a)" aux params

  and pp_branches prefix ind fmt bs =
    let pp_branch (cargs,body) =
      let pp_pat fmt = function
        | ConstPattern i ->
          Format.fprintf fmt "| %s "
            (string_of_construct prefix ~constant:true ind i)
        | NonConstPattern (tag,args) ->
          Format.fprintf fmt "| %s%a "
            (string_of_construct prefix ~constant:false ind tag) pp_cparams args in
      let rec pp_pats fmt pats =
        match pats with
        | [] -> ()
        | pat::pats ->
          Format.fprintf fmt "%a%a" pp_pat pat pp_pats pats
      in
      Format.fprintf fmt "%a ->@\n  %a@\n" pp_pats cargs pp_mllam body
    in
    Array.iter pp_branch bs

  and pp_primitive fmt = function
    | Mk_prod -> Format.fprintf fmt "mk_prod"
    | Mk_sort -> Format.fprintf fmt "mk_sort_accu"
    | Mk_ind -> Format.fprintf fmt "mk_ind_accu"
    | Mk_const -> Format.fprintf fmt "mk_constant_accu"
    | Mk_sw -> Format.fprintf fmt "mk_sw_accu"
    | Mk_fix(rec_pos,start) ->
        let pp_rec_pos fmt rec_pos =
          Format.fprintf fmt "@[[| %i" rec_pos.(0);
          for i = 1 to Array.length rec_pos - 1 do
            Format.fprintf fmt "; %i" rec_pos.(i)
          done;
          Format.fprintf fmt " |]@]" in
        Format.fprintf fmt "mk_fix_accu %a %i" pp_rec_pos rec_pos start
    | Mk_cofix(start) -> Format.fprintf fmt "mk_cofix_accu %i" start
    | Mk_rel i -> Format.fprintf fmt "mk_rel_accu %i" i
    | Mk_var id ->
        Format.fprintf fmt "mk_var_accu (Names.Id.of_string \"%s\")" (string_of_id id)
    | Mk_proj -> Format.fprintf fmt "mk_proj_accu"
    | Mk_empty_instance -> Format.fprintf fmt "UVars.Instance.empty"
    | Is_int -> Format.fprintf fmt "is_int"
    | Is_float -> Format.fprintf fmt "is_float"
    | Is_string -> Format.fprintf fmt "is_string"
    | Is_parray -> Format.fprintf fmt "is_parray"
    | Cast_accu -> Format.fprintf fmt "cast_accu"
    | Upd_cofix -> Format.fprintf fmt "upd_cofix"
    | Force_cofix -> Format.fprintf fmt "force_cofix"
    | Mk_uint -> Format.fprintf fmt "mk_uint"
    | Mk_float -> Format.fprintf fmt "mk_float"
    | Mk_string -> Format.fprintf fmt "mk_string"
    | Mk_int -> Format.fprintf fmt "mk_int"
    | Val_to_int -> Format.fprintf fmt "val_to_int"
    | Mk_evar -> Format.fprintf fmt "mk_evar_accu"
    | MLand -> Format.fprintf fmt "(&&)"
    | MLnot -> Format.fprintf fmt "not"
    | MLland -> Format.fprintf fmt "(land)"
    | MLmagic -> Format.fprintf fmt "Obj.magic"
    | MLsubst_instance_instance -> Format.fprintf fmt "UVars.subst_instance_instance"
    | MLparray_of_array -> Format.fprintf fmt "parray_of_array"
    | Coq_primitive (op, false) ->
       Format.fprintf fmt "no_check_%s" (CPrimitives.to_string op)
    | Coq_primitive (op, true) -> Format.fprintf fmt "%s" (CPrimitives.to_string op)
    | Get_value -> Format.fprintf fmt "get_value"
    | Get_sort -> Format.fprintf fmt "get_sort"
    | Get_name -> Format.fprintf fmt "get_name"
    | Get_const -> Format.fprintf fmt "get_const"
    | Get_match -> Format.fprintf fmt "get_match"
    | Get_ind -> Format.fprintf fmt "get_ind"
    | Get_evar -> Format.fprintf fmt "get_evar"
    | Get_instance -> Format.fprintf fmt "get_instance"
    | Get_proj -> Format.fprintf fmt "get_proj"
    | Get_symbols -> Format.fprintf fmt "get_symbols"
    | Lazy -> Format.fprintf fmt "lazy"
  in
  Format.fprintf fmt "@[%a@]" pp_mllam l

let pp_array fmt t =
  let len = Array.length t in
  Format.fprintf fmt "@[[|";
  for i = 0 to len - 2 do
    Format.fprintf fmt "%a; " pp_mllam t.(i)
  done;
  if len > 0 then
    Format.fprintf fmt "%a" pp_mllam t.(len - 1);
  Format.fprintf fmt "|]@]"

let type_of_global gn c = match gn with
  | Ginternal "symbols_tbl" -> ""
  | _ -> match c with
    | MLprimitive (Lazy, _) -> " : Nativevalues.t Lazy.t"
    | MLlam ([|_|], MLprimitive (Lazy, _)) -> " : Nativevalues.t -> Nativevalues.t Lazy.t"
    | MLprimitive ((Mk_ind | Mk_const), [|_|]) -> " : UVars.Instance.t -> Nativevalues.t"
    | MLsetref (_,_) -> " : unit"
    | _ -> " : Nativevalues.t"

let pp_global fmt g =
  match g with
  | Glet (gn, c) ->
      Format.fprintf fmt "@[let %a%s = let Refl = Nativevalues.t_eq in@\n  %a@]@\n@." pp_gname gn
        (type_of_global gn c)
        pp_mllam c
  | Gopen s ->
      Format.fprintf fmt "@[open %s@]@." s
  | Gtype (ind, lar) ->
    let rec aux s arity =
      if Int.equal arity 0 then s else aux (s^" * Nativevalues.t") (arity-1) in
    let pp_const_sig fmt (tag,arity) =
      if arity > 0 then
        let sig_str = aux "of Nativevalues.t" (arity-1) in
        let cstr = string_of_construct "" ~constant:false ind tag in
        Format.fprintf fmt "  | %s %s@\n" cstr sig_str
      else
        let sig_str = if arity > 0 then aux "of Nativevalues.t" (arity-1) else "" in
        let cstr = string_of_construct "" ~constant:true ind tag in
        Format.fprintf fmt "  | %s %s@\n" cstr sig_str
    in
    let pp_const_sigs fmt lar =
      Format.fprintf fmt "  | %s of Nativevalues.t@\n" (string_of_accu_construct "" ind);
      Array.iter (pp_const_sig fmt) lar
    in
    Format.fprintf fmt "@[type ind_%s =@\n%a@]@\n@." (string_of_ind ind) pp_const_sigs lar
  | Gtblfixtype (g, params, t) ->
      Format.fprintf fmt "@[let %a %a : Nativevalues.t array = let Refl = Nativevalues.t_eq in@\n  %a@]@\n@." pp_gname g
        pp_ldecls params pp_array t
  | Gtblnorm (g, params, t) ->
      Format.fprintf fmt "@[let %a %a : Nativevalues.t array = let Refl = Nativevalues.t_eq in@\n  %a@]@\n@." pp_gname g
        pp_ldecls params pp_array t
  | Gletcase(gn,params,annot,a,accu,bs) ->
      Format.fprintf fmt "@[(* Hash = %i *)@\nlet rec %a %a : Nativevalues.t = let Refl = Nativevalues.t_eq in@\n  %a@]@\n@."
      (hash_global g)
        pp_gname gn pp_ldecls params
        pp_mllam (MLmatch(annot,a,accu,bs))
  | Gcomment s ->
      Format.fprintf fmt "@[(* %s *)@]@." s

(** Compilation of elements in environment **)
let rec compile_with_fv ?(wrap = fun t -> t) env sigma univ auxdefs l t =
  let const_prefix c = get_const_prefix env c in
  let const_lazy = get_const_lazy env in
  let mind_prefix c = get_mind_prefix env c in
  let (auxdefs,(fv_named,fv_rel),ml) = mllambda_of_lambda univ const_prefix const_lazy mind_prefix auxdefs l t in
  let ml = wrap ml in
  if List.is_empty fv_named && List.is_empty fv_rel then (auxdefs,ml)
  else apply_fv env sigma univ (fv_named,fv_rel) auxdefs ml

and apply_fv env sigma univ (fv_named,fv_rel) auxdefs ml =
  let get_rel_val (n,_) auxdefs =
    (*
    match !(lookup_rel_native_val n env) with
    | NVKnone ->
    *)
        compile_rel env sigma univ auxdefs n
(*    | NVKvalue (v,d) -> assert false *)
  in
  let get_named_val (id,_) auxdefs =
    (*
    match !(lookup_named_native_val id env) with
    | NVKnone ->
        *)
        compile_named env sigma univ auxdefs id
(*    | NVKvalue (v,d) -> assert false *)
  in
  let auxdefs = List.fold_right get_rel_val fv_rel auxdefs in
  let auxdefs = List.fold_right get_named_val fv_named auxdefs in
  let lvl = Context.Rel.length (rel_context env) in
  let fv_rel = List.map (fun (n,_) -> MLglobal (Grel (lvl-n))) fv_rel in
  let fv_named = List.map (fun (id,_) -> MLglobal (Gnamed id)) fv_named in
  let aux_name = fresh_lname Anonymous in
  auxdefs, MLlet(aux_name, ml, mkMLapp (MLlocal aux_name) (Array.of_list (fv_rel@fv_named)))

and compile_rel env sigma univ auxdefs n =
  let open Context.Rel.Declaration in
  let decl = lookup_rel n env in
  let n = List.length (rel_context env) - n in
  match decl with
  | LocalDef (_,t,_) ->
      let code = lambda_of_constr env sigma t in
      let auxdefs,code = compile_with_fv env sigma univ auxdefs None code in
      Glet(Grel n, code)::auxdefs
  | LocalAssum _ ->
      Glet(Grel n, MLprimitive (Mk_rel n, [||]))::auxdefs

and compile_named env sigma univ auxdefs id =
  let open Context.Named.Declaration in
  match lookup_named id env with
  | LocalDef (_,t,_) ->
      let code = lambda_of_constr env sigma t in
      let auxdefs,code = compile_with_fv env sigma univ auxdefs None code in
      Glet(Gnamed id, code)::auxdefs
  | LocalAssum _ ->
      Glet(Gnamed id, MLprimitive (Mk_var id, [||]))::auxdefs

let compile_constant env sigma con cb =
    let no_univs = UVars.AbstractContext.is_constant (Declareops.constant_polymorphic_context cb) in
    begin match cb.const_body with
    | Def t ->
      let code = lambda_of_constr env sigma t in
      debug_native_compiler (fun () -> Pp.str "Generated lambda code");
      let is_lazy = is_lazy_constant env cb in
      let wrap t = if is_lazy then MLprimitive (Lazy, [|t|]) else t in
      let l = Constant.label con in
      let auxdefs,code =
        if no_univs then
          compile_with_fv ~wrap env sigma None [] (Some l) code
        else
          let univ = fresh_univ () in
          let (auxdefs,code) = compile_with_fv ~wrap env sigma (Some univ) [] (Some l) code in
          (auxdefs,mkMLlam [|univ|] code)
      in
      debug_native_compiler (fun () -> Pp.str "Generated mllambda code");
      let code =
        optimize_stk (Glet(Gconstant ("", con),code)::auxdefs)
      in
      debug_native_compiler (fun () -> Pp.str "Optimized mllambda code");
      code
    | _ ->
        let i = push_symbol (SymbConst con) in
        let args =
          if no_univs then [|get_const_code i; ml_empty_instance|]
          else [|get_const_code i|]
        in
        (*
        let t = mkMLlam [|univ|] (mkMLapp (MLprimitive Mk_const)
         *)
        [Glet(Gconstant ("", con), MLprimitive (Mk_const, args))]
    end

module StringOrd = struct type t = string let compare = String.compare end
module StringSet = Set.Make(StringOrd)

let loaded_native_files = ref StringSet.empty

let is_loaded_native_file s = StringSet.mem s !loaded_native_files

let register_native_file s =
  loaded_native_files := StringSet.add s !loaded_native_files

let is_code_loaded name =
  match !name with
  | NotLinked -> false
  | Linked s ->
      if is_loaded_native_file s then true
      else (name := NotLinked; false)

let compile_mind mb mind stack =
  let u = Declareops.inductive_polymorphic_context mb in
  (** Generate data for every block *)
  let f i stack ob =
    let ind = (mind, i) in
    let gtype = Gtype(ind, ob.mind_reloc_tbl) in
    let j = push_symbol (SymbInd ind) in
    let name = Gind ("", ind) in
    let accu =
      let args =
        if UVars.AbstractContext.is_constant u then
          [|get_ind_code j; ml_empty_instance|]
        else [|get_ind_code j|]
      in
      (* FIXME: pass universes here *)
      Glet(name, MLprimitive (Mk_ind, args))
    in
    let add_proj proj_arg acc _pb =
      let tbl = ob.mind_reloc_tbl in
      (* Building info *)
      let asw = { asw_ind = ind; asw_prefix = "";
                  asw_reloc = tbl; asw_finite = true } in
      let c_uid = fresh_lname Anonymous in
      let cf_uid = fresh_lname Anonymous in
      let tag, arity = tbl.(0) in
      assert (arity > 0);
      let ci_uid = fresh_lname Anonymous in
      let cargs = Array.init arity
        (fun i -> if Int.equal i proj_arg then Some ci_uid else None)
      in
      let i = push_symbol (SymbProj (ind, proj_arg)) in
      let accu = MLprimitive (Cast_accu, [|MLlocal cf_uid|]) in
      let accu_br = MLprimitive (Mk_proj, [|get_proj_code i;accu|]) in
      let code = MLmatch(asw,MLlocal cf_uid,accu_br,[|[NonConstPattern (tag,cargs)],MLlocal ci_uid|]) in
      let code = MLlet(cf_uid, mkForceCofix "" ind (MLlocal c_uid), code) in
      let gn = Gproj ("", ind, proj_arg) in
      Glet (gn, mkMLlam [|c_uid|] code) :: acc
    in
    let projs = match mb.mind_record with
    | NotRecord | FakeRecord -> []
    | PrimRecord info ->
      let _, _, _, pbs = info.(i) in
      Array.fold_left_i add_proj [] pbs
    in
    projs @ gtype :: accu :: stack
  in
  Array.fold_left_i f stack mb.mind_packets

type code_location_update = {
  upd_info : link_info ref;
  upd_prefix : string;
}

type code_location_updates =
  code_location_update Mindmap_env.t * code_location_update Cmap_env.t

type linkable_code = global list * code_location_updates

let empty_updates = Mindmap_env.empty, Cmap_env.empty

let compile_mind_deps env prefix
    (comp_stack, (mind_updates, const_updates) as init) mind =
  let mib,nameref = lookup_mind_key mind env in
  if is_code_loaded nameref
    || Mindmap_env.mem mind mind_updates
  then init
  else
    let comp_stack =
      compile_mind mib mind comp_stack
    in
    let upd = {
      upd_info = nameref;
      upd_prefix = prefix;
    } in
    let mind_updates = Mindmap_env.add mind upd mind_updates in
    (comp_stack, (mind_updates, const_updates))

(* This function compiles all necessary dependencies of t, and generates code in
   reverse order, as well as linking information updates *)
let compile_deps env sigma prefix init t =
  let rec aux env lvl init t =
  match kind t with
  | Ind ((mind,_),_u) -> compile_mind_deps env prefix init mind
  | Const (c, _u) ->
    let c, _ = get_alias env c in
    let cb,(nameref,_) = lookup_constant_key c env in
    let (_, (_, const_updates)) = init in
    if is_code_loaded nameref
    || (Cmap_env.mem c const_updates)
    then init
    else
      let comp_stack, (mind_updates, const_updates) =
        match cb.const_body with
        | Def t ->
           aux env lvl init t
        | _ -> init
      in
      let code = compile_constant env sigma c cb in
      let upd = {
        upd_info = nameref;
        upd_prefix = prefix;
      } in
      let comp_stack = code@comp_stack in
      let const_updates = Cmap_env.add c upd const_updates in
      comp_stack, (mind_updates, const_updates)
  | Construct (((mind,_),_),_u) -> compile_mind_deps env prefix init mind
  | Proj (p,_,c) ->
    let init = compile_mind_deps env prefix init (Projection.mind p) in
    aux env lvl init c
  | Case (ci, _u, _pms, _p, _iv, _c, _ac) ->
      let mind = fst ci.ci_ind in
      let init = compile_mind_deps env prefix init mind in
      fold_constr_with_binders succ (aux env) lvl init t
  | Var id ->
    let open Context.Named.Declaration in
    begin match lookup_named id env with
      | LocalDef (_,t,_) ->
        aux env lvl init t
      | _ -> init
    end
  | Rel n when n > lvl ->
    let open Context.Rel.Declaration in
    let decl = lookup_rel n env in
    let env = env_of_rel n env in
    begin match decl with
    | LocalDef (_,t,_) ->
      aux env lvl init t
    | LocalAssum _ -> init
    end
  | _ -> fold_constr_with_binders succ (aux env) lvl init t
  in
  aux env 0 init t

let compile_constant_field env con acc cb =
    let gl = compile_constant env (empty_evars env) con cb in
    gl@acc

let compile_mind_field mp l acc mb =
  let mind = MutInd.make2 mp l in
  compile_mind mb mind acc

let warn_native_rules =
  CWarnings.create ~name:"native-rewrite-rules"
    (fun lbl -> Pp.(str "Cannot translate the following rewrite rules: " ++ Label.print lbl))

let compile_rewrite_rules _env lbl acc rrb =
  warn_native_rules lbl;
  ignore rrb; (* TODO *)
  acc

let mk_open s = Gopen s

let mk_internal_let s code =
  Glet(Ginternal s, code)

(* ML Code for conversion function *)
let mk_conv_code env sigma prefix t1 t2 =
  clear_symbols ();
  clear_global_tbl ();
  let gl, (mind_updates, const_updates) =
    let init = ([], empty_updates) in
    compile_deps env sigma prefix init t1
  in
  let gl, (mind_updates, const_updates) =
    let init = (gl, (mind_updates, const_updates)) in
    compile_deps env sigma prefix init t2
  in
  let code1 = lambda_of_constr env sigma t1 in
  let code2 = lambda_of_constr env sigma t2 in
  let (gl,code1) = compile_with_fv env sigma None gl None code1 in
  let (gl,code2) = compile_with_fv env sigma None gl None code2 in
  let t1 = mk_internal_let "t1" code1 in
  let t2 = mk_internal_let "t2" code2 in
  let g1 = MLglobal (Ginternal "t1") in
  let g2 = MLglobal (Ginternal "t2") in
  let setref1 = Glet(Ginternal "_", MLsetref("rt1",g1)) in
  let setref2 = Glet(Ginternal "_", MLsetref("rt2",g2)) in
  let gl = List.rev (setref2 :: setref1 :: t2 :: t1 :: gl) in
  let header = Glet(Ginternal "symbols_tbl",
    MLprimitive (Get_symbols,
      [|MLglobal (Ginternal "()")|])) in
  header::gl, (mind_updates, const_updates)

let mk_norm_code env sigma prefix t =
  clear_symbols ();
  clear_global_tbl ();
  let gl, (mind_updates, const_updates) =
    let init = ([], empty_updates) in
    compile_deps env sigma prefix init t
  in
  let code = lambda_of_constr env sigma t in
  let (gl,code) = compile_with_fv env sigma None gl None code in
  let t1 = mk_internal_let "t1" code in
  let g1 = MLglobal (Ginternal "t1") in
  let setref = Glet(Ginternal "_", MLsetref("rt1",g1)) in
  let gl = List.rev (setref :: t1 :: gl) in
  let header = Glet(Ginternal "symbols_tbl",
    MLprimitive (Get_symbols,
      [|MLglobal (Ginternal "()")|])) in
  header::gl, (mind_updates, const_updates)

let mk_library_header (symbols : Nativevalues.symbols) =
  let symbols = Format.sprintf "(str_decode \"%s\")" (str_encode symbols) in
  [Glet(Ginternal "symbols_tbl", MLglobal (Ginternal symbols))]

let update_location r =
  r.upd_info := Linked r.upd_prefix

let update_locations (ind_updates,const_updates) =
  Mindmap_env.iter (fun _ -> update_location) ind_updates;
  Cmap_env.iter (fun _ -> update_location) const_updates

let add_header_comment mlcode s =
  Gcomment s :: mlcode

(* vim: set filetype=ocaml foldmethod=marker: *)
