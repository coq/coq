(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Constr
open Names
open Pp
open Lazy
module NamedDecl = Context.Named.Declaration

let debug_zify = CDebug.create ~name:"zify" ()

(* The following [constr] are necessary for constructing the proof terms *)

let zify str =
  EConstr.of_constr
    (UnivGen.constr_of_monomorphic_global (Global.env ())
       (Coqlib.lib_ref ("ZifyClasses." ^ str)))

(** classes *)
let coq_InjTyp = lazy (Coqlib.lib_ref "ZifyClasses.InjTyp")

let coq_BinOp = lazy (Coqlib.lib_ref "ZifyClasses.BinOp")
let coq_UnOp = lazy (Coqlib.lib_ref "ZifyClasses.UnOp")
let coq_CstOp = lazy (Coqlib.lib_ref "ZifyClasses.CstOp")
let coq_BinRel = lazy (Coqlib.lib_ref "ZifyClasses.BinRel")
let coq_PropBinOp = lazy (Coqlib.lib_ref "ZifyClasses.PropBinOp")
let coq_PropUOp = lazy (Coqlib.lib_ref "ZifyClasses.PropUOp")
let coq_BinOpSpec = lazy (Coqlib.lib_ref "ZifyClasses.BinOpSpec")
let coq_UnOpSpec = lazy (Coqlib.lib_ref "ZifyClasses.UnOpSpec")
let coq_Saturate = lazy (Coqlib.lib_ref "ZifyClasses.Saturate")

(* morphism like lemma *)

let mkapp2 = lazy (zify "mkapp2")
let mkapp = lazy (zify "mkapp")
let eq_refl = lazy (zify "eq_refl")
let eq = lazy (zify "eq")
let mkrel = lazy (zify "mkrel")
let iff_refl = lazy (zify "iff_refl")
let eq_iff = lazy (zify "eq_iff")
let rew_iff = lazy (zify "rew_iff")
let rew_iff_rev = lazy (zify "rew_iff_rev")

(* propositional logic *)

let op_and = lazy (zify "and")
let op_and_morph = lazy (zify "and_morph")
let op_or = lazy (zify "or")
let op_or_morph = lazy (zify "or_morph")
let op_impl_morph = lazy (zify "impl_morph")
let op_iff = lazy (zify "iff")
let op_iff_morph = lazy (zify "iff_morph")
let op_not = lazy (zify "not")
let op_not_morph = lazy (zify "not_morph")
let op_True = lazy (zify "True")
let op_I = lazy (zify "I")

(** [unsafe_to_constr c] returns a [Constr.t] without considering an evar_map.
    This is useful for calling Constr.hash *)
let unsafe_to_constr = EConstr.Unsafe.to_constr

let pr_constr env evd e = Printer.pr_econstr_env env evd e

let gl_pr_constr e =
  let genv = Global.env () in
  let evd = Evd.from_env genv in
  pr_constr genv evd e

let whd = Reductionops.clos_whd_flags CClosure.all
let is_convertible env evd t1 t2 = Reductionops.(is_conv env evd t1 t2)

(** [get_type_of] performs beta reduction ;
    Is it ok for Retyping.get_type_of (Zpower_nat n q) to return (fun _ : nat => Z) q ? *)
let get_type_of env evd e =
  Tacred.cbv_beta env evd (Retyping.get_type_of env evd e)

(* arguments are dealt with in a second step *)

let rec find_option pred l =
  match l with
  | [] -> raise Not_found
  | e :: l -> ( match pred e with Some r -> r | None -> find_option pred l )

module ConstrMap = struct
  open Names.GlobRef

  type 'a t = 'a list Map.t

  let add gr e m =
    Map.update gr (function None -> Some [e] | Some l -> Some (e :: l)) m

  let empty = Map.empty

  let find evd h m =
    match Map.find (fst (EConstr.destRef evd h)) m with
    | e :: _ -> e
    | [] -> assert false

  let find_all evd h m = Map.find (fst (EConstr.destRef evd h)) m

  let fold f m acc =
    Map.fold
      (fun k l acc -> List.fold_left (fun acc e -> f k e acc) acc l)
      m acc
end

module HConstr = struct
  module M = Map.Make (struct
    type t = EConstr.t

    let compare c c' = Constr.compare (unsafe_to_constr c) (unsafe_to_constr c')
  end)

  type 'a t = 'a M.t

  let add h e m = M.add h e m
  let empty = M.empty
  let find = M.find
end

(** [get_projections_from_constant (evd,c) ]
    returns an array of constr [| a1,.. an|] such that [c] is defined as
    Definition c := mk a1 .. an with mk a constructor.
    ai is therefore either a type parameter or a projection.
 *)

let get_projections_from_constant (evd, i) =
  match EConstr.kind evd (whd (Global.env ()) evd i) with
  | App (c, a) -> Some a
  | _ ->
    raise
      (CErrors.user_err
         Pp.(
           str "The hnf of term "
           ++ pr_constr (Global.env ()) evd i
           ++ str " should be an application i.e. (c a1 ... an)"))

(**  An instance of type, say T, is registered into a hashtable, say TableT. *)

type 'a decl =
  { decl : EConstr.t
  ; (* Registered type instance *)
    deriv : 'a (* Projections of insterest *) }

module EInjT = struct
  type t =
    { isid : bool
    ; (* S = T ->  inj = fun x -> x*)
      source : EConstr.t
    ; (* S *)
      target : EConstr.t
    ; (* T *)
      (* projections *)
      inj : EConstr.t
    ; (* S -> T *)
      pred : EConstr.t
    ; (* T -> Prop *)
      cstr : EConstr.t option (* forall x, pred (inj x) *) }
end

(** [classify_op] classify injected operators and detect special cases. *)

type classify_op =
  | OpInj (* e.g. Z.of_nat ->  \x.x *)
  | OpSame (* e.g. Z.add -> Z.add *)
  | OpConv (* e.g. Pos.ge     == \x.y. Z.ge (Z.pos x) (Z.pos y)
                     \x.y. Z.pos (Pos.add x y) == \x.y. Z.add (Z.pos x) (Z.pos y)
                     Z.succ              == (\x.x + 1)
           *)
  | OpOther

(*let pp_classify_op = function
  | OpInj -> Pp.str "Identity"
  | OpSame -> Pp.str "Same"
  | OpConv -> Pp.str "Conv"
  | OpOther -> Pp.str "Other"
 *)

let name x =
  Context.make_annot (Name.mk_name (Names.Id.of_string x)) Sorts.Relevant

let mkconvert_unop i1 i2 op top =
  (* fun x => inj (op x) *)
  let op =
    EConstr.mkLambda
      ( name "x"
      , i1.EInjT.source
      , EConstr.mkApp (i2.EInjT.inj, [|EConstr.mkApp (op, [|EConstr.mkRel 1|])|])
      )
  in
  (* fun x => top (inj x) *)
  let top =
    EConstr.mkLambda
      ( name "x"
      , i1.EInjT.source
      , EConstr.mkApp
          (top, [|EConstr.mkApp (i1.EInjT.inj, [|EConstr.mkRel 1|])|]) )
  in
  (op, top)

let mkconvert_binop i1 i2 i3 op top =
  (* fun x y => inj (op x y) *)
  let op =
    EConstr.mkLambda
      ( name "x"
      , i1.EInjT.source
      , EConstr.mkLambda
          ( name "y"
          , i1.EInjT.source
          , EConstr.mkApp
              ( i3.EInjT.inj
              , [|EConstr.mkApp (op, [|EConstr.mkRel 2; EConstr.mkRel 1|])|] )
          ) )
  in
  (* fun x y => top (inj x) (inj y) *)
  let top =
    EConstr.mkLambda
      ( name "x"
      , i1.EInjT.source
      , EConstr.mkLambda
          ( name "y"
          , i2.EInjT.source
          , EConstr.mkApp
              ( top
              , [| EConstr.mkApp (i1.EInjT.inj, [|EConstr.mkRel 2|])
                 ; EConstr.mkApp (i2.EInjT.inj, [|EConstr.mkRel 1|]) |] ) ) )
  in
  (op, top)

let mkconvert_rel i r tr =
  let tr =
    EConstr.mkLambda
      ( name "x"
      , i.EInjT.source
      , EConstr.mkLambda
          ( name "y"
          , i.EInjT.source
          , EConstr.mkApp
              ( tr
              , [| EConstr.mkApp (i.EInjT.inj, [|EConstr.mkRel 2|])
                 ; EConstr.mkApp (i.EInjT.inj, [|EConstr.mkRel 1|]) |] ) ) )
  in
  (r, tr)

(** [classify_op mkconvert op top] takes the injection [inj] for the origin operator [op]
    and the destination operator [top] -- both [op] and [top] are closed terms *)
let classify_op mkconvert inj op top =
  let env = Global.env () in
  let evd = Evd.from_env env in
  if is_convertible env evd inj op then OpInj
  else if EConstr.eq_constr evd op top then OpSame
  else
    let op, top = mkconvert op top in
    if is_convertible env evd op top then OpConv else OpOther

(*let classify_op mkconvert tysrc op top =
  let res = classify_op mkconvert tysrc op top in
  Feedback.msg_debug
    Pp.(
      str "classify_op:" ++ gl_pr_constr op ++ str " " ++ gl_pr_constr top
      ++ str "  " ++ pp_classify_op res ++ fnl ());
  res
 *)
module EBinOpT = struct
  type t =
    { (* Op : source1 -> source2 -> source3 *)
      source1 : EConstr.t
    ; source2 : EConstr.t
    ; source3 : EConstr.t
    ; target1 : EConstr.t
    ; target2 : EConstr.t
    ; target3 : EConstr.t
    ; inj1 : EInjT.t (* InjTyp source1 target1 *)
    ; inj2 : EInjT.t (* InjTyp source2 target2 *)
    ; inj3 : EInjT.t (* InjTyp source3 target3 *)
    ; bop : EConstr.t (* BOP *)
    ; tbop : EConstr.t (* TBOP *)
    ; tbopinj : EConstr.t (* TBOpInj *)
    ; classify_binop : classify_op }
end

module ECstOpT = struct
  type t =
    { source : EConstr.t
    ; target : EConstr.t
    ; inj : EInjT.t
    ; cst : EConstr.t
    ; cstinj : EConstr.t
    ; is_construct : bool }
end

module EUnOpT = struct
  type t =
    { source1 : EConstr.t
    ; source2 : EConstr.t
    ; target1 : EConstr.t
    ; target2 : EConstr.t
    ; uop : EConstr.t
    ; inj1_t : EInjT.t
    ; inj2_t : EInjT.t
    ; tuop : EConstr.t
    ; tuopinj : EConstr.t
    ; classify_unop : classify_op
    ; is_construct : bool }
end

module EBinRelT = struct
  type t =
    { source : EConstr.t
    ; target : EConstr.t
    ; inj : EInjT.t
    ; brel : EConstr.t
    ; tbrel : EConstr.t
    ; brelinj : EConstr.t
    ; classify_rel : classify_op }
end

module EPropBinOpT = struct
  type t = {op : EConstr.t; op_iff : EConstr.t}
end

module EPropUnOpT = struct
  type t = {op : EConstr.t; op_iff : EConstr.t}
end

module ESatT = struct
  type t = {parg1 : EConstr.t; parg2 : EConstr.t; satOK : EConstr.t}
end

module ESpecT = struct
  type t = {spec : EConstr.t}
end

(* Different type of declarations *)
type decl_kind =
  | PropOp of EPropBinOpT.t decl
  | PropUnOp of EPropUnOpT.t decl
  | InjTyp of EInjT.t decl
  | BinRel of EBinRelT.t decl
  | BinOp of EBinOpT.t decl
  | UnOp of EUnOpT.t decl
  | CstOp of ECstOpT.t decl
  | Saturate of ESatT.t decl
  | UnOpSpec of ESpecT.t decl
  | BinOpSpec of ESpecT.t decl

type term_kind = Application of EConstr.constr | OtherTerm of EConstr.constr

module type Elt = sig
  type elt

  (** name *)
  val name : string

  val gref : GlobRef.t Lazy.t
  val table : (term_kind * decl_kind) ConstrMap.t ref
  val cast : elt decl -> decl_kind
  val dest : decl_kind -> elt decl option

  (** [get_key] is the type-index used as key for the instance *)
  val get_key : int

  (** [mk_elt evd i [a0,..,an]  returns the element of the table
        built from the type-instance i and the arguments (type indexes and projections)
        of the type-class constructor. *)
  val mk_elt : Evd.evar_map -> EConstr.t -> EConstr.t array -> elt

  (*  val arity : int*)
end

let table = Summary.ref ~name:"zify_table" ConstrMap.empty
let saturate = Summary.ref ~name:"zify_saturate" ConstrMap.empty
let specs = Summary.ref ~name:"zify_specs" ConstrMap.empty
let table_cache = ref ConstrMap.empty
let saturate_cache = ref ConstrMap.empty
let specs_cache = ref ConstrMap.empty

(** Each type-class gives rise to a different table.
    They only differ on how projections are extracted.  *)

module EInj = struct
  open EInjT

  type elt = EInjT.t

  let name = "EInj"
  let gref = coq_InjTyp
  let table = table
  let cast x = InjTyp x
  let dest = function InjTyp x -> Some x | _ -> None

  let is_cstr_true evd c =
    match EConstr.kind evd c with
    | Lambda (_, _, c) -> EConstr.eq_constr_nounivs evd c (Lazy.force op_True)
    | _ -> false

  let mk_elt evd i (a : EConstr.t array) =
    let isid = EConstr.eq_constr_nounivs evd a.(0) a.(1) in
    { isid
    ; source = a.(0)
    ; target = a.(1)
    ; inj = a.(2)
    ; pred = a.(3)
    ; cstr = (if is_cstr_true evd a.(3) then None else Some a.(4)) }

  let get_key = 0
end

let get_inj evd c =
  match get_projections_from_constant (evd, c) with
  | None ->
    let env = Global.env () in
    let t = string_of_ppcmds (pr_constr env evd c) in
    failwith ("Cannot register term " ^ t)
  | Some a -> EInj.mk_elt evd c a

let rec decomp_type evd ty =
  match EConstr.kind_of_type evd ty with
  | EConstr.ProdType (_, t1, rst) -> t1 :: decomp_type evd rst
  | _ -> [ty]

let pp_type env evd l =
  Pp.prlist_with_sep (fun _ -> Pp.str " -> ") (pr_constr env evd) l

let check_typ evd expty op =
  let env = Global.env () in
  let ty = Retyping.get_type_of env evd op in
  let ty = decomp_type evd ty in
  if List.for_all2 (EConstr.eq_constr_nounivs evd) ty expty then ()
  else
    raise
      (CErrors.user_err
         Pp.(
           str ": Cannot register operator "
           ++ pr_constr env evd op ++ str ". It has type " ++ pp_type env evd ty
           ++ str " instead of expected type "
           ++ pp_type env evd expty))

module EBinOp = struct
  type elt = EBinOpT.t

  open EBinOpT

  let name = "BinOp"
  let gref = coq_BinOp
  let table = table

  let mk_elt evd i a =
    let i1 = get_inj evd a.(7) in
    let i2 = get_inj evd a.(8) in
    let i3 = get_inj evd a.(9) in
    let bop = a.(6) in
    let tbop = a.(10) in
    check_typ evd EInjT.[i1.source; i2.source; i3.source] bop;
    { source1 = a.(0)
    ; source2 = a.(1)
    ; source3 = a.(2)
    ; target1 = a.(3)
    ; target2 = a.(4)
    ; target3 = a.(5)
    ; inj1 = i1
    ; inj2 = i2
    ; inj3 = i3
    ; bop
    ; tbop
    ; tbopinj = a.(11)
    ; classify_binop =
        classify_op (mkconvert_binop i1 i2 i3) i3.EInjT.inj a.(6) tbop }

  let get_key = 6
  let cast x = BinOp x
  let dest = function BinOp x -> Some x | _ -> None
end

(*let debug_term msg c =
  let genv = Global.env () in
  Feedback.msg_debug
    Pp.(str msg ++ str " " ++ pr_constr genv (Evd.from_env genv) c);
  c
 *)
module ECstOp = struct
  type elt = ECstOpT.t

  open ECstOpT

  let name = "CstOp"
  let gref = coq_CstOp
  let table = table
  let cast x = CstOp x
  let dest = function CstOp x -> Some x | _ -> None

  let isConstruct evd c =
    match EConstr.kind evd c with
    | Construct _ | Int _ | Float _ -> true
    | _ -> false

  let mk_elt evd i a =
    { source = a.(0)
    ; target = a.(1)
    ; inj = get_inj evd a.(3)
    ; cst = a.(4)
    ; cstinj = a.(5)
    ; is_construct = isConstruct evd a.(2) }

  let get_key = 2
end

module EUnOp = struct
  type elt = EUnOpT.t

  open EUnOpT

  let name = "UnOp"
  let gref = coq_UnOp
  let table = table
  let cast x = UnOp x
  let dest = function UnOp x -> Some x | _ -> None

  let mk_elt evd i a =
    let i1 = get_inj evd a.(5) in
    let i2 = get_inj evd a.(6) in
    let uop = a.(4) in
    check_typ evd EInjT.[i1.source; i2.source] uop;
    let tuop = a.(7) in
    { source1 = a.(0)
    ; source2 = a.(1)
    ; target1 = a.(2)
    ; target2 = a.(3)
    ; uop
    ; inj1_t = i1
    ; inj2_t = i2
    ; tuop
    ; tuopinj = a.(8)
    ; is_construct = EConstr.isConstruct evd uop
    ; classify_unop = classify_op (mkconvert_unop i1 i2) i2.EInjT.inj uop tuop
    }

  let get_key = 4
end

module EBinRel = struct
  type elt = EBinRelT.t

  open EBinRelT

  let name = "BinRel"
  let gref = coq_BinRel
  let table = table
  let cast x = BinRel x
  let dest = function BinRel x -> Some x | _ -> None

  let mk_elt evd i a =
    let i = get_inj evd a.(3) in
    let brel = a.(2) in
    let tbrel = a.(4) in
    check_typ evd EInjT.[i.source; i.source; EConstr.mkProp] brel;
    { source = a.(0)
    ; target = a.(1)
    ; inj = get_inj evd a.(3)
    ; brel
    ; tbrel
    ; brelinj = a.(5)
    ; classify_rel = classify_op (mkconvert_rel i) i.EInjT.inj brel tbrel }

  let get_key = 2
end

module EPropBinOp = struct
  type elt = EPropBinOpT.t

  open EPropBinOpT

  let name = "PropBinOp"
  let gref = coq_PropBinOp
  let table = table
  let cast x = PropOp x
  let dest = function PropOp x -> Some x | _ -> None
  let mk_elt evd i a = {op = a.(0); op_iff = a.(1)}
  let get_key = 0
end

module EPropUnOp = struct
  type elt = EPropUnOpT.t

  open EPropUnOpT

  let name = "PropUOp"
  let gref = coq_PropUOp
  let table = table
  let cast x = PropUnOp x
  let dest = function PropUnOp x -> Some x | _ -> None
  let mk_elt evd i a = {op = a.(0); op_iff = a.(1)}
  let get_key = 0
end

let constr_of_term_kind = function Application c -> c | OtherTerm c -> c

module type S = sig
  val register : Libnames.qualid -> unit
  val print : unit -> unit
end

module MakeTable (E : Elt) = struct
  (** Given a term [c] and its arguments ai,
        we construct a HConstr.t table that is
        indexed by ai for i = E.get_key.
        The elements of the table are built using E.mk_elt c [|a0,..,an|]
     *)

  let make_elt (evd, i) =
    match get_projections_from_constant (evd, i) with
    | None ->
      let env = Global.env () in
      let t = string_of_ppcmds (pr_constr env evd i) in
      failwith ("Cannot register term " ^ t)
    | Some a -> E.mk_elt evd i a

  let safe_ref evd c =
    try
      fst (EConstr.destRef evd c)
    with DestKO -> CErrors.user_err Pp.(str "Add Zify "++str E.name ++ str ": the term "++
                                          gl_pr_constr c ++ str " should be a global reference")

  let register_hint evd t elt =
    match EConstr.kind evd t with
    | App (c, _) ->
       let gr = safe_ref evd c in
       E.table := ConstrMap.add gr (Application t, E.cast elt) !E.table
    | _ ->
       let gr = safe_ref evd t in
       E.table := ConstrMap.add gr (OtherTerm t, E.cast elt) !E.table

  let register_constr env evd c =
    let c = EConstr.of_constr c in
    let t = get_type_of env evd c in
    match EConstr.kind evd t with
    | App (intyp, args) when EConstr.isRefX evd (Lazy.force E.gref) intyp ->
      let styp = args.(E.get_key) in
      let elt = {decl = c; deriv = make_elt (evd, c)} in
      register_hint evd styp elt
    | _ ->
      let env = Global.env () in
      raise
        (CErrors.user_err
           Pp.(
             str "Cannot register " ++ pr_constr env evd c
             ++ str ". It has type " ++ pr_constr env evd t
             ++ str " instead of type "
             ++ Printer.pr_global (Lazy.force E.gref)
             ++ str " X1 ... Xn"))

  let register_obj : Constr.constr -> Libobject.obj =
    let cache_constr c =
      let env = Global.env () in
      let evd = Evd.from_env env in
      register_constr env evd c
    in
    let subst_constr (subst, c) = Mod_subst.subst_mps subst c in
    Libobject.declare_object
    @@ Libobject.superglobal_object_nodischarge
         ("register-zify-" ^ E.name)
         ~cache:cache_constr ~subst:(Some subst_constr)

  (** [register c] is called from the VERNACULAR ADD [name] reference(t).
       The term [c] is interpreted and
       registered as a [superglobal_object_nodischarge].
       TODO: pre-compute [get_type_of] - [cache_constr] is using another environment.
     *)
  let register c =
    try
      let c = UnivGen.constr_of_monomorphic_global (Global.env ()) (Nametab.locate c) in
      let _ = Lib.add_leaf (register_obj c) in
      ()
    with Not_found ->
      raise
        (CErrors.user_err Pp.(Libnames.pr_qualid c ++ str " does not exist."))

  let pp_keys () =
    let env = Global.env () in
    let evd = Evd.from_env env in
    ConstrMap.fold
      (fun _ (k, d) acc ->
        match E.dest d with
        | None -> acc
        | Some _ ->
          Pp.(pr_constr env evd (constr_of_term_kind k) ++ str " " ++ acc))
      !E.table (Pp.str "")

  let print () = Feedback.msg_info (pp_keys ())
end

module InjTable = MakeTable (EInj)

module ESat = struct
  type elt = ESatT.t

  open ESatT

  let name = "Saturate"
  let gref = coq_Saturate
  let table = saturate
  let cast x = Saturate x
  let dest = function Saturate x -> Some x | _ -> None
  let mk_elt evd i a = {parg1 = a.(2); parg2 = a.(3); satOK = a.(5)}
  let get_key = 1
end

module EUnopSpec = struct
  open ESpecT

  type elt = ESpecT.t

  let name = "UnopSpec"
  let gref = coq_UnOpSpec
  let table = specs
  let cast x = UnOpSpec x
  let dest = function UnOpSpec x -> Some x | _ -> None
  let mk_elt evd i a = {spec = a.(4)}
  let get_key = 2
end

module EBinOpSpec = struct
  open ESpecT

  type elt = ESpecT.t

  let name = "BinOpSpec"
  let gref = coq_BinOpSpec
  let table = specs
  let cast x = BinOpSpec x
  let dest = function BinOpSpec x -> Some x | _ -> None
  let mk_elt evd i a = {spec = a.(5)}
  let get_key = 3
end

module BinOp = MakeTable (EBinOp)
module UnOp = MakeTable (EUnOp)
module CstOp = MakeTable (ECstOp)
module BinRel = MakeTable (EBinRel)
module PropBinOp = MakeTable (EPropBinOp)
module PropUnOp = MakeTable (EPropUnOp)
module Saturate = MakeTable (ESat)
module UnOpSpec = MakeTable (EUnopSpec)
module BinOpSpec = MakeTable (EBinOpSpec)

let init_cache () =
  table_cache := !table;
  saturate_cache := !saturate;
  specs_cache := !specs

open EInjT

(** Get constr of lemma and projections in ZifyClasses. *)

(** Module [CstrTable] records terms  [x] injected into [inj x]
    together with the corresponding type constraint.
    The terms are stored by side-effect during the traversal
    of the goal. It must therefore be cleared before calling
    the main tactic.
 *)

module CstrTable = struct
  module HConstr = Hashtbl.Make (struct
    type t = EConstr.t

    let hash c = Constr.hash (unsafe_to_constr c)
    let equal c c' = Constr.equal (unsafe_to_constr c) (unsafe_to_constr c')
  end)

  let table : EConstr.t HConstr.t = HConstr.create 10
  let register evd t (i : EConstr.t) = HConstr.add table t i

  let get () =
    let l = HConstr.fold (fun k i acc -> (k, i) :: acc) table [] in
    HConstr.clear table; l

  (** [gen_cstr table] asserts (cstr k) for each element of the table (k,cstr).
        NB: the constraint is only asserted if it does not already exist in the context.
     *)
  let gen_cstr table =
    Proofview.Goal.enter (fun gl ->
        let evd = Tacmach.project gl in
        (* Build the table of existing hypotheses *)
        let has_hyp =
          let hyps_table = HConstr.create 20 in
          List.iter
            (fun (_, (t : EConstr.types)) -> HConstr.add hyps_table t ())
            (Tacmach.pf_hyps_types gl);
          fun c ->
            let m = HConstr.mem hyps_table c in
            if not m then HConstr.add hyps_table c ();
            m
        in
        (* Add the constraint (cstr k) if it is not already present *)
        let gen k cstr =
          Proofview.Goal.enter (fun gl ->
              let env = Tacmach.pf_env gl in
              let term = EConstr.mkApp (cstr, [|k|]) in
              let types = get_type_of env evd term in
              if has_hyp types then Tacticals.tclIDTAC
              else
                let n =
                  Tactics.fresh_id_in_env Id.Set.empty
                    (Names.Id.of_string "cstr")
                    env
                in
                Tactics.pose_proof (Names.Name n) term)
        in
        List.fold_left
          (fun acc (k, i) -> Tacticals.tclTHEN (gen k i) acc)
          Tacticals.tclIDTAC table)
end

type prf =
  | Term (* source is built from constructors.
             target = compute(inj source)
             inj source ==  target *)
  | Same (* target = source
             inj source == inj target *)
  | Conv of EConstr.t (* inj source == target *)
  | Prf of EConstr.t * EConstr.t

(** [eq_proof typ source target] returns (target = target : source = target) *)
let eq_proof typ source target =
  EConstr.mkCast
    ( EConstr.mkApp (force eq_refl, [|typ; target|])
    , DEFAULTcast
    , EConstr.mkApp (force eq, [|typ; source; target|]) )

let interp_prf evd inj source prf =
  let inj_source =
    if inj.EInjT.isid then source else EConstr.mkApp (inj.EInjT.inj, [|source|])
  in
  match prf with
  | Term ->
    let target = Tacred.compute (Global.env ()) evd inj_source in
    (target, EConstr.mkApp (force eq_refl, [|inj.target; target|]))
  | Same ->
    (inj_source, EConstr.mkApp (force eq_refl, [|inj.target; inj_source|]))
  | Conv trm -> (trm, eq_proof inj.target inj_source trm)
  | Prf (target, prf) -> (target, prf)

let pp_prf prf =
  match prf with
  | Term -> Pp.str "Term"
  | Same -> Pp.str "Same"
  | Conv t -> Pp.(str "Conv " ++ gl_pr_constr t)
  | Prf (_, _) -> Pp.str "Prf "

let interp_prf evd inj source prf =
  let t, prf' = interp_prf evd inj source prf in
  debug_zify (fun () ->
      Pp.(
        str "interp_prf " ++ gl_pr_constr inj.EInjT.inj ++ str " "
        ++ gl_pr_constr source ++ str " = " ++ gl_pr_constr t ++ str " by "
        ++ gl_pr_constr prf' ++ str " from " ++ pp_prf prf ++ fnl ()));
  (t, prf')

let mkvar evd inj e =
  (match inj.cstr with None -> () | Some ctr -> CstrTable.register evd e ctr);
  Same

let pp_prf evd inj src prf =
  let t, prf' = interp_prf evd inj src prf in
  Pp.(
    gl_pr_constr inj.EInjT.inj ++ str " " ++ gl_pr_constr src ++ str " = "
    ++ gl_pr_constr t ++ str " by "
    ++
    match prf with
    | Term -> Pp.str "Term"
    | Same -> Pp.str "Same"
    | Conv t -> Pp.str "Conv"
    | Prf (_, p) -> Pp.str "Prf " ++ gl_pr_constr p)

let conv_of_term evd op isid arg =
  Tacred.compute (Global.env ()) evd
    (if isid then arg else EConstr.mkApp (op, [|arg|]))

let app_unop evd src unop arg prf =
  let cunop = unop.EUnOpT.classify_unop in
  let default a' prf' =
    let target = EConstr.mkApp (unop.EUnOpT.tuop, [|a'|]) in
    EUnOpT.(
      Prf
        ( target
        , EConstr.mkApp
            ( force mkapp
            , [| unop.source1
               ; unop.source2
               ; unop.target1
               ; unop.target2
               ; unop.uop
               ; unop.inj1_t.EInjT.inj
               ; unop.inj2_t.EInjT.inj
               ; unop.tuop
               ; unop.tuopinj
               ; arg
               ; a'
               ; prf' |] ) ))
  in
  match prf with
  | Term -> (
    if unop.EUnOpT.is_construct then Term (* Keep rebuilding *)
    else
      match cunop with
      | OpInj -> Conv (conv_of_term evd unop.EUnOpT.uop false arg)
      | OpSame -> Same
      | _ ->
        let a', prf = interp_prf evd unop.EUnOpT.inj1_t arg prf in
        default a' prf )
  | Same -> (
    match cunop with
    | OpSame -> Same
    | OpInj -> Same
    | OpConv ->
      Conv
        (EConstr.mkApp
           ( unop.EUnOpT.tuop
           , [|EConstr.mkApp (unop.EUnOpT.inj1_t.EInjT.inj, [|arg|])|] ))
    | OpOther ->
      let a', prf' = interp_prf evd unop.EUnOpT.inj1_t arg prf in
      default a' prf' )
  | Conv a' -> (
    match cunop with
    | OpSame | OpConv -> Conv (EConstr.mkApp (unop.EUnOpT.tuop, [|a'|]))
    | OpInj -> Conv a'
    | _ ->
      let a', prf = interp_prf evd unop.EUnOpT.inj1_t arg prf in
      default a' prf )
  | Prf (a', prf') -> default a' prf'

let app_unop evd src unop arg prf =
  let res = app_unop evd src unop arg prf in
  debug_zify (fun () ->
      Pp.(
        str "\napp_unop "
        ++ pp_prf evd unop.EUnOpT.inj1_t arg prf
        ++ str " => "
        ++ pp_prf evd unop.EUnOpT.inj2_t src res));
  res

let app_binop evd src binop arg1 prf1 arg2 prf2 =
  EBinOpT.(
    let mkApp a1 a2 = EConstr.mkApp (binop.tbop, [|a1; a2|]) in
    let to_conv inj arg = function
      | Term -> conv_of_term evd inj.EInjT.inj inj.EInjT.isid arg
      | Same ->
        if inj.EInjT.isid then arg else EConstr.mkApp (inj.EInjT.inj, [|arg|])
      | Conv t -> t
      | Prf _ -> failwith "Prf is not convertible"
    in
    let default a1 prf1 a2 prf2 =
      let res = mkApp a1 a2 in
      let prf =
        EBinOpT.(
          EConstr.mkApp
            ( force mkapp2
            , [| binop.source1
               ; binop.source2
               ; binop.source3
               ; binop.target1
               ; binop.target2
               ; binop.target3
               ; binop.bop
               ; binop.inj1.EInjT.inj
               ; binop.inj2.EInjT.inj
               ; binop.inj3.EInjT.inj
               ; binop.tbop
               ; binop.tbopinj
               ; arg1
               ; a1
               ; prf1
               ; arg2
               ; a2
               ; prf2 |] ))
      in
      Prf (res, prf)
    in
    match (binop.EBinOpT.classify_binop, prf1, prf2) with
    | OpSame, Same, Same -> Same
    | OpSame, Term, Same | OpSame, Same, Term -> Same
    | OpSame, (Term | Same | Conv _), (Term | Same | Conv _) ->
      let t1 = to_conv binop.EBinOpT.inj1 arg1 prf1 in
      let t2 = to_conv binop.EBinOpT.inj1 arg2 prf2 in
      Conv (mkApp t1 t2)
    | _, _, _ ->
      let a1, prf1 = interp_prf evd binop.inj1 arg1 prf1 in
      let a2, prf2 = interp_prf evd binop.inj2 arg2 prf2 in
      default a1 prf1 a2 prf2)

type typed_constr = {constr : EConstr.t; typ : EConstr.t; inj : EInjT.t}

let get_injection env evd t =
  try
    match snd (ConstrMap.find evd t !table_cache) with
    | InjTyp i -> i
    | _ -> raise Not_found
  with DestKO -> raise Not_found

(* [arrow] is the term (fun (x:Prop) (y : Prop) => x -> y) *)
let arrow =
  let name x =
    Context.make_annot (Name.mk_name (Names.Id.of_string x)) Sorts.Relevant
  in
  EConstr.mkLambda
    ( name "x"
    , EConstr.mkProp
    , EConstr.mkLambda
        ( name "y"
        , EConstr.mkProp
        , EConstr.mkProd
            ( Context.make_annot Names.Anonymous Sorts.Relevant
            , EConstr.mkRel 2
            , EConstr.mkRel 2 ) ) )

let is_prop env sigma term =
  let sort = Retyping.get_sort_of env sigma term in
  Sorts.is_prop sort

let is_arrow env evd a p1 p2 =
  is_prop env evd p1
  && is_prop
       (EConstr.push_rel (Context.Rel.Declaration.LocalAssum (a, p1)) env)
       evd p2
  && (a.Context.binder_name = Names.Anonymous || EConstr.Vars.noccurn evd 1 p2)

(** [get_operator env evd e] expresses [e] as an application (c a)
     where c is the head symbol and [a] is the array of arguments.
     The function also transforms (x -> y) as (arrow x y) *)
let get_operator barrow env evd e =
  let e' = EConstr.whd_evar evd e in
  match EConstr.kind evd e' with
  | Prod (a, p1, p2) ->
    if barrow && is_arrow env evd a p1 p2 then (arrow, [|p1; p2|], false)
    else raise Not_found
  | App (c, a) -> (
    let c' = EConstr.whd_evar evd c in
    match EConstr.kind evd c' with
    | Construct _ (* e.g. Z0 , Z.pos *) | Const _ (* e.g. Z.max *) | Proj _
     |Lambda _ (* e.g projections *) | Ind _ (* e.g. eq *) ->
      (c', a, false)
    | _ -> raise Not_found )
  | Const _ -> (e', [||], false)
  | Construct _ -> (e', [||], true)
  | Int _ | Float _ -> (e', [||], true)
  | _ -> raise Not_found

let decompose_app env evd e =
  match EConstr.kind evd e with
  | Prod (a, p1, p2) when is_arrow env evd a p1 p2 -> (arrow, [|p1; p2|])
  | App (c, a) -> (c, a)
  | _ -> (EConstr.whd_evar evd e, [||])

type 'op propop = {op : 'op; op_constr : EConstr.t; op_iff : EConstr.t}

let mk_propop op c1 c2 = {op; op_constr = c1; op_iff = c2}

type prop_binop = AND | OR | IFF | IMPL
type prop_unop = NOT

type prop_op =
  | BINOP of prop_binop propop * EConstr.t * EConstr.t
  | UNOP of prop_unop propop * EConstr.t
  | OTHEROP of EConstr.t * EConstr.t array

let classify_prop env evd e =
  match EConstr.kind evd e with
  | Prod (a, p1, p2) when is_arrow env evd a p1 p2 ->
    BINOP (mk_propop IMPL arrow (force op_impl_morph), p1, p2)
  | App (c, a) -> (
    match Array.length a with
    | 1 ->
      if EConstr.eq_constr_nounivs evd (force op_not) c then
        UNOP (mk_propop NOT c (force op_not_morph), a.(0))
      else OTHEROP (c, a)
    | 2 ->
      if EConstr.eq_constr_nounivs evd (force op_and) c then
        BINOP (mk_propop AND c (force op_and_morph), a.(0), a.(1))
      else if EConstr.eq_constr_nounivs evd (force op_or) c then
        BINOP (mk_propop OR c (force op_or_morph), a.(0), a.(1))
      else if EConstr.eq_constr_nounivs evd (force op_iff) c then
        BINOP (mk_propop IFF c (force op_iff_morph), a.(0), a.(1))
      else OTHEROP (c, a)
    | _ -> OTHEROP (c, a) )
  | _ -> OTHEROP (e, [||])

(** [match_operator env evd hd arg (t,d)]
     - hd is head operator of t
     - If t = OtherTerm _, then t = hd
     - If t = Application _, then
       we extract the relevant number of arguments from arg
       and check for convertibility *)
let match_operator env evd hd args (t, d) =
  let decomp t i =
    let n = Array.length args in
    let t' = EConstr.mkApp (hd, Array.sub args 0 (n - i)) in
    if is_convertible env evd t' t then Some (d, t) else None
  in
  match t with
  | OtherTerm t -> Some (d, t)
  | Application t -> (
    match d with
    | CstOp _ -> decomp t 0
    | UnOp _ -> decomp t 1
    | BinOp _ -> decomp t 2
    | BinRel _ -> decomp t 2
    | PropOp _ -> decomp t 2
    | PropUnOp _ -> decomp t 1
    | _ -> None )

let pp_trans_expr env evd e res =
  let {deriv = inj} = get_injection env evd e.typ in
  debug_zify (fun () -> Pp.(str "\ntrans_expr " ++ pp_prf evd inj e.constr res));
  res

let declared_term env evd hd args =
  let match_operator (t, d) =
    let decomp t i =
      let n = Array.length args in
      let t' = EConstr.mkApp (hd, Array.sub args 0 (n - i)) in
      if is_convertible env evd t' t then Some (t, Array.sub args (n - i) i)
      else None
    in
    match t with
    | OtherTerm t -> ( match d with InjTyp _ -> None | _ -> Some (t, args) )
    | Application t -> (
      match d with
      | CstOp _ -> decomp t 0
      | UnOp _ -> decomp t 1
      | BinOp _ -> decomp t 2
      | BinRel _ -> decomp t 2
      | PropOp _ -> decomp t 2
      | PropUnOp _ -> decomp t 1
      | _ -> None )
  in
  find_option match_operator (ConstrMap.find_all evd hd !table)

let rec trans_expr env evd e =
  let inj = e.inj in
  let e = e.constr in
  try
    let c, a, is_constant = get_operator false env evd e in
    if is_constant then Term
    else
      let k, t =
        find_option
          (match_operator env evd c a)
          (ConstrMap.find_all evd c !table_cache)
      in
      let n = Array.length a in
      match k with
      | CstOp {deriv = c'} ->
        ECstOpT.(if c'.is_construct then Term else Prf (c'.cst, c'.cstinj))
      | UnOp {deriv = unop} ->
        let prf =
          trans_expr env evd
            { constr = a.(n - 1)
            ; typ = unop.EUnOpT.source1
            ; inj = unop.EUnOpT.inj1_t }
        in
        app_unop evd e unop a.(n - 1) prf
      | BinOp {deriv = binop} ->
        let prf1 =
          trans_expr env evd
            { constr = a.(n - 2)
            ; typ = binop.EBinOpT.source1
            ; inj = binop.EBinOpT.inj1 }
        in
        let prf2 =
          trans_expr env evd
            { constr = a.(n - 1)
            ; typ = binop.EBinOpT.source2
            ; inj = binop.EBinOpT.inj2 }
        in
        app_binop evd e binop a.(n - 2) prf1 a.(n - 1) prf2
      | d -> mkvar evd inj e
  with Not_found | DestKO ->    mkvar evd inj e

let trans_expr env evd e =
  try pp_trans_expr env evd e (trans_expr env evd e)
  with Not_found ->
    raise
      (CErrors.user_err
         ( Pp.str "Missing injection for type "
         ++ Printer.pr_leconstr_env env evd e.typ ))

type prfp =
  | TProof of EConstr.t * EConstr.t  (** Proof of tranformed proposition *)
  | CProof of EConstr.t  (** Transformed proposition is convertible *)
  | IProof  (** Transformed proposition is identical *)

let pp_prfp = function
  | TProof (t, prf) ->
    Pp.str "TProof " ++ gl_pr_constr t ++ Pp.str " by " ++ gl_pr_constr prf
  | CProof t -> Pp.str "CProof " ++ gl_pr_constr t
  | IProof -> Pp.str "IProof"

let trans_binrel evd src rop a1 prf1 a2 prf2 =
  EBinRelT.(
    match (rop.classify_rel, prf1, prf2) with
    | OpSame, Same, Same -> IProof
    | (OpSame | OpConv), Conv t1, Conv t2 ->
      CProof (EConstr.mkApp (rop.tbrel, [|t1; t2|]))
    | (OpSame | OpConv), (Same | Term | Conv _), (Same | Term | Conv _) ->
      let a1', _ = interp_prf evd rop.inj a1 prf1 in
      let a2', _ = interp_prf evd rop.inj a2 prf2 in
      CProof (EConstr.mkApp (rop.tbrel, [|a1'; a2'|]))
    | _, _, _ ->
      let a1', prf1 = interp_prf evd rop.inj a1 prf1 in
      let a2', prf2 = interp_prf evd rop.inj a2 prf2 in
      TProof
        ( EConstr.mkApp (rop.EBinRelT.tbrel, [|a1'; a2'|])
        , EConstr.mkApp
            ( force mkrel
            , [| rop.source
               ; rop.target
               ; rop.brel
               ; rop.EBinRelT.inj.EInjT.inj
               ; rop.EBinRelT.tbrel
               ; rop.EBinRelT.brelinj
               ; a1
               ; a1'
               ; prf1
               ; a2
               ; a2'
               ; prf2 |] ) ))

let trans_binrel evd src rop a1 prf1 a2 prf2 =
  let res = trans_binrel evd src rop a1 prf1 a2 prf2 in
  debug_zify (fun () -> Pp.(str "\ntrans_binrel " ++ pp_prfp res));
  res

let mkprf t p =
  EConstr.(
    match p with
    | IProof -> (t, mkApp (force iff_refl, [|t|]))
    | CProof t' -> (t', mkApp (force eq_iff, [|t; t'; eq_proof mkProp t t'|]))
    | TProof (t', p) -> (t', p))

let mkprf t p =
  let t', p = mkprf t p in
  debug_zify (fun () ->
      Pp.(
        str "mkprf " ++ gl_pr_constr t ++ str " <-> " ++ gl_pr_constr t'
        ++ str " by " ++ gl_pr_constr p));
  (t', p)

let trans_bin_prop op_constr op_iff t1 p1 t2 p2 =
  match (p1, p2) with
  | IProof, IProof -> IProof
  | CProof t1', IProof -> CProof (EConstr.mkApp (op_constr, [|t1'; t2|]))
  | IProof, CProof t2' -> CProof (EConstr.mkApp (op_constr, [|t1; t2'|]))
  | CProof t1', CProof t2' -> CProof (EConstr.mkApp (op_constr, [|t1'; t2'|]))
  | _, _ ->
    let t1', p1 = mkprf t1 p1 in
    let t2', p2 = mkprf t2 p2 in
    TProof
      ( EConstr.mkApp (op_constr, [|t1'; t2'|])
      , EConstr.mkApp (op_iff, [|t1; t2; t1'; t2'; p1; p2|]) )

let trans_bin_prop op_constr op_iff t1 p1 t2 p2 =
  let prf = trans_bin_prop op_constr op_iff t1 p1 t2 p2 in
  debug_zify (fun () -> pp_prfp prf);
  prf

let trans_un_prop op_constr op_iff p1 prf1 =
  match prf1 with
  | IProof -> IProof
  | CProof p1' -> CProof (EConstr.mkApp (op_constr, [|p1'|]))
  | TProof (p1', prf) ->
    TProof
      ( EConstr.mkApp (op_constr, [|p1'|])
      , EConstr.mkApp (op_iff, [|p1; p1'; prf|]) )

let rec trans_prop env evd e =
  match classify_prop env evd e with
  | BINOP ({op_constr; op_iff}, p1, p2) ->
    let prf1 = trans_prop env evd p1 in
    let prf2 = trans_prop env evd p2 in
    trans_bin_prop op_constr op_iff p1 prf1 p2 prf2
  | UNOP ({op_constr; op_iff}, p1) ->
    let prf1 = trans_prop env evd p1 in
    trans_un_prop op_constr op_iff p1 prf1
  | OTHEROP (c, a) -> (
    try
      let k, t =
        find_option
          (match_operator env evd c a)
          (ConstrMap.find_all evd c !table_cache)
      in
      let n = Array.length a in
      match k with
      | BinRel {decl = br; deriv = rop} ->
        let a1 =
          trans_expr env evd
            { constr = a.(n - 2)
            ; typ = rop.EBinRelT.source
            ; inj = rop.EBinRelT.inj }
        in
        let a2 =
          trans_expr env evd
            { constr = a.(n - 1)
            ; typ = rop.EBinRelT.source
            ; inj = rop.EBinRelT.inj }
        in
        trans_binrel evd e rop a.(n - 2) a1 a.(n - 1) a2
      | _ -> IProof
    with Not_found | DestKO -> IProof )

let trans_check_prop env evd t =
  if is_prop env evd t then Some (trans_prop env evd t) else None

let get_hyp_typ = function
  | NamedDecl.LocalDef (h, _, ty) | NamedDecl.LocalAssum (h, ty) ->
    (h.Context.binder_name, EConstr.of_constr ty)

let trans_hyps env evd l =
  List.fold_left
    (fun acc decl ->
      let h, ty = get_hyp_typ decl in
      match trans_check_prop env evd ty with
      | None -> acc
      | Some p' -> (h, ty, p') :: acc)
    [] l

let trans_hyp h t0 prfp =
  debug_zify (fun () -> Pp.(str "trans_hyp: " ++ pp_prfp prfp ++ fnl ()));
  match prfp with
  | IProof -> Tacticals.tclIDTAC (* Should detect before *)
  | CProof t' ->
    Proofview.Goal.enter (fun gl ->
        let env = Tacmach.pf_env gl in
        let evd = Tacmach.project gl in
        let t' = Reductionops.nf_betaiota env evd t' in
        Tactics.change_in_hyp ~check:true None
          (Tactics.make_change_arg t')
          (h, Locus.InHypTypeOnly))
  | TProof (t', prf) ->
    Tacticals.(
      Proofview.Goal.enter (fun gl ->
          let env = Tacmach.pf_env gl in
          let evd = Tacmach.project gl in
          let target = Reductionops.nf_betaiota env evd t' in
          let h' = Tactics.fresh_id_in_env Id.Set.empty h env in
          let prf =
            EConstr.mkApp (force rew_iff, [|t0; target; prf; EConstr.mkVar h|])
          in
          tclTHEN
            (Tactics.pose_proof (Name.Name h') prf)
            (tclTRY
               (tclTHEN (Tactics.clear [h]) (Tactics.rename_hyp [(h', h)])))))

let trans_concl prfp =
  debug_zify (fun () -> Pp.(str "trans_concl: " ++ pp_prfp prfp ++ fnl ()));
  match prfp with
  | IProof -> Tacticals.tclIDTAC
  | CProof t ->
    Proofview.Goal.enter (fun gl ->
        let env = Tacmach.pf_env gl in
        let evd = Tacmach.project gl in
        let t' = Reductionops.nf_betaiota env evd t in
        Tactics.change_concl t')
  | TProof (t, prf) ->
    Proofview.Goal.enter (fun gl ->
        let env = Tacmach.pf_env gl in
        let evd = Tacmach.project gl in
        let typ = get_type_of env evd prf in
        match EConstr.kind evd typ with
        | App (c, a) when Array.length a = 2 ->
          Tactics.apply
            (EConstr.mkApp (Lazy.force rew_iff_rev, [|a.(0); a.(1); prf|]))
        | _ ->
          raise (CErrors.anomaly Pp.(str "zify cannot transform conclusion")))

let tclTHENOpt e tac tac' =
  match e with None -> tac' | Some e' -> Tacticals.tclTHEN (tac e') tac'

let assert_inj t =
  init_cache ();
  Proofview.Goal.enter (fun gl ->
      let env = Tacmach.pf_env gl in
      let evd = Tacmach.project gl in
      try
        ignore (get_injection env evd t);
        Tacticals.tclIDTAC
      with Not_found ->
        Tacticals.tclFAIL (Pp.str " InjTyp does not exist"))

let elim_binding x t ty =
  Proofview.Goal.enter (fun gl ->
      let env = Tacmach.pf_env gl in
      let h =
        Tactics.fresh_id_in_env Id.Set.empty (Nameops.add_prefix "heq_" x) env
      in
      Tacticals.tclTHEN
        (Tactics.pose_proof (Name h) (eq_proof ty (EConstr.mkVar x) t))
        (Tacticals.tclTRY (Tactics.clear_body [x])))

let do_let tac (h : Constr.named_declaration) =
  match h with
  | Context.Named.Declaration.LocalAssum _ -> Tacticals.tclIDTAC
  | Context.Named.Declaration.LocalDef (id, t, ty) ->
    Proofview.Goal.enter (fun gl ->
        let env = Tacmach.pf_env gl in
        let evd = Tacmach.project gl in
        try
          let x = id.Context.binder_name in
          ignore
            (let eq = Lazy.force eq in
             find_option
               (match_operator env evd eq
                  [|EConstr.of_constr ty; EConstr.mkVar x; EConstr.of_constr t|])
               (ConstrMap.find_all evd eq !table_cache));
          tac x (EConstr.of_constr t) (EConstr.of_constr ty)
        with Not_found -> Tacticals.tclIDTAC)

let iter_let_aux tac =
  Proofview.Goal.enter (fun gl ->
      let env = Tacmach.pf_env gl in
      let sign = Environ.named_context env in
      init_cache ();
      Tacticals.tclMAP (do_let tac) sign)

let iter_let (tac : Ltac_plugin.Tacinterp.Value.t) =
  iter_let_aux (fun (id : Names.Id.t) t ty ->
      Ltac_plugin.Tacinterp.Value.apply tac
        [ Ltac_plugin.Tacinterp.Value.of_constr (EConstr.mkVar id)
        ; Ltac_plugin.Tacinterp.Value.of_constr t
        ; Ltac_plugin.Tacinterp.Value.of_constr ty ])

let elim_let = iter_let_aux elim_binding

let zify_tac =
  Proofview.Goal.enter (fun gl ->
      Coqlib.check_required_library ["Coq"; "micromega"; "ZifyClasses"];
      Coqlib.check_required_library ["Coq"; "micromega"; "ZifyInst"];
      init_cache ();
      let evd = Tacmach.project gl in
      let env = Tacmach.pf_env gl in
      let sign = Environ.named_context env in
      let concl = trans_check_prop env evd (Tacmach.pf_concl gl) in
      let hyps = trans_hyps env evd sign in
      let l = CstrTable.get () in
      tclTHENOpt concl trans_concl
        (Tacticals.tclTHEN
           (Tacticals.tclTHENLIST
              (List.rev_map (fun (h, p, t) -> trans_hyp h p t) hyps))
           (CstrTable.gen_cstr l)))

type pscript = Set of Names.Id.t * EConstr.t | Pose of Names.Id.t * EConstr.t

type spec_env =
  { map : Names.Id.t HConstr.t
  ; spec_name : Names.Id.t
  ; term_name : Names.Id.t
  ; fresh : Nameops.Subscript.t
  ; proofs : pscript list }

let register_constr {map; spec_name; term_name; fresh; proofs} c thm =
  let tname = Nameops.add_subscript term_name fresh in
  let sname = Nameops.add_subscript spec_name fresh in
  ( EConstr.mkVar tname
  , { map = HConstr.add c tname map
    ; spec_name
    ; term_name
    ; fresh = Nameops.Subscript.succ fresh
    ; proofs = Set (tname, c) :: Pose (sname, thm) :: proofs } )

let fresh_subscript env =
  let ctx = (Environ.named_context_val env).Environ.env_named_map in
  Nameops.Subscript.succ
    (Names.Id.Map.fold
       (fun id _ s ->
         let _, s' = Nameops.get_subscript id in
         let cmp = Nameops.Subscript.compare s s' in
         if cmp = 0 then s else if cmp < 0 then s' else s)
       ctx Nameops.Subscript.zero)

let init_env sname tname s =
  { map = HConstr.empty
  ; spec_name = sname
  ; term_name = tname
  ; fresh = s
  ; proofs = [] }

let rec spec_of_term env evd (senv : spec_env) t =
  let get_name t env =
    try EConstr.mkVar (HConstr.find t senv.map) with Not_found -> t
  in
  let c, a = decompose_app env evd t in
  if a = [||] then (* The term cannot be decomposed. *)
    (get_name t senv, senv)
  else
    (* recursively analyse the sub-terms *)
    let a', senv' =
      Array.fold_right
        (fun e (l, senv) ->
          let r, senv = spec_of_term env evd senv e in
          (r :: l, senv))
        a ([], senv)
    in
    let a' = Array.of_list a' in
    let t' = EConstr.mkApp (c, a') in
    try (EConstr.mkVar (HConstr.find t' senv'.map), senv')
    with Not_found -> (
      try
        match snd (ConstrMap.find evd c !specs_cache) with
        | UnOpSpec s | BinOpSpec s ->
          let thm = EConstr.mkApp (s.deriv.ESpecT.spec, a') in
          register_constr senv' t' thm
        | _ -> (get_name t' senv', senv')
      with Not_found | DestKO -> (t', senv') )

let interp_pscript s =
  match s with
  | Set (id, c) ->
    Tacticals.tclTHEN
      (Tactics.letin_tac None (Names.Name id) c None
         {Locus.onhyps = None; Locus.concl_occs = Locus.AllOccurrences})
      (Tactics.clear_body [id])
  | Pose (id, c) -> Tactics.pose_proof (Names.Name id) c

let rec interp_pscripts l =
  match l with
  | [] -> Tacticals.tclIDTAC
  | s :: l -> Tacticals.tclTHEN (interp_pscript s) (interp_pscripts l)

let spec_of_hyps =
  Proofview.Goal.enter (fun gl ->
      let terms =
        Tacmach.pf_concl gl :: List.map snd (Tacmach.pf_hyps_types gl)
      in
      let env = Tacmach.pf_env gl in
      let evd = Tacmach.project gl in
      let s = fresh_subscript env in
      let env =
        List.fold_left
          (fun acc t -> snd (spec_of_term env evd acc t))
          (init_env (Names.Id.of_string "H") (Names.Id.of_string "z") s)
          terms
      in
      interp_pscripts (List.rev env.proofs))

let iter_specs = spec_of_hyps

let find_hyp evd t l =
  try
    Some
      (EConstr.mkVar
         (fst (List.find (fun (h, t') -> EConstr.eq_constr evd t t') l)))
  with Not_found -> None

let find_proof evd t l =
  if EConstr.eq_constr evd t (Lazy.force op_True) then Some (Lazy.force op_I)
  else find_hyp evd t l

(** [sat_constr env evd sub taclist hyps c d]= (sub',taclist',hyps') where
    -  sub' is a fresh subscript obtained from sub
    - taclist' is obtained from taclist by posing the lemma 'd' applied to 'c'
    - hyps' is obtained from hyps'
    taclist and hyps are threaded to avoid adding duplicates
 *)
let sat_constr env evd (sub,taclist, hyps) c d =
  match EConstr.kind evd c with
  | App (c, args) ->
     if Array.length args = 2 then
       let h1 =
         Tacred.cbv_beta env evd
           (EConstr.mkApp (d.ESatT.parg1, [|args.(0)|]))
       in
       let h2 =
         Tacred.cbv_beta env evd
           (EConstr.mkApp (d.ESatT.parg2, [|args.(1)|]))
       in
       let n = Nameops.add_subscript (Names.Id.of_string "__sat") sub in
       let trm =
         match (find_proof evd h1 hyps, find_proof evd h2 hyps) with
         | Some h1, Some h2 ->
            (EConstr.mkApp (d.ESatT.satOK, [|args.(0); args.(1); h1; h2|]))
         | Some h1, _ ->
            EConstr.mkApp (d.ESatT.satOK, [|args.(0); args.(1); h1|])
         | _, _ -> EConstr.mkApp (d.ESatT.satOK, [|args.(0); args.(1)|])
       in
       let rtrm = Tacred.cbv_beta env evd trm in
       let typ  = Retyping.get_type_of env evd rtrm in
       match find_hyp evd typ hyps with
       | None -> (Nameops.Subscript.succ sub, (Tactics.pose_proof (Names.Name n) rtrm :: taclist) , (n,typ)::hyps)
       | Some _ -> (sub, taclist, hyps)
     else (sub,taclist,hyps)
  | _ -> (sub,taclist,hyps)


let get_all_sat env evd c =
  List.fold_left
    (fun acc e -> match e with _, Saturate s -> s :: acc | _ -> acc)
    []
    ( try ConstrMap.find_all evd c !saturate_cache
      with DestKO | Not_found -> [] )

let saturate =
  Proofview.Goal.enter (fun gl ->
      init_cache ();
      let table = CstrTable.HConstr.create 20 in
      let concl = Tacmach.pf_concl gl in
      let hyps = Tacmach.pf_hyps_types gl in
      let evd = Tacmach.project gl in
      let env = Tacmach.pf_env gl in
      let rec sat t =
        match EConstr.kind evd t with
        | App (c, args) ->
          sat c;
          Array.iter sat args;
          if Array.length args = 2 then
            let ds = get_all_sat env evd c in
            if ds = [] ||  CstrTable.HConstr.mem table t
            then ()
            else List.iter (fun x ->
                     CstrTable.HConstr.add table t x.deriv) ds
          else ()
        | Prod (a, t1, t2) when a.Context.binder_name = Names.Anonymous ->
          sat t1; sat t2
        | _ -> ()
      in
      (* Collect all the potential saturation lemma *)
      sat concl;
      List.iter (fun (_, t) -> sat t) hyps;
      let s0 = fresh_subscript env in
      let (_,tacs,_) = CstrTable.HConstr.fold (fun c d acc -> sat_constr env evd acc c d) table (s0,[],hyps) in
      Tacticals.tclTHENLIST tacs)
