(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Constr
open Names
open Pp
open Lazy

(** [get_type_of] performs beta reduction ;
    Is it ok for Retyping.get_type_of (Zpower_nat n q) to return (fun _ : nat => Z) q ? *)
let get_type_of env evd e =
  Tacred.cbv_beta env evd (Retyping.get_type_of env evd e)

(** [unsafe_to_constr c] returns a [Constr.t] without considering an evar_map.
    This is useful for calling Constr.hash *)
let unsafe_to_constr = EConstr.Unsafe.to_constr

let pr_constr env evd e = Printer.pr_econstr_env env evd e

let rec find_option pred l =
  match l with
  | [] -> raise Not_found
  | e::l -> match pred e with
            | Some r -> r
            | None   -> find_option pred l


(** [HConstr] is a map indexed by EConstr.t.
    It should only be used using closed terms.
 *)
module HConstr = struct
  module M = Map.Make (struct
    type t = EConstr.t

    let compare c c' =
      Constr.compare (unsafe_to_constr c) (unsafe_to_constr c')
  end)

  type 'a t = 'a list M.t

  let lfind h m = try M.find h m with Not_found -> []

  let add h e m =
    let l = lfind h m in
    M.add h (e :: l) m

  let empty = M.empty

  let find h m = match lfind h m with e :: _ -> e | [] -> raise Not_found

  let find_all = lfind

  let fold f m acc =
    M.fold (fun k l acc -> List.fold_left (fun acc e -> f k e acc) acc l) m acc

end


(** [get_projections_from_constant (evd,c) ]
    returns an array of constr [| a1,.. an|] such that [c] is defined as
    Definition c := mk a1 .. an with mk a constructor.
    ai is therefore either a type parameter or a projection.
 *)


let get_projections_from_constant (evd, i) =
  match EConstr.kind evd (Reductionops.clos_whd_flags CClosure.all (Global.env ()) evd i) with
  | App (c, a) -> Some a
  | _ ->
     raise (CErrors.user_err Pp.(str "The hnf of term " ++ pr_constr (Global.env ()) evd i
                          ++ str " should be an application i.e. (c a1 ... an)"))

(**  An instance of type, say T, is registered into a hashtable, say TableT. *)

type 'a decl =
  { decl: EConstr.t
  ; (* Registered type instance *)
    deriv: 'a
  (* Projections of insterest *) }


module EInjT = struct
  type t =
    { isid: bool
    ; (* S = T ->  inj = fun x -> x*)
      source: EConstr.t
    ; (* S *)
      target: EConstr.t
    ; (* T *)
      (* projections *)
      inj: EConstr.t
    ; (* S -> T *)
      pred: EConstr.t
    ; (* T -> Prop *)
      cstr: EConstr.t option
    (* forall x, pred (inj x) *) }
end

module EBinOpT = struct
  type t =
    { (* Op : source1 -> source2 -> source3 *)
      source1: EConstr.t
    ; source2: EConstr.t
    ; source3: EConstr.t
    ; target: EConstr.t
    ; inj1: EConstr.t
    ; (* InjTyp source1 target *)
      inj2: EConstr.t
    ; (* InjTyp source2 target *)
      inj3: EConstr.t
    ; (* InjTyp source3 target *)
      tbop: EConstr.t
    (* TBOpInj *) }
end

module ECstOpT = struct
  type t = {source: EConstr.t; target: EConstr.t; inj: EConstr.t}
end

module EUnOpT = struct
  type t =
    { source1: EConstr.t
    ; source2: EConstr.t
    ; target: EConstr.t
    ; inj1_t: EConstr.t
    ; inj2_t: EConstr.t
    ; unop: EConstr.t }
end

module EBinRelT = struct
  type t =
    {source: EConstr.t; target: EConstr.t; inj: EConstr.t; brel: EConstr.t}
end

module EPropBinOpT = struct
  type t = EConstr.t
end

module EPropUnOpT = struct
  type t = EConstr.t
end


module ESatT = struct
  type t =  {parg1: EConstr.t; parg2: EConstr.t; satOK: EConstr.t}
end

(* Different type of declarations *)
type decl_kind =
  | PropOp of EPropBinOpT.t decl
  | PropUnOp  of EPropUnOpT.t decl
  | InjTyp of EInjT.t  decl
  | BinRel of EBinRelT.t  decl
  | BinOp  of EBinOpT.t  decl
  | UnOp   of EUnOpT.t  decl
  | CstOp  of ECstOpT.t  decl
  | Saturate of ESatT.t  decl


let get_decl  = function
  | PropOp d -> d.decl
  | PropUnOp  d -> d.decl
  | InjTyp d    -> d.decl
  | BinRel d    -> d.decl
  | BinOp  d    -> d.decl
  | UnOp   d    -> d.decl
  | CstOp  d    -> d.decl
  | Saturate d  -> d.decl

type term_kind =
  | Application of EConstr.constr
  | OtherTerm of EConstr.constr


module type Elt = sig
  type elt

  val name : string
  (** name *)

  val table : (term_kind * decl_kind)  HConstr.t ref

  val cast : elt decl -> decl_kind

  val dest : decl_kind -> (elt decl) option

  val get_key : int
  (** [get_key] is the type-index used as key for the instance *)

  val mk_elt : Evd.evar_map -> EConstr.t -> EConstr.t array -> elt
  (** [mk_elt evd i [a0,..,an]  returns the element of the table
        built from the type-instance i and the arguments (type indexes and projections)
        of the type-class constructor. *)

                                                                 (*  val arity : int*)

end


let table =  Summary.ref  ~name:("zify_table") HConstr.empty

let saturate = Summary.ref ~name:("zify_saturate") HConstr.empty

let table_cache = ref HConstr.empty
let saturate_cache = ref HConstr.empty


(** Each type-class gives rise to a different table.
    They only differ on how projections are extracted.  *)
module EInj = struct
  open EInjT

  type elt = EInjT.t

  let name = "EInj"

  let table = table

  let cast x = InjTyp x

  let dest = function
    | InjTyp x -> Some x
    | _        -> None


  let mk_elt evd i (a : EConstr.t array) =
    let isid = EConstr.eq_constr evd a.(0) a.(1) in
    { isid
    ; source= a.(0)
    ; target= a.(1)
    ; inj= a.(2)
    ; pred= a.(3)
    ; cstr= (if isid then None else Some a.(4)) }

  let get_key = 0

end

module EBinOp = struct
  type elt = EBinOpT.t
  open EBinOpT

  let name = "BinOp"

  let table = table

  let mk_elt evd i a =
    { source1= a.(0)
    ; source2= a.(1)
    ; source3= a.(2)
    ; target= a.(3)
    ; inj1= a.(5)
    ; inj2= a.(6)
    ; inj3= a.(7)
    ; tbop= a.(9) }

  let get_key = 4


  let cast x = BinOp x

  let dest = function
    | BinOp  x -> Some x
    | _  -> None

end

module ECstOp = struct
  type elt = ECstOpT.t
  open ECstOpT

  let name = "CstOp"

  let table = table

  let cast x = CstOp x

  let dest = function
    | CstOp  x -> Some x
    | _  -> None


  let mk_elt evd i a = {source= a.(0); target= a.(1); inj= a.(3)}

  let get_key = 2

end

module EUnOp = struct
  type elt = EUnOpT.t
  open EUnOpT

  let name = "UnOp"

  let table = table

  let cast x = UnOp x

  let dest = function
    | UnOp  x -> Some x
    | _  -> None


  let mk_elt evd i a =
    { source1= a.(0)
    ; source2= a.(1)
    ; target= a.(2)
    ; inj1_t= a.(4)
    ; inj2_t= a.(5)
    ; unop= a.(6) }

  let get_key = 3

end

module EBinRel = struct
  type elt = EBinRelT.t
  open EBinRelT

  let name = "BinRel"

  let table = table

  let cast x = BinRel x

  let dest = function
    | BinRel  x -> Some x
    | _  -> None

  let mk_elt evd i a = {source= a.(0); target= a.(1); inj= a.(3); brel= a.(4)}

  let get_key = 2

end

module EPropOp = struct
  type elt = EConstr.t

  let name = "PropBinOp"

  let table = table

  let cast x = PropOp x

  let dest = function
    | PropOp  x -> Some x
    | _  -> None

  let mk_elt evd i a = i

  let get_key = 0

end

module EPropUnOp = struct
  type elt = EConstr.t

  let name = "PropUnOp"

  let table = table

  let cast x = PropUnOp x

  let dest = function
    | PropUnOp  x -> Some x
    | _  -> None

  let mk_elt evd i a = i

  let get_key = 0

end



let constr_of_term_kind = function
  | Application c -> c
  | OtherTerm   c -> c



let fold_declared_const f evd acc =
  HConstr.fold
    (fun _ (_,e) acc -> f (fst (EConstr.destConst evd (get_decl e))) acc)
    (!table_cache) acc



module type S = sig
  val register : Constrexpr.constr_expr -> unit

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

  let register_hint  evd t elt =
    match EConstr.kind evd t with
    | App(c,_) ->
       E.table := HConstr.add c (Application t, E.cast elt) !E.table
    |  _       -> E.table := HConstr.add t (OtherTerm t, E.cast elt) !E.table




  let register_constr env evd c =
    let c = EConstr.of_constr c in
    let t = get_type_of env evd c in
    match EConstr.kind evd t with
    | App (intyp, args) ->
        let styp = args.(E.get_key) in
        let elt = {decl= c; deriv=  (make_elt (evd, c))} in
        register_hint evd styp elt
    | _ ->
       let env = Global.env () in
       raise (CErrors.user_err Pp.
              (str ": Cannot register term "++pr_constr env evd c++
                 str ". It has type "++pr_constr env evd t++str " which should be of the form  [F X1 .. Xn]"))

  let register_obj : Constr.constr -> Libobject.obj =
    let cache_constr (_, c) =
      let env = Global.env () in
      let evd = Evd.from_env env in
      register_constr env evd c
    in
    let subst_constr (subst, c) = Mod_subst.subst_mps subst c in
    Libobject.declare_object
    @@ Libobject.superglobal_object_nodischarge
         ("register-zify-" ^  E.name)
         ~cache:cache_constr ~subst:(Some subst_constr)

  (** [register c] is called from the VERNACULAR ADD [name] constr(t).
       The term [c] is interpreted and
       registered as a [superglobal_object_nodischarge].
       TODO: pre-compute [get_type_of] - [cache_constr] is using another environment.
     *)
  let register = fun c ->
    let env = Global.env () in
    let evd = Evd.from_env env in
    let evd, c = Constrintern.interp_open_constr env evd c in
    let _ = Lib.add_anonymous_leaf (register_obj (EConstr.to_constr evd c)) in
    ()


  let pp_keys () =
    let env = Global.env () in
    let evd = Evd.from_env env in
    HConstr.fold
      (fun _ (k,d) acc ->
        match E.dest d with
        | None -> acc
        | Some _ ->
           Pp.(pr_constr env evd (constr_of_term_kind k) ++ str " " ++ acc))
      (!E.table) (Pp.str "")


  let print () =  Feedback.msg_info (pp_keys ())

end


module InjTable = MakeTable (EInj)


module ESat = struct
  type elt = ESatT.t
  open ESatT

  let name = "Saturate"

  let table = saturate

  let cast x = Saturate x

  let dest = function
    | Saturate  x -> Some x
    | _  -> None

  let mk_elt evd i a = {parg1= a.(2); parg2= a.(3); satOK= a.(5)}

  let get_key = 1

end

module BinOp = MakeTable (EBinOp)
module UnOp = MakeTable (EUnOp)
module CstOp = MakeTable (ECstOp)
module BinRel = MakeTable (EBinRel)
module PropOp = MakeTable (EPropOp)
module PropUnOp = MakeTable (EPropUnOp)
module Saturate = MakeTable (ESat)

let init_cache () =
  table_cache :=  !table;
  saturate_cache := !saturate


(** The module [Spec] is used to register
    the instances of [BinOpSpec], [UnOpSpec].
    They are not indexed and stored in a list. *)

module Spec = struct
  let table = Summary.ref ~name:"zify_Spec" []

  let register_obj : Constr.constr -> Libobject.obj =
    let cache_constr (_, c) = table := EConstr.of_constr c :: !table in
    let subst_constr (subst, c) = Mod_subst.subst_mps subst c in
    Libobject.declare_object
    @@ Libobject.superglobal_object_nodischarge "register-zify-Spec"
         ~cache:cache_constr ~subst:(Some subst_constr)

  let register c =
    let env = Global.env () in
    let evd = Evd.from_env env in
    let _, c = Constrintern.interp_open_constr env evd c in
    let _ = Lib.add_anonymous_leaf (register_obj (EConstr.to_constr evd c)) in
    ()

  let get () = !table

  let print () =
    let env = Global.env () in
    let evd = Evd.from_env env in
    let constr_of_spec c =
      let t = get_type_of env evd c in
      match EConstr.kind evd t with
      | App (intyp, args) -> pr_constr env evd args.(2)
      | _ -> Pp.str ""
    in
    let l =
      List.fold_left
        (fun acc c -> Pp.(constr_of_spec c ++ str " " ++ acc))
        (Pp.str "") !table
    in
    Feedback.msg_notice l
end


let unfold_decl evd =
  let f cst acc = cst :: acc in
  fold_declared_const f evd []

open EInjT

(** Get constr of lemma and projections in ZifyClasses. *)

let zify str =
  EConstr.of_constr
    (UnivGen.constr_of_monomorphic_global
       (Coqlib.lib_ref ("ZifyClasses." ^ str)))

let locate_const str =
  let rf = "ZifyClasses." ^ str in
  match Coqlib.lib_ref rf with
  | GlobRef.ConstRef c -> c
  | _ -> CErrors.anomaly Pp.(str rf ++ str " should be a constant")

(* The following [constr] are necessary for constructing the proof terms *)
let mkapp2 = lazy (zify "mkapp2")

let mkapp = lazy (zify "mkapp")

let mkapp0 = lazy (zify "mkapp0")

let mkdp = lazy (zify "mkinjterm")

let eq_refl = lazy (zify "eq_refl")

let mkrel = lazy (zify "mkrel")

let mkprop_op = lazy (zify "mkprop_op")

let mkuprop_op = lazy (zify "mkuprop_op")

let mkdpP = lazy (zify "mkinjprop")

let iff_refl = lazy (zify "iff_refl")

let q = lazy (zify "target_prop")

let ieq = lazy (zify "injprop_ok")

let iff = lazy (zify "iff")



(* A super-set of the previous are needed to unfold the generated proof terms. *)

let to_unfold =
  lazy
    (List.rev_map locate_const
       [ "source_prop"
       ; "target_prop"
       ; "uop_iff"
       ; "op_iff"
       ; "mkuprop_op"
       ; "TUOp"
       ; "inj_ok"
       ; "TRInj"
       ; "inj"
       ; "source"
       ; "injprop_ok"
       ; "TR"
       ; "TBOp"
       ; "TCst"
       ; "target"
       ; "mkrel"
       ; "mkapp2"
       ; "mkapp"
       ; "mkapp0"
       ; "mkprop_op" ])


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
    HConstr.clear table ; l

  (** [gen_cstr table] asserts (cstr k) for each element of the table (k,cstr).
        NB: the constraint is only asserted if it does not already exist in the context.
     *)
  let gen_cstr table =
    Proofview.Goal.enter (fun gl ->
        let evd = Tacmach.New.project gl in
        (* Build the table of existing hypotheses *)
        let has_hyp =
          let hyps_table = HConstr.create 20 in
          List.iter
            (fun (_, (t : EConstr.types)) -> HConstr.add hyps_table t ())
            (Tacmach.New.pf_hyps_types gl) ;
          fun c -> HConstr.mem hyps_table c
        in
        (* Add the constraint (cstr k) if it is not already present *)
        let gen k cstr =
          Proofview.Goal.enter (fun gl ->
              let env = Tacmach.New.pf_env gl in
              let term = EConstr.mkApp (cstr, [|k|]) in
              let types = get_type_of env evd term in
              if has_hyp types then Tacticals.New.tclIDTAC
              else
                let n =
                  Tactics.fresh_id_in_env Id.Set.empty
                    (Names.Id.of_string "cstr")
                    env
                in
                Tactics.pose_proof (Names.Name n) term )
        in
        List.fold_left
          (fun acc (k, i) -> Tacticals.New.tclTHEN (gen k i) acc)
          Tacticals.New.tclIDTAC table )
end

let mkvar red evd inj v =
  ( if not red then
    match inj.cstr with None -> () | Some ctr -> CstrTable.register evd v ctr
  ) ;
  let iv = EConstr.mkApp (inj.inj, [|v|]) in
  let iv = if red then Tacred.compute (Global.env ()) evd iv else iv in
  EConstr.mkApp
    ( force mkdp
    , [| inj.source
       ; inj.target
       ; inj.inj
       ; v
       ; iv
       ; EConstr.mkApp (force eq_refl, [|inj.target; iv|]) |] )

type texpr =
  | Var of EInj.elt * EConstr.t
      (** Var is a term that cannot be injected further *)
  | Constant of EInj.elt * EConstr.t
      (** Constant is a term that is solely built from constructors *)
  | Injterm of EConstr.t
      (** Injected is an injected term represented by a  term of type [injterm] *)

let is_constant = function Constant _ -> true | _ -> false

let constr_of_texpr = function
  | Constant (i, e) | Var (i, e) -> if i.isid then Some e else None
  | _ -> None

let inj_term_of_texpr evd = function
  | Injterm e -> e
  | Var (inj, e) -> mkvar false evd inj e
  | Constant (inj, e) -> mkvar true evd inj e

let mkapp2_id evd i (* InjTyp S3 T *)
                    inj (* deriv i *)
                        t (* S1 -> S2 -> S3 *)
                          b (* Binop S1 S2 S3 t ... *)
                            dbop (* deriv b *) e1 e2 =
  let default () =
    let e1' = inj_term_of_texpr evd e1 in
    let e2' = inj_term_of_texpr evd e2 in
    EBinOpT.(
      Injterm
        (EConstr.mkApp
           ( force mkapp2
           , [| dbop.source1
              ; dbop.source2
              ; dbop.source3
              ; dbop.target
              ; t
              ; dbop.inj1
              ; dbop.inj2
              ; dbop.inj3
              ; b
              ; e1'
              ; e2' |] )))
  in
  if not inj.isid then default ()
  else
    match (e1, e2) with
    | Constant (_, e1), Constant (_, e2)
     |Var (_, e1), Var (_, e2)
     |Constant (_, e1), Var (_, e2)
     |Var (_, e1), Constant (_, e2) ->
        Var (inj, EConstr.mkApp (t, [|e1; e2|]))
    | _, _ -> default ()

let mkapp_id evd i inj (unop, u) f e1 =
  EUnOpT.(if EConstr.eq_constr evd u.unop f then
    (* Injection does nothing *)
    match e1 with
    | Constant (_, e) | Var (_, e) -> Var (inj, EConstr.mkApp (f, [|e|]))
    | Injterm e1 ->
        Injterm
          (EConstr.mkApp
             ( force mkapp
             , [| u.source1
                ; u.source2
                ; u.target
                ; f
                ; u.inj1_t
                ; u.inj2_t
                ; unop
                ; e1 |] ))
  else
    let e1 = inj_term_of_texpr evd e1 in
    Injterm
      (EConstr.mkApp
         ( force mkapp
         , [|u.source1; u.source2; u.target; f; u.inj1_t; u.inj2_t; unop; e1|]
         )))

type typed_constr = {constr: EConstr.t; typ: EConstr.t}



let get_injection env evd t =
  match snd (HConstr.find t !table_cache) with
  | InjTyp i -> i
  | _        -> raise Not_found


 (* [arrow] is the term (fun (x:Prop) (y : Prop) => x -> y) *)
 let arrow =
   let name x =
     Context.make_annot (Name.mk_name (Names.Id.of_string x)) Sorts.Relevant  in
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
  let sort  = Retyping.get_sort_of env sigma term in
  Sorts.is_prop sort

 (** [get_application env evd e] expresses [e] as an application (c a)
     where c is the head symbol and [a] is the array of arguments.
     The function also transforms (x -> y) as (arrow x y) *)
 let get_operator env evd e =
   let is_arrow a p1 p2 =
     is_prop env evd p1 && is_prop (EConstr.push_rel (Context.Rel.Declaration.LocalAssum(a,p1)) env) evd p2
     && (a.Context.binder_name = Names.Anonymous || EConstr.Vars.noccurn evd 1 p2) in
   match EConstr.kind evd e with
   | Prod (a, p1, p2) when is_arrow a p1 p2 ->
      (arrow,[|p1 ;p2|])
   | App(c,a) -> (c,a)
   |  _       -> (e,[||])


 let is_convertible env evd k t =
   Reductionops.check_conv env evd k t

 (** [match_operator env evd hd arg (t,d)]
     - hd is head operator of t
     - If t = OtherTerm _, then t = hd
     - If t = Application _, then
       we extract the relevant number of arguments from arg
       and check for convertibility *)
 let match_operator env evd hd args (t, d) =
   let decomp t i =
     let n = Array.length args in
     let t' = EConstr.mkApp(hd,Array.sub args 0 (n-i)) in
          if is_convertible env evd t' t
          then Some (d,t)
          else None in

   match t with
   | OtherTerm t -> Some(d,t)
   | Application t ->
      match d with
      | CstOp _    -> decomp t 0
      | UnOp _     -> decomp t 1
      | BinOp _    -> decomp t 2
      | BinRel _   -> decomp t 2
      | PropOp _   -> decomp t 2
      | PropUnOp _ -> decomp t 1
      |  _  -> None


 let rec trans_expr env evd e =
  (* Get the injection *)
  let {decl= i; deriv= inj} = get_injection  env evd e.typ in
  let e = e.constr in
  if EConstr.isConstruct evd e then Constant (inj, e) (* Evaluate later *)
  else
    let (c,a) = get_operator env evd e in
    try
      let (k,t) = find_option (match_operator env evd c a) (HConstr.find_all c !table_cache) in
      let n = Array.length a in
       match k with
       | CstOp {decl = c'} ->
          Injterm (EConstr.mkApp (force mkapp0, [|inj.source; inj.target; e; i; c'|]))
       | UnOp {decl = unop ; deriv = u} ->
          let a' = trans_expr env evd {constr= a.(n-1); typ= u.EUnOpT.source1} in
            if is_constant a' && EConstr.isConstruct evd t then
              Constant (inj, e)
            else mkapp_id evd i inj (unop, u) t a'
       | BinOp {decl = binop ; deriv = b} ->
          let a0 = trans_expr env evd {constr= a.(n-2); typ= b.EBinOpT.source1} in
          let a1 = trans_expr env evd {constr= a.(n-1); typ= b.EBinOpT.source2} in
          if is_constant a0 && is_constant a1 && EConstr.isConstruct evd t
          then Constant (inj, e)
          else mkapp2_id evd i inj t binop b a0 a1
       |  d  ->
           Var (inj,e)
    with Not_found -> Var (inj,e)

let trans_expr env evd e =
  try trans_expr env evd e with Not_found ->
    raise
      (CErrors.user_err
         ( Pp.str "Missing injection for type "
         ++ Printer.pr_leconstr_env env evd e.typ ))


type tprop =
  | TProp of EConstr.t  (** Transformed proposition *)
  | IProp of EConstr.t  (** Identical proposition *)

let mk_iprop e =
  EConstr.mkApp (force mkdpP, [|e; e; EConstr.mkApp (force iff_refl, [|e|])|])

let inj_prop_of_tprop = function TProp p -> p | IProp e -> mk_iprop e

let rec trans_prop env evd e =
  let (c,a) = get_operator env evd e in
  try
    let (k,t) = find_option (match_operator env evd c a) (HConstr.find_all c !table_cache) in
    let n = Array.length a in
    match k with
    | PropOp {decl= rop} ->
       begin
         try
           let t1 = trans_prop env evd a.(n-2) in
           let t2 = trans_prop env evd a.(n-1) in
           match (t1, t2) with
            | IProp _, IProp _ -> IProp e
            | _, _ ->
               let t1 = inj_prop_of_tprop t1 in
                let t2 = inj_prop_of_tprop t2 in
                TProp (EConstr.mkApp (force mkprop_op, [|t; rop; t1; t2|]))
         with Not_found -> IProp e
       end
    | BinRel {decl = br ; deriv = rop} ->
       begin
       try
            let a1 = trans_expr env evd {constr = a.(n-2) ; typ = rop.EBinRelT.source} in
            let a2 = trans_expr env evd {constr = a.(n-1) ; typ = rop.EBinRelT.source} in
            if EConstr.eq_constr evd t rop.EBinRelT.brel then
              match (constr_of_texpr a1, constr_of_texpr a2) with
              | Some e1, Some e2 -> IProp (EConstr.mkApp (t, [|e1; e2|]))
              | _, _ ->
                  let a1 = inj_term_of_texpr evd a1 in
                  let a2 = inj_term_of_texpr evd a2 in
                  TProp
                    (EConstr.mkApp
                       ( force mkrel
                       , [| rop.EBinRelT.source
                          ; rop.EBinRelT.target
                          ; t
                          ; rop.EBinRelT.inj
                          ; br
                          ; a1
                          ; a2 |] ))
            else
              let a1 = inj_term_of_texpr evd a1 in
              let a2 = inj_term_of_texpr evd a2 in
              TProp
                (EConstr.mkApp
                   ( force mkrel
                   , [| rop.EBinRelT.source
                      ; rop.EBinRelT.target
                      ; t
                      ; rop.EBinRelT.inj
                      ; br
                      ; a1
                      ; a2 |] ))
          with Not_found -> IProp e
       end
    | PropUnOp {decl = rop} ->
     begin
       try
         let t1 = trans_prop env evd a.(n-1) in
         match t1 with
         | IProp _ -> IProp e
         | _ ->
            let t1 = inj_prop_of_tprop t1 in
              TProp (EConstr.mkApp (force mkuprop_op, [|t; rop; t1|]))
       with Not_found -> IProp e
     end
  | _ ->  IProp e
  with Not_found -> IProp e

let unfold n env evd c =
  let cbv l =
    CClosure.RedFlags.(
      Tacred.cbv_norm_flags
        (mkflags
           (fBETA :: fMATCH :: fFIX :: fCOFIX :: fZETA :: List.rev_map fCONST l)))
  in
  let unfold_decl = unfold_decl evd in
  (* Unfold the let binding *)
  let c =
    match n with
    | None -> c
    | Some n ->
        Tacred.unfoldn [(Locus.AllOccurrences, Names.EvalVarRef n)] env evd c
  in
  (* Reduce the term *)
  let c = cbv (List.rev_append (force to_unfold)  unfold_decl) env evd c in
  c

let trans_check_prop env evd t =
  if is_prop  env evd t then
    (*let t = Tacred.unfoldn [Locus.AllOccurrences, Names.EvalConstRef coq_not] env evd t in*)
    match trans_prop env evd t with IProp e -> None | TProp e -> Some e
  else None

let trans_hyps env evd l =
  List.fold_left
    (fun acc (h, p) ->
      match trans_check_prop env evd p with
      | None -> acc
      | Some p' -> (h, p, p') :: acc )
    [] (List.rev l)

(* Only used if a direct rewrite fails *)
let trans_hyp h t =
  Tactics.(
    Tacticals.New.(
      Proofview.Goal.enter (fun gl ->
          let env = Tacmach.New.pf_env gl in
          let n =
            fresh_id_in_env Id.Set.empty (Names.Id.of_string "__zify") env
          in
          let h' = fresh_id_in_env Id.Set.empty h env in
          tclTHENLIST
            [ letin_tac None (Names.Name n) t None
                Locus.{onhyps= None; concl_occs= NoOccurrences}
            ; assert_by (Name.Name h')
                (EConstr.mkApp (force q, [|EConstr.mkVar n|]))
                (tclTHEN
                   (Equality.rewriteRL
                      (EConstr.mkApp (force ieq, [|EConstr.mkVar n|])))
                   (exact_check (EConstr.mkVar h)))
            ; reduct_in_hyp ~check:true ~reorder:false (unfold (Some n))
                (h', Locus.InHyp)
            ; clear [n]
            ; (* [clear H] may fail if [h] has dependencies *)
              tclTRY (clear [h]) ] )))

let is_progress_rewrite evd t rew =
  match EConstr.kind evd rew with
  | App (c, [|lhs; rhs|]) ->
      if EConstr.eq_constr evd (force iff) c then
        (* This is a successful rewriting *)
        not (EConstr.eq_constr evd lhs rhs)
      else
        CErrors.anomaly
          Pp.(
            str "is_progress_rewrite: not a rewrite"
            ++ pr_constr (Global.env ()) evd rew)
  | _ -> failwith "is_progress_rewrite: not even an application"

let trans_hyp h t0 t =
  Tacticals.New.(
    Proofview.Goal.enter (fun gl ->
        let env = Tacmach.New.pf_env gl in
        let evd = Tacmach.New.project gl in
        let t' = unfold None env evd (EConstr.mkApp (force ieq, [|t|])) in
        if is_progress_rewrite evd t0 (get_type_of env evd t') then
          tclFIRST
            [ Equality.general_rewrite_in true Locus.AllOccurrences true false
                h t' false
            ; trans_hyp h t ]
        else tclIDTAC ))

let trans_concl t =
  Tacticals.New.(
    Proofview.Goal.enter (fun gl ->
        let concl = Tacmach.New.pf_concl gl in
        let env = Tacmach.New.pf_env gl in
        let evd = Tacmach.New.project gl in
        let t' = unfold None env evd (EConstr.mkApp (force ieq, [|t|])) in
        if is_progress_rewrite evd concl (get_type_of env evd t') then
          Equality.general_rewrite true Locus.AllOccurrences true false t'
        else tclIDTAC ))

let tclTHENOpt e tac tac' =
  match e with None -> tac' | Some e' -> Tacticals.New.tclTHEN (tac e') tac'

let zify_tac =
  Proofview.Goal.enter (fun gl ->
      Coqlib.check_required_library ["Coq"; "micromega"; "ZifyClasses"] ;
      Coqlib.check_required_library ["Coq"; "micromega"; "ZifyInst"] ;
      init_cache ();
      let evd = Tacmach.New.project gl in
      let env = Tacmach.New.pf_env gl in
      let concl = trans_check_prop env evd (Tacmach.New.pf_concl gl) in
      let hyps = trans_hyps env evd (Tacmach.New.pf_hyps_types gl) in
      let l = CstrTable.get () in
      tclTHENOpt concl trans_concl
        (Tacticals.New.tclTHEN
           (Tacticals.New.tclTHENLIST
              (List.rev_map (fun (h, p, t) -> trans_hyp h p t) hyps))
           (CstrTable.gen_cstr l)) )

let iter_specs tac =
  Tacticals.New.tclTHENLIST
    (List.fold_left (fun acc d  -> tac d :: acc) [] (Spec.get ()))


let iter_specs (tac: Ltac_plugin.Tacinterp.Value.t) =
    iter_specs (fun c -> Ltac_plugin.Tacinterp.Value.apply tac [Ltac_plugin.Tacinterp.Value.of_constr c])

let find_hyp evd t l =
  try Some (fst (List.find (fun (h, t') -> EConstr.eq_constr evd t t') l))
  with Not_found -> None

let sat_constr c d =
  Proofview.Goal.enter (fun gl ->
      let evd = Tacmach.New.project gl in
      let env = Tacmach.New.pf_env gl in
      let hyps = Tacmach.New.pf_hyps_types gl in
      match EConstr.kind evd c with
      | App (c, args) ->
          if Array.length args = 2 then (
            let h1 =
              Tacred.cbv_beta env evd
                (EConstr.mkApp (d.ESatT.parg1, [|args.(0)|]))
            in
            let h2 =
              Tacred.cbv_beta env evd
                (EConstr.mkApp (d.ESatT.parg2, [|args.(1)|]))
            in
            match (find_hyp evd h1 hyps, find_hyp evd h2 hyps) with
            | Some h1, Some h2 ->
                let n =
                  Tactics.fresh_id_in_env Id.Set.empty
                    (Names.Id.of_string "__sat")
                    env
                in
                let trm =
                  EConstr.mkApp
                    ( d.ESatT.satOK
                    , [|args.(0); args.(1); EConstr.mkVar h1; EConstr.mkVar h2|]
                    )
                in
                Tactics.pose_proof (Names.Name n) trm
            | _, _ -> Tacticals.New.tclIDTAC )
          else Tacticals.New.tclIDTAC
      | _ -> Tacticals.New.tclIDTAC )


let get_all_sat env evd c =
  List.fold_left (fun acc e ->
      match e with
      | (_,Saturate s) -> s::acc
      |  _   -> acc) [] (HConstr.find_all c !saturate_cache )

let saturate =
  Proofview.Goal.enter (fun gl ->
      init_cache ();
      let table = CstrTable.HConstr.create 20 in
      let concl = Tacmach.New.pf_concl gl in
      let hyps = Tacmach.New.pf_hyps_types gl in
      let evd = Tacmach.New.project gl in
      let env = Tacmach.New.pf_env gl in
      let rec sat t =
        match EConstr.kind evd t with
        | App (c, args) ->
            sat c ;
            Array.iter sat args ;
            if Array.length args = 2 then
              let ds = get_all_sat env evd c in
              if ds = [] then ()
              else (
                List.iter (fun x -> CstrTable.HConstr.add table t x.deriv) ds )
            else ()
        | Prod (a, t1, t2) when a.Context.binder_name = Names.Anonymous ->
            sat t1 ; sat t2
        | _ -> ()
      in
      (* Collect all the potential saturation lemma *)
      sat concl ;
      List.iter (fun (_, t) -> sat t) hyps ;
      Tacticals.New.tclTHENLIST
        (CstrTable.HConstr.fold (fun c d acc -> sat_constr c d :: acc) table [])
  )
