(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(*i*)
open Util
open Constr
open Names
open Globnames
open Mod_subst
open Pp (* debug *)
(*i*)


(* Representation/approximation of terms to use in the dnet:
 *
 * - no meta or evar (use ['a pattern] for that)
 *
 * - [Rel]s and [Sort]s are not taken into account (that's why we need
 *   a second pass of linear filterin on the results - it's not a perfect
 *   term indexing structure)

 * - Foralls and LetIns are represented by a context DCtx (a list of
 *   generalization, similar to rel_context, and coded with DCons and
 *   DNil). This allows for matching under an unfinished context
 *)

module DTerm =
struct

  type 't t =
    | DRel
    | DSort
    | DRef    of GlobRef.t
    | DCtx    of 't * 't (* (binding list, subterm) = Prods and LetIns *)
    | DLambda of 't * 't
    | DApp    of 't * 't (* binary app *)
    | DCase   of case_info * 't * 't * 't array
    | DFix    of int array * int * 't array * 't array
    | DCoFix  of int * 't array * 't array
    | DInt    of Uint63.t

    (* special constructors only inside the left-hand side of DCtx or
       DApp. Used to encode lists of foralls/letins/apps as contexts *)
    | DCons   of ('t * 't option) * 't
    | DNil

  (* debug *)
  let _pr_dconstr f : 'a t -> Pp.t = function
    | DRel -> str "*"
    | DSort -> str "Sort"
    | DRef _ -> str "Ref"
    | DCtx (ctx,t) -> f ctx ++ spc() ++ str "|-" ++ spc () ++ f t
    | DLambda (t1,t2) -> str "fun"++ spc() ++ f t1 ++ spc() ++ str"->" ++ spc() ++ f t2
    | DApp (t1,t2) -> f t1 ++ spc() ++ f t2
    | DCase (_,t1,t2,ta) -> str "case"
    | DFix _ -> str "fix"
    | DCoFix _ -> str "cofix"
    | DInt _ -> str "INT"
    | DCons ((t,dopt),tl) -> f t ++ (match dopt with
	  Some t' -> str ":=" ++ f t'
	| None -> str "") ++ spc() ++ str "::" ++ spc() ++ f tl
    | DNil -> str "[]"

  (*
   * Functional iterators for the t datatype
   * a.k.a boring and error-prone boilerplate code
   *)

  let map f = function
    | (DRel | DSort | DNil | DRef _ | DInt _) as c -> c
    | DCtx (ctx,c) -> DCtx (f ctx, f c)
    | DLambda (t,c) -> DLambda (f t, f c)
    | DApp (t,u) -> DApp (f t,f u)
    | DCase (ci,p,c,bl) -> DCase (ci, f p, f c, Array.map f bl)
    | DFix (ia,i,ta,ca) ->
	DFix (ia,i,Array.map f ta,Array.map f ca)
    | DCoFix(i,ta,ca) ->
	DCoFix (i,Array.map f ta,Array.map f ca)
    | DCons ((t,topt),u) -> DCons ((f t,Option.map f topt), f u)

  let compare_ci ci1 ci2 =
    let c = ind_ord ci1.ci_ind ci2.ci_ind in
    if c = 0 then
      let c = Int.compare ci1.ci_npar ci2.ci_npar in
      if c = 0 then
        let c = Array.compare Int.compare ci1.ci_cstr_ndecls ci2.ci_cstr_ndecls in
        if c = 0 then
          Array.compare Int.compare ci1.ci_cstr_nargs ci2.ci_cstr_nargs
        else c
      else c
    else c

  let compare cmp t1 t2 = match t1, t2 with
  | DRel, DRel -> 0
  | DRel, _ -> -1 | _, DRel -> 1
  | DSort, DSort -> 0
  | DSort, _ -> -1 | _, DSort -> 1
  | DRef gr1, DRef gr2 -> GlobRef.Ordered.compare gr1 gr2
  | DRef _, _ -> -1 | _, DRef _ -> 1

  | DCtx (tl1, tr1), DCtx (tl2, tr2)
  | DLambda (tl1, tr1), DLambda (tl2, tr2)
  | DApp (tl1, tr1), DApp (tl2, tr2) ->
    let c = cmp tl1 tl2 in
    if c = 0 then cmp tr1 tr2 else c
  | DCtx _, _ -> -1 | _, DCtx _ -> 1
  | DLambda _, _ -> -1 | _, DLambda _ -> 1
  | DApp _, _ -> -1 | _, DApp _ -> 1

  | DCase (ci1, c1, t1, p1), DCase (ci2, c2, t2, p2) ->
    let c = cmp c1 c2 in
    if c = 0 then
      let c = cmp t1 t2 in
      if c = 0 then
        let c = Array.compare cmp p1 p2 in
        if c = 0 then compare_ci ci1 ci2
        else c
      else c
    else c
  | DCase _, _ -> -1 | _, DCase _ -> 1

  | DFix (i1, j1, tl1, pl1), DFix (i2, j2, tl2, pl2) ->
    let c = Int.compare j1 j2 in
    if c = 0 then
      let c = Array.compare Int.compare i1 i2 in
      if c = 0 then
        let c = Array.compare cmp tl1 tl2 in
        if c = 0 then Array.compare cmp pl1 pl2
        else c
      else c
    else c
  | DFix _, _ -> -1 | _, DFix _ -> 1

  | DCoFix (i1, tl1, pl1), DCoFix (i2, tl2, pl2) ->
    let c = Int.compare i1 i2 in
    if c = 0 then
      let c = Array.compare cmp tl1 tl2 in
      if c = 0 then Array.compare cmp pl1 pl2
      else c
    else c
  | DCoFix _, _ -> -1 | _, DCoFix _ -> 1

  | DInt i1, DInt i2 -> Uint63.compare i1 i2

  | DInt _, _ -> -1 | _, DInt _ -> 1

  | DCons ((t1, ot1), u1), DCons ((t2, ot2), u2) ->
     let c = cmp t1 t2 in
     if Int.equal c 0 then
       let c = Option.compare cmp ot1 ot2 in
       if Int.equal c 0 then cmp u1 u2
       else c
     else c
  | DCons _, _ -> -1 | _, DCons _ -> 1

  | DNil, DNil -> 0

  let fold f acc = function
    | (DRel | DNil | DSort | DRef _ | DInt _) -> acc
    | DCtx (ctx,c) -> f (f acc ctx) c
    | DLambda (t,c) -> f (f acc t) c
    | DApp (t,u) -> f (f acc t) u
    | DCase (ci,p,c,bl) -> Array.fold_left f (f (f acc p) c) bl
    | DFix (ia,i,ta,ca) ->
	Array.fold_left f (Array.fold_left f acc ta) ca
    | DCoFix(i,ta,ca) ->
	Array.fold_left f (Array.fold_left f acc ta) ca
    | DCons ((t,topt),u) -> f (Option.fold_left f (f acc t) topt) u

  let choose f = function
    | (DRel | DSort | DNil | DRef _ | DInt _) -> invalid_arg "choose"
    | DCtx (ctx,c) -> f ctx
    | DLambda (t,c) -> f t
    | DApp (t,u) -> f u
    | DCase (ci,p,c,bl) -> f c
    | DFix (ia,i,ta,ca) -> f ta.(0)
    | DCoFix (i,ta,ca) -> f ta.(0)
    | DCons ((t,topt),u) -> f u

  let dummy_cmp () () = 0

  let fold2 (f:'a -> 'b -> 'c -> 'a) (acc:'a) (c1:'b t) (c2:'c t) : 'a =
    let head w = map (fun _ -> ()) w in
    if not (Int.equal (compare dummy_cmp (head c1) (head c2)) 0)
    then invalid_arg "fold2:compare" else
      match c1,c2 with
        | (DRel, DRel | DNil, DNil | DSort, DSort | DRef _, DRef _
           | DInt _, DInt _) -> acc
	| (DCtx (c1,t1), DCtx (c2,t2)
	  | DApp (c1,t1), DApp (c2,t2)
	  | DLambda (c1,t1), DLambda (c2,t2)) -> f (f acc c1 c2) t1 t2
	| DCase (ci,p1,c1,bl1),DCase (_,p2,c2,bl2) ->
	    Array.fold_left2 f (f (f acc p1 p2) c1 c2) bl1 bl2
	| DFix (ia,i,ta1,ca1), DFix (_,_,ta2,ca2) ->
	    Array.fold_left2 f (Array.fold_left2 f acc ta1 ta2) ca1 ca2
	| DCoFix(i,ta1,ca1), DCoFix(_,ta2,ca2) ->
	    Array.fold_left2 f (Array.fold_left2 f acc ta1 ta2) ca1 ca2
	| DCons ((t1,topt1),u1), DCons ((t2,topt2),u2) ->
	    f (Option.fold_left2 f (f acc t1 t2) topt1 topt2) u1 u2
        | (DRel | DNil | DSort | DRef _ | DCtx _ | DApp _ | DLambda _ | DCase _
           | DFix _ | DCoFix _ | DCons _ | DInt _), _ -> assert false

  let map2 (f:'a -> 'b -> 'c) (c1:'a t) (c2:'b t) : 'c t =
    let head w = map (fun _ -> ()) w in
    if not (Int.equal (compare dummy_cmp (head c1) (head c2)) 0)
    then invalid_arg "map2_t:compare" else
      match c1,c2 with
        | (DRel, DRel | DSort, DSort | DNil, DNil | DRef _, DRef _
           | DInt _, DInt _) as cc ->
	    let (c,_) = cc in c
	| DCtx (c1,t1), DCtx (c2,t2) -> DCtx (f c1 c2, f t1 t2)
	| DLambda (t1,c1), DLambda (t2,c2) -> DLambda (f t1 t2, f c1 c2)
	| DApp (t1,u1), DApp (t2,u2) -> DApp (f t1 t2,f u1 u2)
	| DCase (ci,p1,c1,bl1), DCase (_,p2,c2,bl2) ->
	    DCase (ci, f p1 p2, f c1 c2, Array.map2 f bl1 bl2)
	| DFix (ia,i,ta1,ca1), DFix (_,_,ta2,ca2) ->
	    DFix (ia,i,Array.map2 f ta1 ta2,Array.map2 f ca1 ca2)
	| DCoFix (i,ta1,ca1), DCoFix (_,ta2,ca2) ->
	    DCoFix (i,Array.map2 f ta1 ta2,Array.map2 f ca1 ca2)
	| DCons ((t1,topt1),u1), DCons ((t2,topt2),u2) ->
	    DCons ((f t1 t2,Option.lift2 f topt1 topt2), f u1 u2)
        | (DRel | DNil | DSort | DRef _ | DCtx _ | DApp _ | DLambda _ | DCase _
           | DFix _ | DCoFix _ | DCons _ | DInt _), _ -> assert false

  let terminal = function
    | (DRel | DSort | DNil | DRef _ | DInt _) -> true
    | DLambda _ | DApp _ | DCase _ | DFix _ | DCoFix _ | DCtx _ | DCons _ ->
      false

  let compare t1 t2 = compare dummy_cmp t1 t2

end

(*
 * Terms discrimination nets
 * Uses the general dnet datatype on DTerm.t
 * (here you can restart reading)
 *)

(*
 * Construction of the module
 *)

module type IDENT =
sig
  type t
  val compare : t -> t -> int
  val subst : substitution -> t -> t
  val constr_of : t -> constr
end

module type OPT =
sig
  val reduce : constr -> constr
  val direction : bool
end

module Make =
  functor (Ident : IDENT) ->
  functor (Opt : OPT) ->
struct

  module TDnet : Dnet.S with type ident=Ident.t
			and  type 'a structure = 'a DTerm.t
			and  type meta = int
    = Dnet.Make(DTerm)(Ident)(Int)

  type t = TDnet.t

  type ident = TDnet.ident

  (** We will freshen metas on the fly, to cope with the implementation defect
      of Term_dnet which requires metas to be all distinct. *)
  let fresh_meta =
    let index = ref 0 in
    fun () ->
      let ans = !index in
      let () = index := succ ans in
      ans

  open DTerm
  open TDnet

  let pat_of_constr c : term_pattern =
    (* To each evar we associate a unique identifier. *)
    let metas = ref Evar.Map.empty in
    let rec pat_of_constr c = match Constr.kind c with
    | Rel _          -> Term DRel
    | Sort _         -> Term DSort
    | Var i          -> Term (DRef (VarRef i))
    | Const (c,u)    -> Term (DRef (ConstRef c))
    | Ind (i,u)      -> Term (DRef (IndRef i))
    | Construct (c,u)-> Term (DRef (ConstructRef c))
    | Meta _         -> assert false
    | Evar (i,_)     ->
      let meta =
        try Evar.Map.find i !metas
        with Not_found ->
          let meta = fresh_meta () in
          let () = metas := Evar.Map.add i meta !metas in
          meta
      in
      Meta meta
    | Case (ci,c1,c2,ca)     ->
      Term(DCase(ci,pat_of_constr c1,pat_of_constr c2,Array.map pat_of_constr ca))
    | Fix ((ia,i),(_,ta,ca)) ->
      Term(DFix(ia,i,Array.map pat_of_constr ta, Array.map pat_of_constr ca))
    | CoFix (i,(_,ta,ca))    ->
      Term(DCoFix(i,Array.map pat_of_constr ta,Array.map pat_of_constr ca))
    | Cast (c,_,_)   -> pat_of_constr c
    | Lambda (_,t,c) -> Term(DLambda (pat_of_constr t, pat_of_constr c))
    | (Prod (_,_,_) | LetIn(_,_,_,_))   ->
      let (ctx,c) = ctx_of_constr (Term DNil) c in Term (DCtx (ctx,c))
    | App (f,ca)     ->
      Array.fold_left (fun c a -> Term (DApp (c,a)))
        (pat_of_constr f) (Array.map pat_of_constr ca)
    | Proj (p,c) -> 
        Term (DApp (Term (DRef (ConstRef (Projection.constant p))), pat_of_constr c))
    | Int i -> Term (DInt i)

    and ctx_of_constr ctx c = match Constr.kind c with
    | Prod (_,t,c)   -> ctx_of_constr (Term(DCons((pat_of_constr t,None),ctx))) c
    | LetIn(_,d,t,c) -> ctx_of_constr (Term(DCons((pat_of_constr t, Some (pat_of_constr d)),ctx))) c
    | _ -> ctx,pat_of_constr c
    in
    pat_of_constr c

  let empty_ctx : term_pattern -> term_pattern = function
    | Meta _ as c -> c
    | Term (DCtx(_,_)) as c -> c
    | c -> Term (DCtx (Term DNil, c))

  (*
   * Basic primitives
   *)

  let empty = TDnet.empty

  let subst s t =
    let sleaf id = Ident.subst s id in
    let snode = function
      | DTerm.DRef gr -> DTerm.DRef (fst (subst_global s gr))
      | n -> n in
    TDnet.map sleaf snode t

  let union = TDnet.union

  let add (c:constr) (id:Ident.t) (dn:t) =
    let c = Opt.reduce c in
    let c = empty_ctx (pat_of_constr c) in
    TDnet.add dn c id


  let new_meta () = Meta (fresh_meta ())

  let rec remove_cap : term_pattern -> term_pattern = function
    | Term (DCons (t,u)) -> Term (DCons (t,remove_cap u))
    | Term DNil -> new_meta()
    | Meta _ as m -> m
    | _ -> assert false

  let under_prod : term_pattern -> term_pattern = function
    | Term (DCtx (t,u)) -> Term (DCtx (remove_cap t,u))
    | Meta m -> Term (DCtx(new_meta(), Meta m))
    | _ -> assert false

  (* debug *)
(*  let rec pr_term_pattern p =
    (fun pr_t -> function
       | Term t -> pr_t t
       | Meta m -> str"["++Pp.int (Obj.magic m)++str"]"
    ) (pr_dconstr pr_term_pattern) p*)

  let search_pat cpat dpat dn =
    let whole_c = EConstr.of_constr cpat in
    (* if we are at the root, add an empty context *)
    let dpat = under_prod (empty_ctx dpat) in
    TDnet.Idset.fold
      (fun id acc ->
	 let c_id = Opt.reduce (Ident.constr_of id) in
	 let c_id = EConstr.of_constr c_id in
	 let (ctx,wc) =
           try Termops.align_prod_letin Evd.empty whole_c c_id (* FIXME *)
	   with Invalid_argument _ -> [],c_id in
	 let wc,whole_c = if Opt.direction then whole_c,wc else wc,whole_c in
	 try
          let _ = Termops.filtering Evd.empty ctx Reduction.CUMUL wc whole_c in
          id :: acc
	 with Termops.CannotFilter -> (* msgnl(str"recon "++Termops.print_constr_env (Global.env()) wc); *) acc
      ) (TDnet.find_match dpat dn) []

  (*
   * High-level primitives describing specific search problems
   *)

  let search_pattern dn pat =
    let pat = Opt.reduce pat in
    search_pat pat (empty_ctx (pat_of_constr pat)) dn

  let find_all dn = Idset.elements (TDnet.find_all dn)

  let map f dn = TDnet.map f (fun x -> x) dn

  let refresh_metas dn =
    let new_metas = ref Int.Map.empty in
    let refresh_one_meta i =
      try Int.Map.find i !new_metas
      with Not_found ->
        let new_meta = fresh_meta () in
        let () = new_metas := Int.Map.add i new_meta !new_metas in
        new_meta
    in
    TDnet.map_metas refresh_one_meta dn
end

module type S =
sig
  type t
  type ident

  val empty : t
  val add : constr -> ident -> t -> t
  val union : t -> t -> t
  val subst : substitution -> t -> t
  val search_pattern : t -> constr -> ident list
  val find_all : t -> ident list
  val map : (ident -> ident) -> t -> t
  val refresh_metas : t -> t
end
