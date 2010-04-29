(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i*)
open Util
open Term
open Sign
open Names
open Libnames
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
    | DRef    of global_reference
    | DCtx    of 't * 't (* (binding list, subterm) = Prods and LetIns *)
    | DLambda of 't * 't
    | DApp    of 't * 't (* binary app *)
    | DCase   of case_info * 't * 't * 't array
    | DFix    of int array * int * 't array * 't array
    | DCoFix  of int * 't array * 't array

    (* special constructors only inside the left-hand side of DCtx or
       DApp. Used to encode lists of foralls/letins/apps as contexts *)
    | DCons   of ('t * 't option) * 't
    | DNil

  type dconstr = dconstr t

  (* debug *)
  let rec pr_dconstr f : 'a t -> std_ppcmds = function
    | DRel -> str "*"
    | DSort -> str "Sort"
    | DRef _ -> str "Ref"
    | DCtx (ctx,t) -> f ctx ++ spc() ++ str "|-" ++ spc () ++ f t
    | DLambda (t1,t2) -> str "fun"++ spc() ++ f t1 ++ spc() ++ str"->" ++ spc() ++ f t2
    | DApp (t1,t2) -> f t1 ++ spc() ++ f t2
    | DCase (_,t1,t2,ta) -> str "case"
    | DFix _ -> str "fix"
    | DCoFix _ -> str "cofix"
    | DCons ((t,dopt),tl) -> f t ++ (match dopt with
	  Some t' -> str ":=" ++ f t'
	| None -> str "") ++ spc() ++ str "::" ++ spc() ++ f tl
    | DNil -> str "[]"

  (*
   * Functional iterators for the t datatype
   * a.k.a boring and error-prone boilerplate code
   *)

  let map f = function
    | (DRel | DSort | DNil | DRef _) as c -> c
    | DCtx (ctx,c) -> DCtx (f ctx, f c)
    | DLambda (t,c) -> DLambda (f t, f c)
    | DApp (t,u) -> DApp (f t,f u)
    | DCase (ci,p,c,bl) -> DCase (ci, f p, f c, Array.map f bl)
    | DFix (ia,i,ta,ca) ->
	DFix (ia,i,Array.map f ta,Array.map f ca)
    | DCoFix(i,ta,ca) ->
	DCoFix (i,Array.map f ta,Array.map f ca)
    | DCons ((t,topt),u) -> DCons ((f t,Option.map f topt), f u)

  let compare x y =
    let make_name n =
      match n with
	| DRef(ConstRef con) ->
	    DRef(ConstRef(constant_of_kn(canonical_con con)))
	| DRef(IndRef (kn,i)) ->
	    DRef(IndRef(mind_of_kn(canonical_mind kn),i))
	| DRef(ConstructRef ((kn,i),j ))->
	    DRef(ConstructRef((mind_of_kn(canonical_mind kn),i),j))
	| k -> k in
    Pervasives.compare (make_name x) (make_name y)

  let fold f acc = function
    | (DRel | DNil | DSort | DRef _) -> acc
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
    | (DRel | DSort | DNil | DRef _) -> invalid_arg "choose"
    | DCtx (ctx,c) -> f ctx
    | DLambda (t,c) -> f t
    | DApp (t,u) -> f u
    | DCase (ci,p,c,bl) -> f c
    | DFix (ia,i,ta,ca) -> f ta.(0)
    | DCoFix (i,ta,ca) -> f ta.(0)
    | DCons ((t,topt),u) -> f u

  let fold2 (f:'a -> 'b -> 'c -> 'a) (acc:'a) (c1:'b t) (c2:'c t) : 'a =
    let head w = map (fun _ -> ()) w in
    if compare (head c1) (head c2) <> 0
    then invalid_arg "fold2:compare" else
      match c1,c2 with
	| (DRel, DRel | DNil, DNil | DSort, DSort | DRef _, DRef _) -> acc
	| (DCtx (c1,t1), DCtx (c2,t2)
	  | DApp (c1,t1), DApp (c2,t2)
	  | DLambda (c1,t1), DLambda (c2,t2)) -> f (f acc c1 c2) t1 t2
	| DCase (ci,p1,c1,bl1),DCase (_,p2,c2,bl2) ->
	    array_fold_left2 f (f (f acc p1 p2) c1 c2) bl1 bl2
	| DFix (ia,i,ta1,ca1), DFix (_,_,ta2,ca2) ->
	    array_fold_left2 f (array_fold_left2 f acc ta1 ta2) ca1 ca2
	| DCoFix(i,ta1,ca1), DCoFix(_,ta2,ca2) ->
	    array_fold_left2 f (array_fold_left2 f acc ta1 ta2) ca1 ca2
	| DCons ((t1,topt1),u1), DCons ((t2,topt2),u2) ->
	    f (Option.fold_left2 f (f acc t1 t2) topt1 topt2) u1 u2
	| _ -> assert false

  let map2 (f:'a -> 'b -> 'c) (c1:'a t) (c2:'b t) : 'c t =
    let head w = map (fun _ -> ()) w in
    if compare (head c1) (head c2) <> 0
    then invalid_arg "map2_t:compare" else
      match c1,c2 with
	| (DRel, DRel | DSort, DSort | DNil, DNil | DRef _, DRef _) as cc ->
	    let (c,_) = cc in c
	| DCtx (c1,t1), DCtx (c2,t2) -> DCtx (f c1 c2, f t1 t2)
	| DLambda (t1,c1), DLambda (t2,c2) -> DLambda (f t1 t2, f c1 c2)
	| DApp (t1,u1), DApp (t2,u2) -> DApp (f t1 t2,f u1 u2)
	| DCase (ci,p1,c1,bl1), DCase (_,p2,c2,bl2) ->
	    DCase (ci, f p1 p2, f c1 c2, array_map2 f bl1 bl2)
	| DFix (ia,i,ta1,ca1), DFix (_,_,ta2,ca2) ->
	    DFix (ia,i,array_map2 f ta1 ta2,array_map2 f ca1 ca2)
	| DCoFix (i,ta1,ca1), DCoFix (_,ta2,ca2) ->
	    DCoFix (i,array_map2 f ta1 ta2,array_map2 f ca1 ca2)
	| DCons ((t1,topt1),u1), DCons ((t2,topt2),u2) ->
	    DCons ((f t1 t2,Option.lift2 f topt1 topt2), f u1 u2)
	| _ -> assert false

  let terminal = function
    | (DRel | DSort | DNil | DRef _) -> true
    | _ -> false
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
			and  type meta = metavariable
    = Dnet.Make(DTerm)(Ident)
    (struct
       type t = metavariable
       let compare = Pervasives.compare
     end)

  type t = TDnet.t

  type ident = TDnet.ident

  type 'a pattern = 'a TDnet.pattern
  type term_pattern = term_pattern DTerm.t pattern

  type idset = TDnet.Idset.t

  type result = ident * (constr*existential_key) * Termops.subst

  open DTerm
  open TDnet

  let rec pat_of_constr c : term_pattern =
    match kind_of_term c with
      | Rel _          -> Term DRel
      | Sort _         -> Term DSort
      | Var i          -> Term (DRef (VarRef i))
      | Const c        -> Term (DRef (ConstRef c))
      | Ind i          -> Term (DRef (IndRef i))
      | Construct c    -> Term (DRef (ConstructRef c))
      | Term.Meta _    -> assert false
      | Evar (i,_)     -> Meta i
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

  and ctx_of_constr ctx c : term_pattern * term_pattern =
    match kind_of_term c with
      | Prod (_,t,c)   -> ctx_of_constr (Term(DCons((pat_of_constr t,None),ctx))) c
      | LetIn(_,d,t,c) -> ctx_of_constr (Term(DCons((pat_of_constr t, Some (pat_of_constr d)),ctx))) c
      | _ -> ctx,pat_of_constr c

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

  let new_meta_no =
    let ctr = ref 0 in
    fun () -> decr ctr; !ctr

  let new_meta_no = Evarutil.new_untyped_evar

  let neutral_meta = new_meta_no()

  let new_meta () = Meta (new_meta_no())
  let new_evar () = mkEvar(new_meta_no(),[||])

  let rec remove_cap : term_pattern -> term_pattern = function
    | Term (DCons (t,u)) -> Term (DCons (t,remove_cap u))
    | Term DNil -> new_meta()
    | Meta _ as m -> m
    | _ -> assert false

  let under_prod : term_pattern -> term_pattern = function
    | Term (DCtx (t,u)) -> Term (DCtx (remove_cap t,u))
    | Meta m -> Term (DCtx(new_meta(), Meta m))
    | _ -> assert false

  let init = let e = new_meta_no() in (mkEvar (e,[||]),e)

  let rec e_subst_evar i (t:unit->constr) c =
    match kind_of_term c with
    | Evar (j,_) when i=j -> t()
    | _ -> map_constr (e_subst_evar i t) c

  let subst_evar i c = e_subst_evar i (fun _ -> c)

  (* debug *)
  let rec pr_term_pattern p =
    (fun pr_t -> function
       | Term t -> pr_t t
       | Meta m -> str"["++Util.pr_int (Obj.magic m)++str"]"
    ) (pr_dconstr pr_term_pattern) p

  let search_pat cpat dpat dn (up,plug) =
    let whole_c = subst_evar plug cpat up in
    (* if we are at the root, add an empty context *)
    let dpat = if isEvar_or_Meta up then under_prod (empty_ctx dpat) else dpat in
    TDnet.Idset.fold
      (fun id acc ->
	 let c_id = Opt.reduce (Ident.constr_of id) in
	 let (ctx,wc) =
	   try Termops.align_prod_letin whole_c c_id
	   with Invalid_argument _ -> [],c_id in
	 let up = it_mkProd_or_LetIn up ctx in
	 let wc,whole_c = if Opt.direction then whole_c,wc else wc,whole_c in
	 try (id,(up,plug),Termops.filtering ctx Reduction.CUMUL wc whole_c)::acc
	 with Termops.CannotFilter -> (* msgnl(str"recon "++Termops.print_constr_env (Global.env()) wc); *) acc
      ) (TDnet.find_match dpat dn) []

  let fold_pattern_neutral f =
    fold_pattern (fun acc (mset,m,dn) -> if m=neutral_meta then acc else f m dn acc)

  let fold_pattern_nonlin f =
    let defined = ref Gmap.empty in
    fold_pattern_neutral
      ( fun m dn acc ->
	 let dn = try TDnet.inter dn (Gmap.find m !defined) with Not_found -> dn in
	 defined := Gmap.add m dn !defined;
	 f m dn acc )

  let fold_pattern_up f acc dpat cpat dn (up,plug) =
    fold_pattern_nonlin
      ( fun m dn acc ->
	  f dn (subst_evar plug (e_subst_evar neutral_meta new_evar cpat) up, m) acc
      ) acc dpat dn

  let possibly_under pat k dn (up,plug) =
    let rec aux fst dn (up,plug) acc =
      let cpat = pat() in
      let dpat = pat_of_constr cpat in
      let dpat = if fst then under_prod (empty_ctx dpat) else dpat in
	(k dn (up,plug)) @
	  snd (fold_pattern_up (aux false) acc dpat cpat dn (up,plug)) in
      aux true dn (up,plug) []

  let eq_pat eq () = mkApp(eq,[|mkEvar(neutral_meta,[||]);new_evar();new_evar()|])
  let app_pat () = mkApp(new_evar(),[|mkEvar(neutral_meta,[||])|])

  (*
   * High-level primitives describing specific search problems
   *)

  let search_pattern dn pat =
    let pat = Opt.reduce pat in
    search_pat pat (empty_ctx (pat_of_constr pat)) dn init

  let search_concl dn pat =
    let pat = Opt.reduce pat in
    search_pat pat (under_prod (empty_ctx (pat_of_constr pat))) dn init

  let search_eq_concl dn eq pat =
    let pat = Opt.reduce pat in
    let eq_pat = eq_pat eq () in
    let eq_dpat = under_prod (empty_ctx (pat_of_constr eq_pat)) in
    snd (fold_pattern_up
      (fun dn up acc ->
	 search_pat pat (pat_of_constr pat) dn up @ acc
      ) [] eq_dpat eq_pat dn init)

   let search_head_concl dn pat =
    let pat = Opt.reduce pat in
    possibly_under app_pat (search_pat pat (pat_of_constr pat)) dn init

  let find_all dn = Idset.elements (TDnet.find_all dn)

  let map f dn = TDnet.map f (fun x -> x) dn
end

module type S =
sig
  type t
  type ident

  type result = ident * (constr*existential_key) * Termops.subst

  val empty : t
  val add : constr -> ident -> t -> t
  val union : t -> t -> t
  val subst : substitution -> t -> t
  val search_pattern : t -> constr -> result list
  val search_concl : t -> constr -> result list
  val search_head_concl : t -> constr -> result list
  val search_eq_concl : t -> constr -> constr -> result list
  val find_all : t -> ident list
  val map : (ident -> ident) -> t -> t
end
