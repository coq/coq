
(* $Id$ *)

(* This module instanciates the structure of generic deBruijn terms to Coq *)

open Util
open Pp
open Names
open Univ

(* Coq abstract syntax with deBruijn variables; 'a is the type of sorts *)

type existential_key = int

(* This defines Cases annotations *)
type pattern_source = DefaultPat of int | RegularPat
type case_style = PrintLet | PrintIf | PrintCases
type case_printing =
    inductive_path * identifier array * int
    * case_style option * pattern_source array
type case_info = int array * case_printing

(* Sorts. *)

type contents = Pos | Null

type sorts =
  | Prop of contents                      (* proposition types *)
  | Type of universe
      
let mk_Set  = Prop Pos
let mk_Prop = Prop Null

let print_sort = function
  | Prop Pos -> [< 'sTR "Set" >]
  | Prop Null -> [< 'sTR "Prop" >]
  | Type _ -> [< 'sTR "Type" >]

(********************************************************************)
(* type of global reference *)

type global_reference =
  | VarRef of section_path
  | ConstRef of constant_path
  | IndRef of inductive_path
  | ConstructRef of constructor_path

(********************************************************************)
(*       Constructions as implemented                               *)
(********************************************************************)

(* I would like the internal representation of constr hidden in a
module but ocaml does not allow then to export Internal.kind_of_term
as kind_of_term with the same constructors as Internal.kind_of_term !! *)

(* What is intended ...

module type InternalSig = sig

type constr
type existential = existential_key * constr array
type constant = section_path * constr array
type constructor = constructor_path * constr array
type inductive = inductive_path * constr array
type rec_declaration = constr array * name list * constr array
type fixpoint = (int array * int) * rec_declaration
type cofixpoint = int * rec_declaration

type kind_of_term =
  | IsRel          of int
  | IsMeta         of int
  | IsVar          of identifier
  | IsXtra         of string
  | IsSort         of sorts
  | IsCast         of constr * constr
  | IsProd         of name * constr * constr
  | IsLambda       of name * constr * constr
  | IsLetIn        of name * constr * constr * constr
  | IsApp         of constr * constr array
  | IsEvar         of existential
  | IsConst        of constant
  | IsMutInd       of inductive
  | IsMutConstruct of constructor
  | IsMutCase      of case_info * constr * constr * constr array
  | IsFix          of fixpoint
  | IsCoFix        of cofixpoint

val mkRel : int -> constr
val mkMeta : int -> constr
val mkVar : identifier -> constr
val mkXtra : string -> constr
val mkSort : sorts -> constr
val mkCast : constr * constr -> constr
val mkProd : name * constr * constr -> constr
val mkLambda : name * constr * constr -> constr
val mkLetIn : name * constr * constr * constr -> constr
val mkApp : constr * constr array -> constr
val mkEvar : existential -> constr
val mkConst : constant -> constr
val mkMutInd : inductive -> constr
val mkMutConstruct : constructor -> constr
val mkMutCase : case_info * constr * constr * constr array -> constr
val mkFix : fixpoint -> constr
val mkCoFix : cofixpoint -> constr

val kind_of_term : constr -> kind_of_term

val hcons_term : 
  (sorts -> sorts) * (section_path -> section_path) *
  (name -> name) * (identifier -> identifier) * (string -> string)
  -> constr -> constr
end

END of intended signature of internal constr 
*)

(*
module Internal : InternalSig =
struct
*)

type constr = kind_of_term

and existential = existential_key * constr array
and constant = constant_path * constr array
and constructor = constructor_path * constr array
and inductive = inductive_path * constr array
and rec_declaration = constr array * name list * constr array
and fixpoint = (int array * int) * rec_declaration
and cofixpoint = int * rec_declaration

and kind_of_term =
  | IsRel          of int
  | IsMeta         of int
  | IsVar          of identifier
  | IsXtra         of string
  | IsSort         of sorts
  | IsCast         of constr * constr
  | IsProd         of name * constr * constr
  | IsLambda       of name * constr * constr
  | IsLetIn        of name * constr * constr * constr
  | IsApp         of constr * constr array
  | IsEvar         of existential
  | IsConst        of constant
  | IsMutInd       of inductive
  | IsMutConstruct of constructor
  | IsMutCase      of case_info * constr * constr * constr array
  | IsFix          of fixpoint
  | IsCoFix        of cofixpoint

(***************************)
(* hash-consing functions  *)                         
(***************************)

let comp_term t1 t2 =
  match t1, t2 with
  | IsRel n1, IsRel n2 -> n1 = n2
  | IsMeta m1, IsMeta m2 -> m1 = m2
  | IsVar id1, IsVar id2 -> id1 == id2
  | IsSort s1, IsSort s2 -> s1 == s2
  | IsXtra s1, IsXtra s2 -> s1 == s2
  | IsCast (c1,t1), IsCast (c2,t2) -> c1 == c2 & t1 == t2
  | IsProd (n1,t1,c1), IsProd (n2,t2,c2) -> n1 == n2 & t1 == t2 & c1 == c2
  | IsLambda (n1,t1,c1), IsLambda (n2,t2,c2) -> n1 == n2 & t1 == t2 & c1 == c2
  | IsLetIn (n1,b1,t1,c1), IsLetIn (n2,b2,t2,c2) ->
      n1 == n2 & b1 == b2 & t1 == t2 & c1 == c2
  | IsApp (c1,l1), IsApp (c2,l2) -> c1 == c2 & array_for_all2 (==) l1 l2
  | IsEvar (e1,l1), IsEvar (e2,l2) -> e1 = e2 & array_for_all2 (==) l1 l2
  | IsConst (c1,l1), IsConst (c2,l2) -> c1 == c2 & array_for_all2 (==) l1 l2
  | IsMutInd (c1,l1), IsMutInd (c2,l2) -> c1 == c2 & array_for_all2 (==) l1 l2
  | IsMutConstruct (c1,l1), IsMutConstruct (c2,l2) ->
      c1 == c2 & array_for_all2 (==) l1 l2
  | IsMutCase (ci1,p1,c1,bl1), IsMutCase (ci2,p2,c2,bl2) ->
      ci1 == ci2 & p1 == p2 & c1 == c2 & array_for_all2 (==) bl1 bl2
  | IsFix (ln1,(tl1,lna1,bl1)), IsFix (ln2,(tl2,lna2,bl2)) ->
      lna1 == lna2 & ln1 = ln2
      & array_for_all2 (==) tl1 tl2 & array_for_all2 (==) bl1 bl2
  | IsCoFix(ln1,(tl1,lna1,bl1)), IsCoFix(ln2,(tl2,lna2,bl2)) ->
      lna1 == lna2 & ln1 = ln2
      & array_for_all2 (==) tl1 tl2 & array_for_all2 (==) bl1 bl2
  | _ -> false

let hash_term (sh_rec,(sh_sort,sh_sp,sh_na,sh_id,sh_str)) t =
  match t with
  | IsRel _ | IsMeta _ -> t
  | IsVar x -> IsVar (sh_id x)
  | IsSort s -> IsSort (sh_sort s)
  | IsXtra s -> IsXtra (sh_str s)
  | IsCast (c,t) -> IsCast (sh_rec c, sh_rec t)
  | IsProd (na,t,c) -> IsProd (sh_na na, sh_rec t, sh_rec c)
  | IsLambda (na,t,c) -> IsLambda (sh_na na, sh_rec t, sh_rec c)
  | IsLetIn (na,b,t,c) -> IsLetIn (sh_na na, sh_rec b, sh_rec t, sh_rec c)
  | IsApp (c,l) -> IsApp (sh_rec c, Array.map sh_rec l)
  | IsEvar (e,l) -> IsEvar (e, Array.map sh_rec l)
  | IsConst (c,l) -> IsConst (sh_sp c, Array.map sh_rec l)
  | IsMutInd ((sp,i),l) -> IsMutInd ((sh_sp sp,i), Array.map sh_rec l)
  | IsMutConstruct (((sp,i),j),l) ->
      IsMutConstruct (((sh_sp sp,i),j), Array.map sh_rec l)
  | IsMutCase (ci,p,c,bl) -> (* TO DO: extract ind_sp *)
      IsMutCase (ci, sh_rec p, sh_rec c, Array.map sh_rec bl)
  | IsFix (ln,(tl,lna,bl)) ->
      IsFix (ln,(Array.map sh_rec tl,List.map sh_na lna,Array.map sh_rec bl))
  | IsCoFix(ln,(tl,lna,bl)) ->
      IsCoFix (ln,(Array.map sh_rec tl,List.map sh_na lna,Array.map sh_rec bl))

module Hconstr =
  Hashcons.Make(
    struct
      type t = constr
      type u = (constr -> constr) *
               ((sorts -> sorts) * (section_path -> section_path)
		* (name -> name) * (identifier -> identifier)
		* (string -> string))
      let hash_sub = hash_term
      let equal = comp_term
      let hash = Hashtbl.hash
    end)

let hcons_term (hsorts,hsp,hname,hident,hstr) =
  Hashcons.recursive_hcons Hconstr.f (hsorts,hsp,hname,hident,hstr)

(* Constructs a DeBrujin index with number n *)
let mkRel   n = IsRel n

(* Constructs an existential variable named "?n" *)
let mkMeta  n =  IsMeta n

(* Constructs a Variable named id *)
let mkVar id = IsVar id

(* Construct an XTRA term (XTRA is an extra slot for whatever you want) *)
let mkXtra s = IsXtra s

(* Construct a type *)
let mkSort s = IsSort s
(* Constructs the term t1::t2, i.e. the term t1 casted with the type t2 *)
(* (that means t2 is declared as the type of t1) *)
let mkCast (t1,t2) =
  match t1 with
    | IsCast (t,_) -> IsCast (t,t2)
    | _ -> IsCast (t1,t2)

(* Constructs the product (x:t1)t2 *)
let mkProd (x,t1,t2) = IsProd (x,t1,t2)

(* Constructs the abstraction [x:t1]t2 *)
let mkLambda (x,t1,t2) = IsLambda (x,t1,t2)

(* Constructs [x=c_1:t]c_2 *)
let mkLetIn (x,c1,t,c2) = IsLetIn (x,c1,t,c2)

(* If lt = [t1; ...; tn], constructs the application (t1 ... tn) *)
(* We ensure applicative terms have at most one arguments and the
   function is not itself an applicative term *)
let mkApp (f, a) = 
  if a=[||] then f else
    match f with
      | IsApp (g, cl) -> IsApp (g, Array.append cl a)
      | _ -> IsApp (f, a)


(* Constructs a constant *) 
(* The array of terms correspond to the variables introduced in the section *)
let mkConst c = IsConst c

(* Constructs an existential variable *)
let mkEvar e = IsEvar e

(* Constructs the ith (co)inductive type of the block named sp *)
(* The array of terms correspond to the variables introduced in the section *)
let mkMutInd m = IsMutInd m

(* Constructs the jth constructor of the ith (co)inductive type of the 
   block named sp. The array of terms correspond to the variables
   introduced in the section *)
let mkMutConstruct c = IsMutConstruct c

(* Constructs the term <p>Case c of c1 | c2 .. | cn end *)
let mkMutCase (ci, p, c, ac) = IsMutCase (ci, p, c, ac)

let mkFix fix = IsFix fix

let mkCoFix cofix = IsCoFix cofix

let kind_of_term c = c

(*
end
END of expected but not allowed module (second variant) *)

(***********************************************************************)
(*    kind_of_term = constructions as seen by the user                 *)
(***********************************************************************)

(*
type constr = Internal.constr
type existential = Internal.existential
type constant = Internal.constant
type constructor = Internal.constructor
type inductive = Internal.inductive
type rec_declaration = Internal.rec_declaration
type fixpoint = Internal.fixpoint
type cofixpoint = Internal.cofixpoint

type kind_of_term = Internal.kindOfTerm

open Internal

END of expected re-export of Internal module *)

(* User view of [constr]. For [IsApp], it is ensured there is at
   least one argument and the function is not itself an applicative
   term *)

let kind_of_term = kind_of_term


(* En vue d'un kind_of_type : constr -> hnftype ??? *)
type hnftype =
  | HnfSort   of sorts
  | HnfProd   of name * constr * constr
  | HnfAtom   of constr
  | HnfMutInd of inductive * constr array

(**********************************************************************)
(*          Non primitive term destructors                            *)
(**********************************************************************)

(* Destructor operations : partial functions 
   Raise invalid_arg "dest*" if the const has not the expected form *)

(* Destructs a DeBrujin index *)
let destRel c = match kind_of_term c with
  | IsRel n -> n
  | _ -> invalid_arg "destRel"

(* Destructs an existential variable *)
let destMeta c = match kind_of_term c with
  | IsMeta n -> n
  | _ -> invalid_arg "destMeta"

let isMeta c = match kind_of_term c with IsMeta _ -> true | _ -> false

(* Destructs a variable *)
let destVar c = match kind_of_term c with
  | IsVar id -> id
  | _ -> invalid_arg "destVar"

(* Destructs an XTRA *)
let destXtra c = match kind_of_term c with
  | IsXtra s -> s
  | _ -> invalid_arg "destXtra"

(* Destructs a type *)
let isSort c = match kind_of_term c with
  | IsSort s -> true
  | _ -> false

let destSort c = match kind_of_term c with
  | IsSort s -> s
  | _ -> invalid_arg "destSort"

let rec isprop c = match kind_of_term c with
  | IsSort (Prop _) -> true
  | IsCast (c,_) -> isprop c
  | _ -> false

let rec is_Prop c = match kind_of_term c with
  | IsSort (Prop Null) -> true
  | IsCast (c,_) -> is_Prop c
  | _ -> false

let rec is_Set c = match kind_of_term c with
  | IsSort (Prop Pos) -> true
  | IsCast (c,_) -> is_Set c
  | _ -> false

let rec is_Type c = match kind_of_term c with
  | IsSort (Type _) -> true
  | IsCast (c,_) -> is_Type c
  | _ -> false

let isType = function
  | Type _ -> true
  | _ -> false

let is_small = function
  | Prop _ -> true
  | _ -> false

let iskind c = isprop c or is_Type c

let same_kind c1 c2 = (isprop c1 & isprop c2) or (is_Type c1 & is_Type c2)

(* Destructs a casted term *)
let destCast c = match kind_of_term c with 
  | IsCast (t1, t2) -> (t1,t2)
  | _ -> invalid_arg "destCast"

let isCast c = match kind_of_term c with IsCast (_,_) -> true | _ -> false

(* Tests if a de Bruijn index *)
let isRel c = match kind_of_term c with IsRel _ -> true | _ -> false

(* Tests if a variable *)
let isVar c = match kind_of_term c with IsVar _ -> true | _ -> false

(* Destructs the product (x:t1)t2 *)
let destProd c = match kind_of_term c with 
  | IsProd (x,t1,t2) -> (x,t1,t2) 
  | _ -> invalid_arg "destProd"

(* Destructs the abstraction [x:t1]t2 *)
let destLambda c = match kind_of_term c with 
  | IsLambda (x,t1,t2) -> (x,t1,t2) 
  | _ -> invalid_arg "destLambda"

(* Destructs the let [x:=b:t1]t2 *)
let destLetIn c = match kind_of_term c with 
  | IsLetIn (x,b,t1,t2) -> (x,b,t1,t2) 
  | _ -> invalid_arg "destProd"

(* Destructs an application *)
let destApplication c = match kind_of_term c with
  | IsApp (f,a) -> (f, a)
  | _ -> invalid_arg "destApplication"

let isApp c = match kind_of_term c with IsApp _ -> true | _ -> false

(* Destructs a constant *)
let destConst c = match kind_of_term c with
  | IsConst (sp, a as r) -> r
  | _ -> invalid_arg "destConst"

let path_of_const c = match kind_of_term c with
  | IsConst (sp,_) -> sp
  | _ -> anomaly "path_of_const called with bad args"

let args_of_const c = match kind_of_term c with
  | IsConst (_,args) -> args
  | _ -> anomaly "args_of_const called with bad args"

let isConst c = match kind_of_term c with IsConst _ -> true | _ -> false

(* Destructs an existential variable *)
let destEvar c = match kind_of_term c with
  | IsEvar (sp, a as r) -> r
  | _ -> invalid_arg "destEvar"

let num_of_evar c = match kind_of_term c with
  | IsEvar (n, _) -> n
  | _ -> anomaly "num_of_evar called with bad args"

(* Destructs a (co)inductive type named sp *)
let destMutInd c = match kind_of_term c with
  | IsMutInd (sp, a as r) -> r
  | _ -> invalid_arg "destMutInd"
	
let op_of_mind c = match kind_of_term c with
  | IsMutInd (ind_sp,_) -> ind_sp
  | _ -> anomaly "op_of_mind called with bad args"

let args_of_mind c = match kind_of_term c with
  | IsMutInd (_,args) -> args
  | _ -> anomaly "args_of_mind called with bad args"

(* Destructs a constructor *)
let destMutConstruct c = match kind_of_term c with
  | IsMutConstruct (sp, a as r) -> r
  | _ -> invalid_arg "dest"

let op_of_mconstr c = match kind_of_term c with
  | IsMutConstruct (sp,_) -> sp
  | _ -> anomaly "op_of_mconstr called with bad args"

let args_of_mconstr c = match kind_of_term c with
  | IsMutConstruct (_,args) -> args
  | _ -> anomaly "args_of_mconstr called with bad args"

let isMutConstruct c = match kind_of_term c with
    IsMutConstruct _ -> true | _ -> false

(* Destructs a term <p>Case c of lc1 | lc2 .. | lcn end *)
let destCase c = match kind_of_term c with
  | IsMutCase (ci,p,c,v) -> (ci,p,c,v)
  | _ -> anomaly "destCase"

let destFix c = match kind_of_term c with 
  | IsFix ((recindxs,i),(types,funnames,bodies) as fix) -> fix
  | _ -> invalid_arg "destFix"
	
let destCoFix c = match kind_of_term c with 
  | IsCoFix (i,(types,funnames,bodies) as cofix) -> cofix
  | _ -> invalid_arg "destCoFix"

(****************************************************************************)
(*              Functions to recur through subterms                         *)
(****************************************************************************)

(* [fold_constr f acc c] folds [f] on the immediate subterms of [c]
   starting from [acc] and proceeding from left to right according to
   the usual representation of the constructions; it is not recursive *)

let fold_constr f acc c = match kind_of_term c with
  | IsRel _ | IsMeta _ | IsVar _   | IsSort _  | IsXtra _ -> acc
  | IsCast (c,t) -> f (f acc c) t
  | IsProd (_,t,c) -> f (f acc t) c
  | IsLambda (_,t,c) -> f (f acc t) c
  | IsLetIn (_,b,t,c) -> f (f (f acc b) t) c
  | IsApp (c,l) -> Array.fold_left f (f acc c) l
  | IsEvar (_,l) -> Array.fold_left f acc l
  | IsConst (_,l) -> Array.fold_left f acc l
  | IsMutInd (_,l) -> Array.fold_left f acc l
  | IsMutConstruct (_,l) -> Array.fold_left f acc l
  | IsMutCase (_,p,c,bl) -> Array.fold_left f (f (f acc p) c) bl
  | IsFix (_,(tl,_,bl)) ->
      array_fold_left2 (fun acc b t -> f (f acc b) t) acc bl tl
  | IsCoFix (_,(tl,_,bl)) ->
      array_fold_left2 (fun acc b t -> f (f acc b) t) acc bl tl

(* [fold_constr_with_binders g f n acc c] folds [f n] on the immediate
   subterms of [c] starting from [acc] and proceeding from left to
   right according to the usual representation of the constructions as
   [fold_constr] but it carries an extra data [n] (typically a lift
   index) which is processed by [g] (which typically add 1 to [n]) at
   each binder traversal; it is not recursive *)

let fold_constr_with_binders g f n acc c = match kind_of_term c with
  | IsRel _ | IsMeta _ | IsVar _   | IsSort _  | IsXtra _ -> acc
  | IsCast (c,t) -> f n (f n acc c) t
  | IsProd (_,t,c) -> f (g n) (f n acc t) c
  | IsLambda (_,t,c) -> f (g n) (f n acc t) c
  | IsLetIn (_,b,t,c) -> f (g n) (f n (f n acc b) t) c
  | IsApp (c,l) -> Array.fold_left (f n) (f n acc c) l
  | IsEvar (_,l) -> Array.fold_left (f n) acc l
  | IsConst (_,l) -> Array.fold_left (f n) acc l
  | IsMutInd (_,l) -> Array.fold_left (f n) acc l
  | IsMutConstruct (_,l) -> Array.fold_left (f n) acc l
  | IsMutCase (_,p,c,bl) -> Array.fold_left (f n) (f n (f n acc p) c) bl
  | IsFix (_,(tl,_,bl)) -> 
      let n' = iterate g (Array.length tl) n in
      array_fold_left2 (fun acc b t -> f n (f n' acc b) t) acc bl tl
  | IsCoFix (_,(tl,_,bl)) ->
      let n' = iterate g (Array.length tl) n in
      array_fold_left2 (fun acc b t -> f n (f n' acc b) t) acc bl tl

(* [iter_constr f c] iters [f] on the immediate subterms of [c]; it is
   not recursive and the order with which subterms are processed is
   not specified *)

let iter_constr f c = match kind_of_term c with
  | IsRel _ | IsMeta _ | IsVar _   | IsSort _  | IsXtra _ -> ()
  | IsCast (c,t) -> f c; f t
  | IsProd (_,t,c) -> f t; f c
  | IsLambda (_,t,c) -> f t; f c
  | IsLetIn (_,b,t,c) -> f b; f t; f c
  | IsApp (c,l) -> f c; Array.iter f l
  | IsEvar (_,l) -> Array.iter f l
  | IsConst (_,l) -> Array.iter f l
  | IsMutInd (_,l) -> Array.iter f l
  | IsMutConstruct (_,l) -> Array.iter f l
  | IsMutCase (_,p,c,bl) -> f p; f c; Array.iter f bl
  | IsFix (_,(tl,_,bl)) -> Array.iter f tl; Array.iter f bl
  | IsCoFix (_,(tl,_,bl)) -> Array.iter f tl; Array.iter f bl

(* [iter_constr_with_binders g f n c] iters [f n] on the immediate
   subterms of [c]; it carries an extra data [n] (typically a lift
   index) which is processed by [g] (which typically add 1 to [n]) at
   each binder traversal; it is not recursive and the order with which
   subterms are processed is not specified *)

let iter_constr_with_binders g f n c = match kind_of_term c with
  | IsRel _ | IsMeta _ | IsVar _   | IsSort _  | IsXtra _ -> ()
  | IsCast (c,t) -> f n c; f n t
  | IsProd (_,t,c) -> f n t; f (g n) c
  | IsLambda (_,t,c) -> f n t; f (g n) c
  | IsLetIn (_,b,t,c) -> f n b; f n t; f (g n) c
  | IsApp (c,l) -> f n c; Array.iter (f n) l
  | IsEvar (_,l) -> Array.iter (f n) l
  | IsConst (_,l) -> Array.iter (f n) l
  | IsMutInd (_,l) -> Array.iter (f n) l
  | IsMutConstruct (_,l) -> Array.iter (f n) l
  | IsMutCase (_,p,c,bl) -> f n p; f n c; Array.iter (f n) bl
  | IsFix (_,(tl,_,bl)) -> 
      Array.iter (f n) tl; Array.iter (f (iterate g (Array.length tl) n)) bl
  | IsCoFix (_,(tl,_,bl)) ->
      Array.iter (f n) tl; Array.iter (f (iterate g (Array.length tl) n)) bl

(* [map_constr f c] maps [f] on the immediate subterms of [c]; it is
   not recursive and the order with which subterms are processed is
   not specified *)

let map_constr f c = match kind_of_term c with
  | IsRel _ | IsMeta _ | IsVar _   | IsSort _  | IsXtra _ -> c
  | IsCast (c,t) -> mkCast (f c, f t)
  | IsProd (na,t,c) -> mkProd (na, f t, f c)
  | IsLambda (na,t,c) -> mkLambda (na, f t, f c)
  | IsLetIn (na,b,t,c) -> mkLetIn (na, f b, f t, f c)
  | IsApp (c,l) -> mkApp (f c, Array.map f l)
  | IsEvar (e,l) -> mkEvar (e, Array.map f l)
  | IsConst (c,l) -> mkConst (c, Array.map f l)
  | IsMutInd (c,l) -> mkMutInd (c, Array.map f l)
  | IsMutConstruct (c,l) -> mkMutConstruct (c, Array.map f l)
  | IsMutCase (ci,p,c,bl) -> mkMutCase (ci, f p, f c, Array.map f bl)
  | IsFix (ln,(tl,lna,bl)) -> mkFix (ln,(Array.map f tl,lna,Array.map f bl))
  | IsCoFix(ln,(tl,lna,bl)) -> mkCoFix (ln,(Array.map f tl,lna,Array.map f bl))

(* [map_constr_with_binders g f n c] maps [f n] on the immediate
   subterms of [c]; it carries an extra data [n] (typically a lift
   index) which is processed by [g] (which typically add 1 to [n]) at
   each binder traversal; it is not recursive and the order with which
   subterms are processed is not specified *)

let map_constr_with_binders g f l c = match kind_of_term c with
  | IsRel _ | IsMeta _ | IsVar _   | IsSort _  | IsXtra _ -> c
  | IsCast (c,t) -> mkCast (f l c, f l t)
  | IsProd (na,t,c) -> mkProd (na, f l t, f (g l) c)
  | IsLambda (na,t,c) -> mkLambda (na, f l t, f (g l) c)
  | IsLetIn (na,b,t,c) -> mkLetIn (na, f l b, f l t, f (g l) c)
  | IsApp (c,al) -> mkApp (f l c, Array.map (f l) al)
  | IsEvar (e,al) -> mkEvar (e, Array.map (f l) al)
  | IsConst (c,al) -> mkConst (c, Array.map (f l) al)
  | IsMutInd (c,al) -> mkMutInd (c, Array.map (f l) al)
  | IsMutConstruct (c,al) -> mkMutConstruct (c, Array.map (f l) al)
  | IsMutCase (ci,p,c,bl) -> mkMutCase (ci, f l p, f l c, Array.map (f l) bl)
  | IsFix (ln,(tl,lna,bl)) ->
      let l' = iterate g (Array.length tl) l in
      mkFix (ln,(Array.map (f l) tl,lna,Array.map (f l') bl))
  | IsCoFix(ln,(tl,lna,bl)) ->
      let l' = iterate g (Array.length tl) l in
      mkCoFix (ln,(Array.map (f l) tl,lna,Array.map (f l') bl))

(* [map_constr_with_named_binders g f l c] maps [f l] on the immediate
   subterms of [c]; it carries an extra data [l] (typically a name
   list) which is processed by [g na] (which typically cons [na] to
   [l]) at each binder traversal (with name [na]); it is not recursive
   and the order with which subterms are processed is not specified *)

let map_constr_with_named_binders g f l c = match kind_of_term c with
  | IsRel _ | IsMeta _ | IsVar _   | IsSort _  | IsXtra _ -> c
  | IsCast (c,t) -> mkCast (f l c, f l t)
  | IsProd (na,t,c) -> mkProd (na, f l t, f (g na l) c)
  | IsLambda (na,t,c) -> mkLambda (na, f l t, f (g na l) c)
  | IsLetIn (na,b,t,c) -> mkLetIn (na, f l b, f l t, f (g na l) c)
  | IsApp (c,al) -> mkApp (f l c, Array.map (f l) al)
  | IsEvar (e,al) -> mkEvar (e, Array.map (f l) al)
  | IsConst (c,al) -> mkConst (c, Array.map (f l) al)
  | IsMutInd (c,al) -> mkMutInd (c, Array.map (f l) al)
  | IsMutConstruct (c,al) -> mkMutConstruct (c, Array.map (f l) al)
  | IsMutCase (ci,p,c,bl) -> mkMutCase (ci, f l p, f l c, Array.map (f l) bl)
  | IsFix (ln,(tl,lna,bl)) ->
      let l' = List.fold_right g lna l in
      mkFix (ln,(Array.map (f l) tl,lna,Array.map (f l') bl))
  | IsCoFix(ln,(tl,lna,bl)) ->
      let l' = List.fold_right g lna l in
      mkCoFix (ln,(Array.map (f l) tl,lna,Array.map (f l') bl))

(* [map_constr_with_binders_left_to_right g f n c] maps [f n] on the
   immediate subterms of [c]; it carries an extra data [n] (typically
   a lift index) which is processed by [g] (which typically add 1 to
   [n]) at each binder traversal; the subterms are processed from left
   to right according to the usual representation of the constructions
   (this may matter if [f] does a side-effect); it is not recursive;
   in fact, the usual representation of the constructions is at the
   time being almost those of the ML representation (except for
   (co-)fixpoint) *)

let array_map_left f a = (* Ocaml does not guarantee Array.map is LR *)
  let l = Array.length a in (* (even if so), then we rewrite it *)
  if l = 0 then [||] else begin
    let r = Array.create l (f a.(0)) in
    for i = 1 to l - 1 do
      r.(i) <- f a.(i)
    done;
    r
  end

let array_map_left_pair f a g b =
  let l = Array.length a in
  if l = 0 then [||],[||] else begin
    let r = Array.create l (f a.(0)) in
    let s = Array.create l (g b.(0)) in
    for i = 1 to l - 1 do
      r.(i) <- f a.(i);
      s.(i) <- g b.(i)
    done;
    r, s
  end

let map_constr_with_binders_left_to_right g f l c = match kind_of_term c with
  | IsRel _ | IsMeta _ | IsVar _   | IsSort _  | IsXtra _ -> c
  | IsCast (c,t) -> let c' = f l c in mkCast (c', f l t)
  | IsProd (na,t,c) -> let t' = f l t in mkProd (na, t', f (g l) c)
  | IsLambda (na,t,c) -> let t' = f l t in mkLambda (na, t', f (g l) c)
  | IsLetIn (na,b,t,c) ->
      let b' = f l b in let t' = f l t in mkLetIn (na, b', t', f (g l) c)
  | IsApp (c,al) -> 
      let c' = f l c in mkApp (c', array_map_left (f l) al)
  | IsEvar (e,al) -> mkEvar (e, array_map_left (f l) al)
  | IsConst (c,al) -> mkConst (c, array_map_left (f l) al)
  | IsMutInd (c,al) -> mkMutInd (c, array_map_left (f l) al)
  | IsMutConstruct (c,al) -> mkMutConstruct (c, array_map_left (f l) al)
  | IsMutCase (ci,p,c,bl) ->
      let p' = f l p in let c' = f l c in
      mkMutCase (ci, p', c', array_map_left (f l) bl)
  | IsFix (ln,(tl,lna,bl)) ->
      let l' = iterate g (Array.length tl) l in
      let tl', bl' = array_map_left_pair (f l) tl (f l') bl in
      mkFix (ln,(tl',lna,bl'))
  | IsCoFix(ln,(tl,lna,bl)) ->
      let l' = iterate g (Array.length tl) l in
      let tl', bl' = array_map_left_pair (f l) tl (f l') bl in
      mkCoFix (ln,(tl',lna,bl'))

(* strong *)
let map_constr_with_full_binders g f l c = match kind_of_term c with
  | IsRel _ | IsMeta _ | IsVar _   | IsSort _  | IsXtra _ -> c
  | IsCast (c,t) -> mkCast (f l c, f l t)
  | IsProd (na,t,c) -> mkProd (na, f l t, f (g (na,None,t) l) c)
  | IsLambda (na,t,c) -> mkLambda (na, f l t, f (g (na,None,t) l) c)
  | IsLetIn (na,b,t,c) -> mkLetIn (na, f l b, f l t, f (g (na,Some b,t) l) c)
  | IsApp (c,al) -> mkApp (f l c, Array.map (f l) al)
  | IsEvar (e,al) -> mkEvar (e, Array.map (f l) al)
  | IsConst (c,al) -> mkConst (c, Array.map (f l) al)
  | IsMutInd (c,al) -> mkMutInd (c, Array.map (f l) al)
  | IsMutConstruct (c,al) -> mkMutConstruct (c, Array.map (f l) al)
  | IsMutCase (ci,p,c,bl) -> mkMutCase (ci, f l p, f l c, Array.map (f l) bl)
  | IsFix (ln,(tl,lna,bl)) ->
      let tll = Array.to_list tl in
      let l' = List.fold_right2 (fun na t l -> g (na,None,t) l) lna tll l in
      mkFix (ln,(Array.map (f l) tl,lna,Array.map (f l') bl))
  | IsCoFix(ln,(tl,lna,bl)) ->
      let tll = Array.to_list tl in
      let l' = List.fold_right2 (fun na t l -> g (na,None,t) l) lna tll l in
      mkCoFix (ln,(Array.map (f l) tl,lna,Array.map (f l') bl))

(* [compare_constr f c1 c2] compare [c1] and [c2] using [f] to compare
   the immediate subterms of [c1] of [c2] if needed; Cast's, binders
   name and Cases annotations are not taken into account *)

let compare_constr f c1 c2 =
  match kind_of_term c1, kind_of_term c2 with
  | IsRel n1, IsRel n2 -> n1 = n2
  | IsMeta m1, IsMeta m2 -> m1 = m2
  | IsVar id1, IsVar id2 -> id1 = id2
  | IsSort s1, IsSort s2 -> s1 = s2
  | IsXtra s1, IsXtra s2 -> s1 = s2
  | IsCast (c1,_), _ -> f c1 c2
  | _, IsCast (c2,_) -> f c1 c2
  | IsProd (_,t1,c1), IsProd (_,t2,c2) -> f t1 t2 & f c1 c2
  | IsLambda (_,t1,c1), IsLambda (_,t2,c2) -> f t1 t2 & f c1 c2
  | IsLetIn (_,b1,t1,c1), IsLetIn (_,b2,t2,c2) -> f b1 b2 & f t1 t2 & f c1 c2
  | IsApp (c1,l1), IsApp (c2,l2) -> f c1 c2 & array_for_all2 f l1 l2
  | IsEvar (e1,l1), IsEvar (e2,l2) -> e1 = e2 & array_for_all2 f l1 l2
  | IsConst (c1,l1), IsConst (c2,l2) -> c1 = c2 & array_for_all2 f l1 l2
  | IsMutInd (c1,l1), IsMutInd (c2,l2) -> c1 = c2 & array_for_all2 f l1 l2
  | IsMutConstruct (c1,l1), IsMutConstruct (c2,l2) ->
      c1 = c2 & array_for_all2 f l1 l2
  | IsMutCase (_,p1,c1,bl1), IsMutCase (_,p2,c2,bl2) ->
      f p1 p2 & f c1 c2 & array_for_all2 f bl1 bl2
  | IsFix (ln1,(tl1,_,bl1)), IsFix (ln2,(tl2,_,bl2)) ->
      ln1 = ln2 & array_for_all2 f tl1 tl2 & array_for_all2 f bl1 bl2
  | IsCoFix(ln1,(tl1,_,bl1)), IsCoFix(ln2,(tl2,_,bl2)) ->
      ln1 = ln2 & array_for_all2 f tl1 tl2 & array_for_all2 f bl1 bl2
  | _ -> false

(***************************************************************************)
(*     Type of assumptions                                                 *)
(***************************************************************************)

type types = constr

let type_app f tt = f tt

let body_of_type ty = ty

type named_declaration = identifier * constr option * types
type rel_declaration = name * constr option * types



(****************************************************************************)
(*              Functions for dealing with constr terms                     *)
(****************************************************************************)

(*********************)
(*     Occurring     *)
(*********************)

exception FreeVar
exception Occur

(* (closedn n M) raises FreeVar if a variable of height greater than n
   occurs in M, returns () otherwise *)

let closedn = 
  let rec closed_rec n c = match kind_of_term c with
    | IsRel m -> if m>n then raise FreeVar
    | _ -> iter_constr_with_binders succ closed_rec n c
  in 
  closed_rec

(* [closed0 M] is true iff [M] is a (deBruijn) closed term *)

let closed0 term =
  try closedn 0 term; true with FreeVar -> false

(* returns the list of free debruijn indices in a term *)

let free_rels m = 
  let rec frec depth acc c = match kind_of_term c with
    | IsRel n       -> if n >= depth then Intset.add (n-depth+1) acc else acc
    | _ -> fold_constr_with_binders succ frec depth acc c
  in 
  frec 1 Intset.empty m

(* (noccurn n M) returns true iff (Rel n) does NOT occur in term M  *)

let noccurn n term = 
  let rec occur_rec n c = match kind_of_term c with
    | IsRel m -> if m = n then raise Occur
    | _ -> iter_constr_with_binders succ occur_rec n c
  in 
  try occur_rec n term; true with Occur -> false

(* (noccur_between n m M) returns true iff (Rel p) does NOT occur in term M 
  for n <= p < n+m *)

let noccur_between n m term = 
  let rec occur_rec n c = match kind_of_term c with
    | IsRel(p) -> if n<=p && p<n+m then raise Occur
    | _        -> iter_constr_with_binders succ occur_rec n c
  in 
  try occur_rec n term; true with Occur -> false

(* Checking function for terms containing existential variables.
 The function [noccur_with_meta] considers the fact that
 each existential variable (as well as each isevar)
 in the term appears applied to its local context,
 which may contain the CoFix variables. These occurrences of CoFix variables
 are not considered *)

let noccur_with_meta n m term = 
  let rec occur_rec n c = match kind_of_term c with
    | IsRel p -> if n<=p & p<n+m then raise Occur
    | IsApp(f,cl) ->
	(match kind_of_term f with
           | IsCast (c,_) when isMeta c -> ()
           | IsMeta _ -> ()
	   | _ -> iter_constr_with_binders succ occur_rec n c)
    | IsEvar (_, _) -> ()
    | _ -> iter_constr_with_binders succ occur_rec n c
  in
  try (occur_rec n term; true) with Occur -> false


(*********************)
(*      Lifting      *)
(*********************)

(* Explicit lifts and basic operations *)
type lift_spec =
  | ELID
  | ELSHFT of lift_spec * int (* ELSHFT(l,n) == lift of n, then apply lift l *)
  | ELLFT of int * lift_spec  (* ELLFT(n,l)  == apply l to de Bruijn > n *)
                            (*                 i.e under n binders *)

(* compose a relocation of magnitude n *)
let rec el_shft n = function
  | ELSHFT(el,k) -> el_shft (k+n) el
  | el -> if n = 0 then el else ELSHFT(el,n)


(* cross n binders *)
let rec el_liftn n = function
  | ELID -> ELID
  | ELLFT(k,el) -> el_liftn (n+k) el
  | el -> if n=0 then el else ELLFT(n, el)

let el_lift el = el_liftn 1 el

(* relocation of de Bruijn n in an explicit lift *)
let rec reloc_rel n = function
  | ELID -> n
  | ELLFT(k,el) ->
      if n <= k then n else (reloc_rel (n-k) el) + k
  | ELSHFT(el,k) -> (reloc_rel (n+k) el)


(* The generic lifting function *)
let rec exliftn el c = match kind_of_term c with
  | IsRel i -> mkRel(reloc_rel i el)
  | _ -> map_constr_with_binders el_lift exliftn el c

(* Lifting the binding depth across k bindings *)

let liftn k n = 
  match el_liftn (pred n) (el_shft k ELID) with
    | ELID -> (fun c -> c)
    | el -> exliftn el
 
let lift k = liftn k 1

let pop t = lift (-1) t

(*********************)
(*   Substituting    *)
(*********************)

(* (subst1 M c) substitutes M for Rel(1) in c 
   we generalise it to (substl [M1,...,Mn] c) which substitutes in parallel
   M1,...,Mn for respectively Rel(1),...,Rel(n) in c *)

(* 1st : general case *)

type info = Closed | Open | Unknown
type 'a substituend = { mutable sinfo: info; sit: 'a }

let rec lift_substituend depth s =
  match s.sinfo with
    | Closed -> s.sit
    | Open -> lift depth s.sit
    | Unknown ->
        s.sinfo <- if closed0 s.sit then Closed else Open;
        lift_substituend depth s

let make_substituend c = { sinfo=Unknown; sit=c }

let substn_many lamv n =
  let lv = Array.length lamv in 
  let rec substrec depth c = match kind_of_term c with
    | IsRel k     ->
        if k<=depth then 
	  c
        else if k-depth <= lv then
          lift_substituend depth lamv.(k-depth-1)
        else 
	  mkRel (k-lv)
    | _ -> map_constr_with_binders succ substrec depth c
  in 
  substrec n

let substnl laml k =
  substn_many (Array.map make_substituend (Array.of_list laml)) k
let substl laml =
  substn_many (Array.map make_substituend (Array.of_list laml)) 0
let subst1 lam = substl [lam]

let substl_decl laml (id,bodyopt,typ as d) =
  match bodyopt with
    | None -> (id,None,substl laml typ)
    | Some body -> (id, Some (substl laml body), type_app (substl laml) typ)
let subst1_decl lam = substl_decl [lam]

(* (thin_val sigma) removes identity substitutions from sigma *)

let rec thin_val = function
  | [] -> []
  | (((id,{ sit = v }) as s)::tl) when isVar v -> 
      if id = destVar v then thin_val tl else s::(thin_val tl)
  | h::tl -> h::(thin_val tl)

(* (replace_vars sigma M) applies substitution sigma to term M *)
let replace_vars var_alist = 
  let var_alist =
    List.map (fun (str,c) -> (str,make_substituend c)) var_alist in
  let var_alist = thin_val var_alist in 
  let rec substrec n c = match kind_of_term c with
    | IsVar x ->
        (try lift_substituend n (List.assoc x var_alist)
         with Not_found -> c)
    | _ -> map_constr_with_binders succ substrec n c
  in 
  if var_alist = [] then (function x -> x) else substrec 0

(* (subst_var str t) substitute (VAR str) by (Rel 1) in t *)
let subst_var str = replace_vars [(str, mkRel 1)]

(* (subst_vars [id1;...;idn] t) substitute (VAR idj) by (Rel j) in t *)
let substn_vars p vars =
  let _,subst =
    List.fold_left (fun (n,l) var -> ((n+1),(var,mkRel n)::l)) (p,[]) vars
  in replace_vars (List.rev subst)

let subst_vars = substn_vars 1

(*********************)
(* Term constructors *)
(*********************)

(* Constructs a DeBrujin index with number n *)
let mkRel = mkRel

(* Constructs an existential variable named "?n" *)
let mkMeta = mkMeta

(* Constructs a Variable named id *)
let mkVar = mkVar

(* Construct an XTRA term (XTRA is an extra slot for whatever you want) *)
let mkXtra = mkXtra

(* Construct a type *)
let mkSort   = mkSort
let mkProp   = mkSort mk_Prop
let mkSet    = mkSort mk_Set
let mkType u = mkSort (Type u)

let prop = Prop Null
and spec = Prop Pos
and types = Type dummy_univ
and type_0 = Type prop_univ
and type_1 = Type prop_univ_univ

(* Constructs the term t1::t2, i.e. the term t1 casted with the type t2 *)
(* (that means t2 is declared as the type of t1) *)
let mkCast = mkCast

(* Constructs the product (x:t1)t2 *)
let mkProd = mkProd
let mkNamedProd id typ c = mkProd (Name id, typ, subst_var id c)
let mkProd_string   s t c = mkProd (Name (id_of_string s), t, c)

(* Constructs the abstraction [x:t1]t2 *)
let mkLambda = mkLambda
let mkNamedLambda id typ c = mkLambda (Name id, typ, subst_var id c)
let mkLambda_string s t c = mkLambda (Name (id_of_string s), t, c)

(* Constructs [x=c_1:t]c_2 *)
let mkLetIn = mkLetIn
let mkNamedLetIn id c1 t c2 = mkLetIn (Name id, c1, t, subst_var id c2)

(* Constructs either [(x:t)c] or [[x=b:t]c] *)
let mkProd_or_LetIn (na,body,t) c =
  match body with
    | None -> mkProd (na, t, c)
    | Some b -> mkLetIn (na, b, t, c)

let mkNamedProd_or_LetIn (id,body,t) c =
  match body with
    | None -> mkNamedProd id (body_of_type t) c
    | Some b -> mkNamedLetIn id b (body_of_type t) c

(* Constructs either [[x:t]c] or [[x=b:t]c] *)
let mkLambda_or_LetIn (na,body,t) c =
  match body with
    | None -> mkLambda (na, t, c)
    | Some b -> mkLetIn (na, b, t, c)

let mkNamedLambda_or_LetIn (id,body,t) c =
  match body with
    | None -> mkNamedLambda id (body_of_type t) c
    | Some b -> mkNamedLetIn id b (body_of_type t) c

(* Constructs either [(x:t)c] or [c] where [x] is replaced by [b] *)
let mkProd_wo_LetIn (na,body,t) c =
  match body with
    | None -> mkProd (na, body_of_type t, c)
    | Some b -> subst1 b c

let mkNamedProd_wo_LetIn (id,body,t) c =
  match body with
    | None -> mkNamedProd id (body_of_type t) c
    | Some b -> subst1 b (subst_var id c)

(* non-dependent product t1 -> t2 *)
let mkArrow t1 t2 = mkProd (Anonymous, t1, t2)

(* If lt = [t1; ...; tn], constructs the application (t1 ... tn) *)
(* We ensure applicative terms have at most one arguments and the
   function is not itself an applicative term *)
let mkApp = mkApp

let mkAppA v =
  let l = Array.length v in
  if l=0 then anomaly "mkAppA received an empty array"
  else mkApp (v.(0), Array.sub v 1 (Array.length v -1))

(* Constructs a constant *) 
(* The array of terms correspond to the variables introduced in the section *)
let mkConst = mkConst

(* Constructs an existential variable *)
let mkEvar = mkEvar

(* Constructs the ith (co)inductive type of the block named sp *)
(* The array of terms correspond to the variables introduced in the section *)
let mkMutInd = mkMutInd

(* Constructs the jth constructor of the ith (co)inductive type of the 
   block named sp. The array of terms correspond to the variables
   introduced in the section *)
let mkMutConstruct = mkMutConstruct

(* Constructs the term <p>Case c of c1 | c2 .. | cn end *)
let mkMutCase = mkMutCase
let mkMutCaseL (ci, p, c, ac) = mkMutCase (ci, p, c, Array.of_list ac)

(* If recindxs = [|i1,...in|] 
      typarray = [|t1,...tn|]
      funnames = [f1,.....fn]
   then    

      mkFix recindxs i typarray funnames bodies
   
   constructs the ith function of the block  

    Fixpoint f1 [ctx1] = b1
    with     f2 [ctx2] = b2
    ...
    with     fn [ctxn] = bn.

   where the lenght of the jth context is ij.
*)

let mkFix = mkFix

(* If typarray = [|t1,...tn|]
      funnames = [f1,.....fn]
      bodies   = [b1,.....bn]
   then

      mkCoFix i typsarray funnames bodies 

   constructs the ith function of the block  
   
    CoFixpoint f1 = b1
    with       f2 = b2
    ...
    with       fn = bn.
*)
let mkCoFix = mkCoFix

(* Construct an implicit *)
let implicit_sort = Type implicit_univ
let mkImplicit = mkSort implicit_sort

let rec strip_outer_cast c = match kind_of_term c with
  | IsCast (c,_) -> strip_outer_cast c
  | _ -> c

(* Fonction spéciale qui laisse les cast clés sous les Fix ou les MutCase *)

let under_outer_cast f c =  match kind_of_term c with
  | IsCast (b,t) -> mkCast (f b,f t)
  | _ -> f c

let rec under_casts f c = match kind_of_term c with
  | IsCast (c,t) -> mkCast (under_casts f c, t)
  | _            -> f c

(***************************)
(* Other term constructors *)
(***************************)

let abs_implicit c = mkLambda (Anonymous, mkImplicit, c)
let lambda_implicit a = mkLambda (Name(id_of_string"y"), mkImplicit, a)
let lambda_implicit_lift n a = iterate lambda_implicit n (lift n a)


(* prod_it b [xn:Tn;..;x1:T1] = (x1:T1)..(xn:Tn)b *)
let prod_it = List.fold_left (fun c (n,t)  -> mkProd (n, t, c))

(* lam_it b [xn:Tn;..;x1:T1] = [x1:T1]..[xn:Tn]b *)
let lam_it = List.fold_left (fun c (n,t)  -> mkLambda (n, t, c))

(* prodn n [xn:Tn;..;x1:T1;Gamma] b = (x1:T1)..(xn:Tn)b *)
let prodn n env b =
  let rec prodrec = function
    | (0, env, b)        -> b
    | (n, ((v,t)::l), b) -> prodrec (n-1,  l, mkProd (v,t,b))
    | _ -> assert false
  in 
  prodrec (n,env,b)

(* lamn n [xn:Tn;..;x1:T1;Gamma] b = [x1:T1]..[xn:Tn]b *)
let lamn n env b =
  let rec lamrec = function
    | (0, env, b)        -> b
    | (n, ((v,t)::l), b) -> lamrec (n-1,  l, mkLambda (v,t,b))
    | _ -> assert false
  in 
  lamrec (n,env,b)

let applist (f,l) = mkApp (f, Array.of_list l)

let applistc f l = mkApp (f, Array.of_list l)

let appvect = mkApp
	    
let appvectc f l = mkApp (f,l)
		     
(* to_lambda n (x1:T1)...(xn:Tn)(xn+1:Tn+1)...(xn+j:Tn+j)T =
 * [x1:T1]...[xn:Tn](xn+1:Tn+1)...(xn+j:Tn+j)T *)
let rec to_lambda n prod =
  if n = 0 then 
    prod 
  else 
    match kind_of_term prod with 
      | IsProd (na,ty,bd) -> mkLambda (na,ty,to_lambda (n-1) bd)
      | IsCast (c,_) -> to_lambda n c
      | _   -> errorlabstrm "to_lambda" [<>]                      

let rec to_prod n lam =
  if n=0 then 
    lam
  else   
    match kind_of_term lam with 
      | IsLambda (na,ty,bd) -> mkProd (na,ty,to_prod (n-1) bd)
      | IsCast (c,_) -> to_prod n c
      | _   -> errorlabstrm "to_prod" [<>]                      
	    
(* pseudo-reduction rule:
 * [prod_app  s (Prod(_,B)) N --> B[N]
 * with an strip_outer_cast on the first argument to produce a product *)

let prod_app t n =
  match kind_of_term (strip_outer_cast t) with
    | IsProd (_,_,b) -> subst1 n b
    | _ ->
	errorlabstrm "prod_app"
	  [< 'sTR"Needed a product, but didn't find one" ; 'fNL >]


(* prod_appvect T [| a1 ; ... ; an |] -> (T a1 ... an) *)
let prod_appvect t nL = Array.fold_left prod_app t nL

(* prod_applist T [ a1 ; ... ; an ] -> (T a1 ... an) *)
let prod_applist t nL = List.fold_left prod_app t nL


(*********************************)
(* Other term destructors        *)
(*********************************)

type arity = rel_declaration list * sorts

(* Transforms a product term (x1:T1)..(xn:Tn)T into the pair
   ([(xn,Tn);...;(x1,T1)],T), where T is not a product *)
let destArity = 
  let rec prodec_rec l c =
    match kind_of_term c with
    | IsProd (x,t,c) -> prodec_rec ((x,None,t)::l) c
    | IsLetIn (x,b,t,c) -> prodec_rec ((x,Some b,t)::l) c
    | IsCast (c,_)   -> prodec_rec l c
    | IsSort s       -> l,s
    | _              -> anomaly "destArity: not an arity"
  in 
  prodec_rec [] 

let rec isArity c =
  match kind_of_term c with
  | IsProd (_,_,c) -> isArity c
  | IsCast (c,_)   -> isArity c
  | IsSort _       -> true
  | _ -> false

(* Transforms a product term (x1:T1)..(xn:Tn)T into the pair
   ([(xn,Tn);...;(x1,T1)],T), where T is not a product *)
let decompose_prod = 
  let rec prodec_rec l c = match kind_of_term c with
    | IsProd (x,t,c) -> prodec_rec ((x,t)::l) c
    | IsCast (c,_)   -> prodec_rec l c
    | _              -> l,c
  in 
  prodec_rec []

let rec hd_of_prod prod =
  match kind_of_term prod with
    | IsProd (n,c,t') -> hd_of_prod t'
    | IsCast (c,_) -> hd_of_prod c
    | _ -> prod

(* Transforms a lambda term [x1:T1]..[xn:Tn]T into the pair
   ([(xn,Tn);...;(x1,T1)],T), where T is not a lambda *)
let decompose_lam = 
  let rec lamdec_rec l c = match kind_of_term c with
    | IsLambda (x,t,c) -> lamdec_rec ((x,t)::l) c
    | IsCast (c,_)     -> lamdec_rec l c
    | _                -> l,c
  in 
  lamdec_rec []

(* Given a positive integer n, transforms a product term (x1:T1)..(xn:Tn)T 
   into the pair ([(xn,Tn);...;(x1,T1)],T) *)
let decompose_prod_n n =
  if n < 0 then error "decompose_prod_n: integer parameter must be positive";
  let rec prodec_rec l n c = 
    if n=0 then l,c 
    else match kind_of_term c with 
      | IsProd (x,t,c) -> prodec_rec ((x,t)::l) (n-1) c
      | IsCast (c,_)   -> prodec_rec l n c
      | _ -> error "decompose_prod_n: not enough products"
  in 
  prodec_rec [] n 

(* Given a positive integer n, transforms a lambda term [x1:T1]..[xn:Tn]T 
   into the pair ([(xn,Tn);...;(x1,T1)],T) *)
let decompose_lam_n n =
  if n < 0 then error "decompose_lam_n: integer parameter must be positive";
  let rec lamdec_rec l n c = 
    if n=0 then l,c 
    else match kind_of_term c with 
      | IsLambda (x,t,c) -> lamdec_rec ((x,t)::l) (n-1) c
      | IsCast (c,_)     -> lamdec_rec l n c
      | _ -> error "decompose_lam_n: not enough abstractions"
  in 
  lamdec_rec [] n 

(* (nb_lam [na1:T1]...[nan:Tan]c) where c is not an abstraction
 * gives n (casts are ignored) *)
let nb_lam = 
  let rec nbrec n c = match kind_of_term c with
    | IsLambda (_,_,c) -> nbrec (n+1) c
    | IsCast (c,_) -> nbrec n c
    | _ -> n
  in 
  nbrec 0
    
(* similar to nb_lam, but gives the number of products instead *)
let nb_prod = 
  let rec nbrec n c = match kind_of_term c with
    | IsProd (_,_,c) -> nbrec (n+1) c
    | IsCast (c,_) -> nbrec n c
    | _ -> n
  in 
  nbrec 0

(* Misc *)
let sort_hdchar = function
  | Prop(_) -> "P"
  | Type(_) -> "T"

(* Level comparison for information extraction : Prop <= Type *)
let le_kind l m = (isprop l) or (is_Type m)

let le_kind_implicit k1 k2 = 
  (k1=mkImplicit) or (isprop k1) or (k2=mkImplicit) or (is_Type k2)

(******************************************************************)
(* Flattening and unflattening of embedded applications and casts *)
(******************************************************************)

(* flattens application lists *)
let rec collapse_appl c = match kind_of_term c with
  | IsApp (f,cl) -> 
      let rec collapse_rec f cl2 = match kind_of_term f with
	| IsApp (g,cl1) -> collapse_rec g (Array.append cl1 cl2)
	| IsCast (c,_) when isApp c -> collapse_rec c cl2
	| _ -> if cl2 = [||] then f else mkApp (f,cl2)
      in 
      collapse_rec f cl
  | _ -> c

let rec decomp_app c =
  match kind_of_term (collapse_appl c) with
    | IsApp (f,cl) -> (f, Array.to_list cl)
    | IsCast (c,t) -> decomp_app c
    | _ -> (c,[])

(* strips head casts and flattens head applications *)
let rec strip_head_cast c = match kind_of_term c with
  | IsApp (f,cl) -> 
      let rec collapse_rec f cl2 = match kind_of_term f with
	| IsApp (g,cl1) -> collapse_rec g (Array.append cl1 cl2)
	| IsCast (c,_) -> collapse_rec c cl2
	| _ -> if cl2 = [||] then f else mkApp (f,cl2)
      in 
      collapse_rec f cl
  | IsCast (c,t) -> strip_head_cast c
  | _ -> c

(* Returns the list of global variables in a term *)

let rec global_varsl l constr = match kind_of_term constr with
  | IsVar id -> id::l
  | _        -> fold_constr global_varsl l constr

let global_vars = global_varsl []

let global_vars_decl = function
  | (_, None, t) -> global_vars t
  | (_, Some c, t) -> (global_vars c)@(global_vars t)

let global_vars_set constr = 
  let rec filtrec acc c = match kind_of_term c with
    | IsVar id -> Idset.add id acc
    | _        -> fold_constr filtrec acc c
  in 
  filtrec Idset.empty constr

(* Rem: end of import from old module Generic *)

(* Various occurs checks *)

(* (occur_const s c) -> true if constant s occurs in c,
 * false otherwise *)
let occur_const s c = 
  let rec occur_rec c = match kind_of_term c with
    | IsConst (sp,_) when sp=s -> raise Occur
    | _ -> iter_constr occur_rec c
  in 
  try occur_rec c; false with Occur -> true

let occur_evar n c = 
  let rec occur_rec c = match kind_of_term c with
    | IsEvar (sp,_) when sp=n -> raise Occur
    | _ -> iter_constr occur_rec c
  in 
  try occur_rec c; false with Occur -> true

let occur_var s c = 
  let rec occur_rec c = match kind_of_term c with
    | IsVar id when id=s -> raise Occur
    | _ -> iter_constr occur_rec c
  in 
  try occur_rec c; false with Occur -> true

let occur_var_in_decl hyp (_,c,typ) =
  match c with
    | None -> occur_var hyp (body_of_type typ)
    | Some body -> occur_var hyp (body_of_type typ) || occur_var hyp body

(***************************************)
(*  alpha and eta conversion functions *)                         
(***************************************)

(* alpha conversion : ignore print names and casts *)
let rec eq_constr m n = 
  (m = n) or   (* Rem: ocaml '=' includes '==' *)
  compare_constr eq_constr m n

(* (dependent M N) is true iff M is eq_term with a subterm of N 
   M is appropriately lifted through abstractions of N *)

let dependent m t =
  let rec deprec m t =
    if (eq_constr m t) then
      raise Occur
    else
      iter_constr_with_binders (lift 1) deprec m t
  in 
  try deprec m t; false with Occur -> true

(* On reduit une serie d'eta-redex de tete ou rien du tout  *)
(* [x1:c1;...;xn:cn]@(f;a1...an;x1;...;xn) --> @(f;a1...an) *)
(* Remplace 2 versions précédentes buggées                  *)

let rec eta_reduce_head c =
  match kind_of_term c with
    | IsLambda (_,c1,c') ->
	(match kind_of_term (eta_reduce_head c') with
           | IsApp (f,cl) ->
               let lastn = (Array.length cl) - 1 in 
               if lastn < 1 then anomaly "application without arguments"
               else
                 (match kind_of_term cl.(lastn) with
                    | IsRel 1 ->
			let c' =
                          if lastn = 1 then f
			  else mkApp (f, Array.sub cl 0 lastn)
			in
			if not (dependent (mkRel 1) c')
                        then lift (-1) c'
                        else c
                    | _   -> c)
           | _ -> c)
    | _ -> c

(* alpha-eta conversion : ignore print names and casts *)
let eta_eq_constr =
  let rec aux t1 t2 =
    let t1 = eta_reduce_head (strip_head_cast t1)
    and t2 = eta_reduce_head (strip_head_cast t2) in
    t1=t2 or compare_constr aux t1 t2
  in aux


(* This renames bound variables with fresh and distinct names *)
(* in such a way that the printer doe not generate new names  *)
(* and therefore that printed names are the intern names      *)
(* In this way, tactics such as Induction works well          *)

let rec rename_bound_var l c =
  match kind_of_term c with
  | IsProd (Name s,c1,c2)  ->
      if dependent (mkRel 1) c2 then
        let s' = next_ident_away s (global_vars c2@l) in
        mkProd (Name s', c1, rename_bound_var (s'::l) c2)
      else 
	mkProd (Name s, c1, rename_bound_var l c2)
  | IsProd (Anonymous,c1,c2) -> mkProd (Anonymous, c1, rename_bound_var l c2)
  | IsCast (c,t) -> mkCast (rename_bound_var l c, t)
  | x -> c

(***************************)
(*  substitution functions *)                         
(***************************)

(* First utilities for avoiding telescope computation for subst_term *)

let prefix_application (k,c) (t : constr) = 
  let c' = strip_head_cast c and t' = strip_head_cast t in
  match kind_of_term c', kind_of_term t' with
    | IsApp (f1,cl1), IsApp (f2,cl2) ->
	let l1 = Array.length cl1
	and l2 = Array.length cl2 in
	if l1 <= l2
	   && eq_constr c' (mkApp (f2, Array.sub cl2 0 l1)) then
	  Some (mkApp (mkRel k, Array.sub cl2 l1 (l2 - l1)))
	else 
	  None
    | _ -> None

let prefix_application_eta (k,c) (t : constr) =
  let c' = strip_head_cast c and t' = strip_head_cast t in
  match kind_of_term c', kind_of_term t' with
    | IsApp (f1,cl1), IsApp (f2,cl2) ->
	let l1 = Array.length cl1
	and l2 = Array.length cl2 in
	if l1 <= l2 &&
           eta_eq_constr  c' (mkApp (f2, Array.sub cl2 0 l1)) then
	  Some (mkApp (mkRel k, Array.sub cl2 l1 (l2 - l1)))
	else 
	  None
  | (_,_) -> None

let sort_increasing_snd = 
  Sort.list 
    (fun (_,x) (_,y) -> match kind_of_term x, kind_of_term y with 
       | IsRel m, IsRel n -> m < n
       | _ -> assert false)

(* Recognizing occurrences of a given (closed) subterm in a term for Pattern :
   [subst_term c t] substitutes [(Rel 1)] for all occurrences of (closed)
   term [c] in a term [t] *)

let subst_term_gen eq_fun c t = 
  let rec substrec (k,c as kc) t =
    match prefix_application kc t with
      | Some x -> x
      | None ->
    (if eq_fun t c then mkRel k else match kind_of_term t with
       | IsConst _ | IsMutInd _ | IsMutConstruct _ -> t
       | _ ->
	   map_constr_with_binders
	     (fun (k,c) -> (k+1,lift 1 c))
	     substrec kc t)
  in 
  substrec (1,c) t

let subst_term = subst_term_gen eq_constr
let subst_term_eta = subst_term_gen eta_eq_constr

(* bl : (int,constr) Listmap.t = (int * constr) list *)
(* c : constr *)
(* for each binding (i,c_i) in bl, substitutes the metavar i by c_i in c *)
(* Raises Not_found if c contains a meta that is not in the association list *)

(* Bogué ? Pourquoi pas de lift en passant sous un lieur ?? *)
(* Et puis meta doit fusionner avec Evar *)
let rec subst_meta bl c = 
  match kind_of_term c with
    | IsMeta i -> List.assoc i bl
    | _ -> map_constr (subst_meta bl) c

(* Substitute only a list of locations locs, the empty list is
   interpreted as substitute all, if 0 is in the list then no
   substitution is done. The list may contain only negative occurrences
   that will not be substituted. *)

let subst_term_occ_gen locs occ c t =
  let maxocc = List.fold_right max locs 0 in
  let pos = ref occ in
  let check = ref true in
  let except = List.for_all (fun n -> n<0) locs in
  let rec substrec (k,c as kc) t =
    if (not except) & (!pos > maxocc) then t
    else
    if eq_constr t c then
      let r = 
	if except then 
	  if List.mem (- !pos) locs then t else (mkRel k)
	else 
	  if List.mem !pos locs then (mkRel k) else t
      in incr pos; r
    else
      match kind_of_term t with
	| IsConst _ | IsMutConstruct _ | IsMutInd _ -> t
	| _ ->
	    map_constr_with_binders_left_to_right
	      (fun (k,c) -> (k+1,lift 1 c)) substrec kc t
  in
  let t' = substrec (1,c) t in
  (!pos, t')

let subst_term_occ locs c t = 
  if locs = [] then
    subst_term c t
  else if List.mem 0 locs then 
    t
  else 
    let (nbocc,t') = subst_term_occ_gen locs 1 c t in
    if List.exists (fun o -> o >= nbocc or o <= -nbocc) locs then
      errorlabstrm "subst_term_occ" [< 'sTR "Too few occurences" >];
    t'

let subst_term_occ_decl locs c (id,bodyopt,typ as d) =
  match bodyopt with
    | None -> (id,None,subst_term_occ locs c typ)
    | Some body -> 
	if locs = [] then
	  (id,Some (subst_term c body),type_app (subst_term c) typ)
	else if List.mem 0 locs then 
	  d
	else 
	  let (nbocc,body') = subst_term_occ_gen locs 1 c body in
	  let (nbocc',t') = type_app (subst_term_occ_gen locs nbocc c) typ in
	  if List.exists (fun o -> o >= nbocc' or o <= -nbocc') locs then
	    errorlabstrm "subst_term_occ_decl" [< 'sTR "Too few occurences" >];
	  (id,Some body',t')
  
(***************************)
(* occurs check functions  *)                         
(***************************)

let occur_meta c =
  let rec occrec c = match kind_of_term c with
    | IsMeta _ -> raise Occur
    | _ -> iter_constr occrec c
  in try occrec c; false with Occur -> true

let occur_existential c = 
  let rec occrec c = match kind_of_term c with
    | IsEvar _ -> raise Occur
    | _ -> iter_constr occrec c
  in try occrec c; false with Occur -> true


module Htype =
  Hashcons.Make(
    struct
      type t = types
      type u = (constr -> constr) * (sorts -> sorts)
(*
      let hash_sub (hc,hs) j = {body=hc j.body; typ=hs j.typ}
      let equal j1 j2 = j1.body==j2.body & j1.typ==j2.typ
*)
(**)
      let hash_sub (hc,hs) j = hc j
      let equal j1 j2 = j1==j2
(**)
      let hash = Hashtbl.hash
    end)

let hsort _ _ s = s

let hcons_constr (hspcci,hspfw,hname,hident,hstr) =
  let hsortscci = Hashcons.simple_hcons hsort hspcci in
  let hsortsfw = Hashcons.simple_hcons hsort hspfw in
  let hcci = hcons_term (hsortscci,hspcci,hname,hident,hstr) in
  let hfw = hcons_term (hsortsfw,hspfw,hname,hident,hstr) in
  let htcci = Hashcons.simple_hcons Htype.f (hcci,hsortscci) in
  (hcci,hfw,htcci)

let hcons1_constr =
  let hnames = hcons_names () in
  let (hc,_,_) = hcons_constr hnames in
  hc

(* Abstract decomposition of constr to deal with generic functions *)

type fix_kind = RFix of (int array * int) | RCoFix of int

type constr_operator =
  | OpMeta of int
  | OpSort of sorts
  | OpRel of int | OpVar of identifier
  | OpCast | OpProd of name | OpLambda of name | OpLetIn of name
  | OpApp | OpConst of constant_path
  | OpEvar of existential_key
  | OpMutInd of inductive_path
  | OpMutConstruct of constructor_path
  | OpMutCase of case_info
  | OpRec of fix_kind * name list
  | OpXtra of string

let splay_constr c = match kind_of_term c with
  | IsRel n                    -> OpRel n, [||]
  | IsVar id                   -> OpVar id, [||] 
  | IsMeta n                   -> OpMeta n, [||]
  | IsSort s                   -> OpSort s, [||]
  | IsCast (t1, t2)            -> OpCast, [|t1;t2|]
  | IsProd (x, t1, t2)         -> OpProd x, [|t1;t2|]
  | IsLambda (x, t1, t2)       -> OpLambda x, [|t1;t2|]
  | IsLetIn (x, b, t1, t2)     -> OpLetIn x, [|b;t1;t2|]
  | IsApp (f,a)               -> OpApp, Array.append [|f|] a
  | IsConst (sp, a)            -> OpConst sp, a
  | IsEvar (sp, a)             -> OpEvar sp, a
  | IsMutInd (ind_sp, l)       -> OpMutInd ind_sp, l
  | IsMutConstruct (cstr_sp,l) -> OpMutConstruct cstr_sp, l
  | IsMutCase (ci,p,c,bl)      -> OpMutCase ci, Array.append [|p;c|] bl
  | IsFix (fi,(tl,lna,bl))     -> OpRec (RFix fi,lna), Array.append tl bl
  | IsCoFix (fi,(tl,lna,bl))   -> OpRec (RCoFix fi,lna), Array.append tl bl
  | IsXtra s                   -> OpXtra s, [||]

let gather_constr = function
  | OpRel n, [||]  -> mkRel n
  | OpVar id, [||] -> mkVar id
  | OpMeta n, [||] -> mkMeta n
  | OpSort s, [||] -> mkSort s
  | OpCast, [|t1;t2|]     -> mkCast (t1, t2)
  | OpProd x, [|t1;t2|]   -> mkProd (x, t1, t2)
  | OpLambda x, [|t1;t2|] -> mkLambda (x, t1, t2)
  | OpLetIn x, [|b;t1;t2|] -> mkLetIn (x, b, t1, t2)
  | OpApp, v     -> let f = v.(0) and a = array_tl v in mkApp (f, a)
  | OpConst sp, a -> mkConst (sp, a)
  | OpEvar sp, a  -> mkEvar (sp, a) 
  | OpMutInd ind_sp, l        -> mkMutInd (ind_sp, l) 
  | OpMutConstruct cstr_sp, l -> mkMutConstruct (cstr_sp, l)
  | OpMutCase ci,  v    ->
      let p = v.(0) and c = v.(1) and bl = Array.sub v 2 (Array.length v -2)
      in mkMutCase (ci, p, c, bl)   
  | OpRec (RFix fi,lna), a  ->
      let n = Array.length a / 2 in
      mkFix (fi,(Array.sub a 0 n, lna, Array.sub a n n))
  | OpRec (RCoFix i,lna), a ->
      let n = Array.length a / 2 in
      mkCoFix (i,(Array.sub a 0 n, lna, Array.sub a n n))
  | OpXtra s, [||] -> mkXtra s
  | _ -> errorlabstrm "Term.gather_term" [< 'sTR "ill-formed splayed constr">]

let rec mycombine l1 l3 =
  match (l1, l3) with
    ([], []) -> []
  | (a1::l1, a3::l3) -> (a1, None, a3) :: mycombine l1 l3
  | (_, _) -> invalid_arg "mycombine"

let rec mysplit = function
    [] -> ([], [])
  | (x, _, z)::l -> let (rx, rz) = mysplit l in (x::rx, z::rz)

let splay_constr_with_binders c = match kind_of_term c with
  | IsRel n                    -> OpRel n, [], [||]
  | IsVar id                   -> OpVar id, [], [||] 
  | IsMeta n                   -> OpMeta n, [], [||]
  | IsSort s                   -> OpSort s, [], [||]
  | IsCast (t1, t2)            -> OpCast, [], [|t1;t2|]
  | IsProd (x, t1, t2)         -> OpProd x, [x,None,t1], [|t2|]
  | IsLambda (x, t1, t2)       -> OpLambda x, [x,None,t1], [|t2|]
  | IsLetIn (x, b, t1, t2)     -> OpLetIn x, [x,Some b,t1], [|t2|]
  | IsApp (f,v)               -> OpApp, [], Array.append [|f|] v
  | IsConst (sp, a)            -> OpConst sp, [], a
  | IsEvar (sp, a)             -> OpEvar sp, [], a
  | IsMutInd (ind_sp, l)       -> OpMutInd ind_sp, [], l
  | IsMutConstruct (cstr_sp,l) -> OpMutConstruct cstr_sp, [], l
  | IsMutCase (ci,p,c,bl)      ->
      let v = Array.append [|p;c|] bl in OpMutCase ci, [], v
  | IsFix (fi,(tl,lna,bl)) ->
      let n = Array.length bl in
      let ctxt = mycombine
		   (List.rev lna)
		   (Array.to_list (Array.mapi lift tl)) in
      OpRec (RFix fi,lna), ctxt, bl
  | IsCoFix (fi,(tl,lna,bl)) ->
      let n = Array.length bl in
      let ctxt = mycombine
		   (List.rev lna)
		   (Array.to_list (Array.mapi lift tl)) in
      OpRec (RCoFix fi,lna), ctxt, bl
  | IsXtra s -> OpXtra s, [], [||]

let gather_constr_with_binders = function
  | OpRel n, [], [||]  -> mkRel n
  | OpVar id, [], [||] -> mkVar id
  | OpMeta n, [], [||] -> mkMeta n
  | OpSort s, [], [||] -> mkSort s
  | OpCast, [], [|t1;t2|]     -> mkCast (t1, t2)
  | OpProd _, [x,None,t1], [|t2|]   -> mkProd (x, t1, t2)
  | OpLambda _, [x,None,t1], [|t2|] -> mkLambda (x, t1, t2)
  | OpLetIn _, [x,Some b,t1], [|t2|] -> mkLetIn (x, b, t1, t2)
  | OpApp, [], v     -> let f = v.(0) and a = array_tl v in mkApp (f, a)
  | OpConst sp, [], a -> mkConst (sp, a)
  | OpEvar sp, [], a  -> mkEvar (sp, a) 
  | OpMutInd ind_sp, [], l        -> mkMutInd (ind_sp, l) 
  | OpMutConstruct cstr_sp, [], l -> mkMutConstruct (cstr_sp, l)
  | OpMutCase ci, [], v    ->
      let p = v.(0) and c = v.(1) and bl = Array.sub v 2 (Array.length v -2)
      in mkMutCase (ci, p, c, bl)   
  | OpRec (RFix fi,lna), ctxt, bl  ->
      let (lna, tl) = mysplit ctxt in
      let tl = Array.mapi (fun i -> lift (-i)) (Array.of_list tl) in
      mkFix (fi,(tl, List.rev lna, bl))
  | OpRec (RCoFix i,lna), ctxt, bl ->
      let (lna, tl) = mysplit ctxt in
      let tl = Array.mapi (fun i -> lift (-i)) (Array.of_list tl) in
      mkCoFix (i,(tl, List.rev lna, bl))
  | OpXtra s, [], [||] -> mkXtra s
  | _  -> errorlabstrm "Term.gather_term" [< 'sTR "ill-formed splayed constr">]

let generic_fold_left f acc bl tl =
  let acc =
    List.fold_left 
      (fun acc (_,bo,t) ->
	 match bo with
	   | None -> f acc t
	   | Some b -> f (f acc b) t) acc bl in
  Array.fold_left f acc tl
