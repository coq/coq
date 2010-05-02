(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util
open Names
open Term
open Libobject
open Library
open Pattern
open Libnames

(* Named, bounded-depth, term-discrimination nets.
   Implementation:
   Term-patterns are stored in discrimination-nets, which are
   themselves stored in a hash-table, indexed by the first label.
   They are also stored by name in a table on-the-side, so that we can
   override them if needed. *)

(* The former comments are from Chet.
   See the module dn.ml for further explanations.
   Eduardo (5/8/97) *)
module Make = 
  functor (Y:Map.OrderedType) ->
struct
  module X = struct
    type t = constr_pattern*int
    let compare = Pervasives.compare
  end

  module Term_dn = Termdn.Make(Y)
  open Term_dn
  module Z = struct 
     type t = Term_dn.term_label
     let compare x y =  
       let make_name n =
	 match n with
	 | GRLabel(ConstRef con) -> 
	     GRLabel(ConstRef(constant_of_kn(canonical_con con)))
	 | GRLabel(IndRef (kn,i)) ->
	     GRLabel(IndRef(mind_of_kn(canonical_mind kn),i))
	 | GRLabel(ConstructRef ((kn,i),j ))->
	     GRLabel(ConstructRef((mind_of_kn(canonical_mind kn),i),j))
	 | k -> k
       in
	 Pervasives.compare (make_name x) (make_name y)
  end

  module Dn = Dn.Make(X)(Z)(Y)
  module Bounded_net = Btermdn.Make(Y)

    
type 'na t = {
  mutable table : ('na,constr_pattern * Y.t) Gmap.t;
  mutable patterns : (Term_dn.term_label option,Bounded_net.t) Gmap.t }


type 'na frozen_t = 
    ('na,constr_pattern * Y.t) Gmap.t
    * (Term_dn.term_label option, Bounded_net.t) Gmap.t

let create () =
  { table = Gmap.empty;
    patterns = Gmap.empty }

let get_dn dnm hkey =
  try Gmap.find hkey dnm with Not_found -> Bounded_net.create ()

let add dn (na,(pat,valu)) =
  let hkey = Option.map fst (Term_dn.constr_pat_discr pat) in 
  dn.table <- Gmap.add na (pat,valu) dn.table;
  let dnm = dn.patterns in
  dn.patterns <- Gmap.add hkey (Bounded_net.add None (get_dn dnm hkey) (pat,valu)) dnm

let rmv dn na =
  let (pat,valu) = Gmap.find na dn.table in
  let hkey = Option.map fst (Term_dn.constr_pat_discr pat) in 
  dn.table <- Gmap.remove na dn.table;
  let dnm = dn.patterns in
  dn.patterns <- Gmap.add hkey (Bounded_net.rmv None (get_dn dnm hkey) (pat,valu)) dnm

let in_dn dn na = Gmap.mem na dn.table

let remap ndn na (pat,valu) =
  rmv ndn na;
  add ndn (na,(pat,valu))

let decomp = 
  let rec decrec acc c = match kind_of_term c with
    | App (f,l) -> decrec (Array.fold_right (fun a l -> a::l) l acc) f
    | Cast (c1,_,_) -> decrec acc c1
    | _ -> (c,acc)
  in 
  decrec []

  let constr_val_discr t =
  let c, l = decomp t in
    match kind_of_term c with
    | Ind ind_sp -> Dn.Label(Term_dn.GRLabel (IndRef ind_sp),l)
    | Construct cstr_sp -> Dn.Label(Term_dn.GRLabel (ConstructRef cstr_sp),l)
    | Var id -> Dn.Label(Term_dn.GRLabel (VarRef id),l)
    | Const _ -> Dn.Everything
    | _ -> Dn.Nothing

let constr_val_discr_st (idpred,cpred) t =
  let c, l = decomp t in
    match kind_of_term c with
    | Const c -> if Cpred.mem c cpred then Dn.Everything else Dn.Label(Term_dn.GRLabel (ConstRef c),l)
    | Ind ind_sp -> Dn.Label(Term_dn.GRLabel (IndRef ind_sp),l)
    | Construct cstr_sp -> Dn.Label(Term_dn.GRLabel (ConstructRef cstr_sp),l)
    | Var id when not (Idpred.mem id idpred) -> Dn.Label(Term_dn.GRLabel (VarRef id),l)
    | Prod (n, d, c) -> Dn.Label(Term_dn.ProdLabel, [d; c])
    | Lambda (n, d, c) -> Dn.Label(Term_dn.LambdaLabel, [d; c] @ l)
    | Sort _ -> Dn.Label(Term_dn.SortLabel, [])
    | Evar _ -> Dn.Everything
    | _ -> Dn.Nothing

let lookup dn valu =
  let hkey =
    match (constr_val_discr valu) with
    | Dn.Label(l,_) -> Some l
    | _ -> None
  in
  try Bounded_net.lookup None (Gmap.find hkey dn.patterns) valu with Not_found -> []

let app f dn = Gmap.iter f dn.table

let dnet_depth = Btermdn.dnet_depth

let freeze dn = (dn.table, dn.patterns)

let unfreeze (fnm,fdnm) dn =
  dn.table <- fnm;
  dn.patterns <- fdnm

let empty dn =
  dn.table <- Gmap.empty;
  dn.patterns <- Gmap.empty

let to2lists dn =
  (Gmap.to_list dn.table, Gmap.to_list dn.patterns)
end
