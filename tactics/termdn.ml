
(* $Id$ *)

open Util
open Generic
open Term

(* Discrimination nets of terms.
   See the module dn.ml for further explanations.
   Eduardo (5/8/97) *)

type lbl =
  | TERM of constr
  | DOPER of sorts oper
  | DLAMBDA

type 'a t = (lbl,constr,'a) Dn.t

(*If we have: f a b c ..., decomp gives: (f,[a;b;c;...])*)

let decomp = 
  let rec decrec acc = function
    | DOPN(AppL,cl) -> decrec (array_app_tl cl acc) (array_hd cl)
    | DOP2(Cast,c1,_) -> decrec acc c1
    | c -> (c,acc)
  in 
  decrec []   

let constr_pat_discr t =
  if not(occur_meta t) then 
    None
  else
    match decomp t with
      (* | DOPN(Const _,_) as c,l -> Some(TERM c,l) *)
      | DOPN(MutInd _,_) as c,l -> Some(TERM c,l)
      | DOPN(MutConstruct _,_) as c,l -> Some(TERM c,l)
      | VAR _ as c,l -> Some(TERM c,l)
      | c -> None

let constr_val_discr t =
  match decomp t with
    (* DOPN(Const _,_) as c,l -> Some(TERM c,l) *)
    | DOPN(MutInd _,_) as c,l -> Some(TERM c,l)
    | DOPN(MutConstruct _,_) as c,l -> Some(TERM c,l)
    | VAR _ as c,l -> Some(TERM c,l)
    | c -> None

(* Les deux fonctions suivantes ecrasaient les precedentes, 
   ajout d'un suffixe _nil CP 16/08 *) 

let constr_pat_discr_nil t =
  match constr_pat_discr t with
    | None -> None
    | Some (c,_) -> Some(c,[])

let constr_val_discr_nil t =
  match constr_val_discr t with
    | None -> None
    | Some (c,_) -> Some(c,[])

let create () = Dn.create constr_pat_discr

let add = Dn.add
let rmv = Dn.rmv

let lookup dn t = Dn.lookup dn constr_val_discr t

let app f dn = Dn.app f dn
