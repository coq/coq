
(* $Id$ *)

open Util
open Names
(* open Generic *)
open Term
open Declarations
open Reduction

type constant_evaluation = 
  | EliminationFix of (int * constr) list * int
  | EliminationCases of int
  | NotAnElimination

let eval_table = ref Spmap.empty

(* Check that c is an "elimination constant"
    [xn:An]..[x1:A1](<P>MutCase (Rel i) of f1..fk end g1 ..gp)
or  [xn:An]..[x1:A1](Fix(f|t) (Rel i1) ..(Rel ip)) 
    with i1..ip distinct variables not occuring in t 
keep relevenant information ([i1,Ai1;..;ip,Aip],n,b)
with b = true in case of a fixpoint in order to compute 
an equivalent of Fix(f|t)[xi<-ai] as 
[yip:Bip]..[yi1:Bi1](F bn..b1) 
    == [yip:Bip]..[yi1:Bi1](Fix(f|t)[xi<-ai] (Rel 1)..(Rel p))
with bj=aj if j<>ik and bj=(Rel c) and Bic=Aic[xn..xic-1 <- an..aic-1] *)

exception Elimconst

let compute_consteval c = 
  let rec srec n labs c =
    let c',l = whd_betadeltaeta_stack (Global.env()) Evd.empty c [] in
    match kind_of_term c' with
      | IsLambda (_,t,g) when l=[] -> srec (n+1) (t::labs) g
      | IsFix ((nv,i),(tys,_,bds)) -> 
          if (List.length l) > n then raise Elimconst;
	  let nbfix = Array.length bds in
          let li = 
            List.map
	      (function
                 | Rel k ->
                     if
		       array_for_all (noccurn k) tys
		       && array_for_all (noccurn (k+nbfix)) bds
		     then 
		       (k, List.nth labs (k-1)) 
		     else 
		       raise Elimconst
                 | _ -> 
		     raise Elimconst) l
          in 
	  if list_distinct (List.map fst li) then 
	    EliminationFix (li,n) 
          else 
	    raise Elimconst
      | IsMutCase (_,_,Rel _,_) -> EliminationCases n
      | _ -> raise Elimconst
  in
  try srec 0 [] c
  with Elimconst -> NotAnElimination

let constant_eval sp =
  try
    Spmap.find sp !eval_table
  with Not_found -> begin
    let v = 
      let cb = Global.lookup_constant sp in
      match cb.const_body with
	| None -> NotAnElimination
	| Some v -> let c = cook_constant v in compute_consteval c
    in
    eval_table := Spmap.add sp v !eval_table;
    v
  end

(* Registration as global tables and rollback. *)

type frozen = constant_evaluation Spmap.t

let init () =
  eval_table := Spmap.empty

let freeze () =
  !eval_table

let unfreeze ct =
  eval_table := ct

let _ = 
  Summary.declare_summary "evaluation"
    { Summary.freeze_function = freeze;
      Summary.unfreeze_function = unfreeze;
      Summary.init_function = init }

let rollback f x =
  let fs = freeze () in
  try f x with e -> begin unfreeze fs; raise e end
