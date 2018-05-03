open Util
open Num
open Polynomial
open Vect

let debug = false

let compare_float (p : float) q = Pervasives.compare p q

(** Implementation of intervals *)
module Itv =
struct

  (** The type of intervals is *)
  type interval = num option * num option
      (** None models the absence of bound i.e. infinity *)
      (** As a result,
	  - None , None   -> \]-oo,+oo\[
	  - None , Some v -> \]-oo,v\]
	  - Some v, None  -> \[v,+oo\[
	  - Some v, Some v' -> \[v,v'\]
      Intervals needs to be explicitly normalised.
      *)

  (** if then interval [itv] is empty, [norm_itv itv] returns [None]
      otherwise, it returns [Some itv] *)

  let norm_itv itv =
    match itv with
      | Some a , Some b -> if a <=/ b then Some itv else None
      |   _             -> Some itv

(** [inter i1 i2 = None] if the intersection of intervals is empty
    [inter i1 i2 = Some i] if [i] is the intersection of the intervals [i1] and [i2] *)
  let inter i1 i2 =
    let (l1,r1) = i1
    and (l2,r2) = i2 in

    let inter f o1 o2 =
      match o1 , o2 with
	| None , None -> None
	| Some _ , None -> o1
	| None  , Some _ -> o2
	| Some n1 , Some n2 -> Some (f n1 n2) in

    norm_itv (inter max_num l1 l2 , inter min_num r1 r2)

  let range = function
    | None,_ | _,None -> None
    | Some i,Some j -> Some (floor_num j -/ceiling_num i +/ (Int 1))


  let smaller_itv i1 i2 =
    match  range i1 ,  range i2  with
      | None , _ -> false
      |  _   , None -> true
      | Some i , Some j -> i <=/ j


(** [in_bound bnd v] checks whether [v] is within the bounds [bnd] *)
let in_bound bnd v =
  let (l,r) = bnd in
  match l , r with
    | None , None -> true
    | None , Some a -> v <=/ a
    | Some a , None -> a <=/ v
    | Some a , Some b -> a <=/ v && v <=/ b


end
open Itv
type vector = Vect.t

(** 'cstr' is the type of constraints.
    {coeffs = v ; bound = (l,r) } models the constraints l <= v <= r
**)

module ISet = Set.Make(Int)

module System = Hashtbl.Make(Vect)

type proof =
| Assum of int
| Elim of  var * proof * proof
| And of proof * proof

let max_nb_cstr = ref max_int

type system = {
  sys : cstr_info ref System.t ;
  vars : ISet.t
}
and cstr_info = {
  bound : interval ;
  prf : proof ;
  pos : int ;
  neg : int ;
}


(** A system of constraints has the form [\{sys = s ; vars = v\}].
    [s] is a hashtable mapping a normalised vector to a [cstr_info] record where
    - [bound] is an interval
    - [prf_idx] is the set of hypothesis indexes (i.e. constraints in the initial system) used to obtain the current constraint.
       In the initial system, each constraint is given an unique singleton proof_idx.
       When a new constraint c is computed by a function f(c1,...,cn), its proof_idx is ISet.fold union (List.map (fun x -> x.proof_idx) [c1;...;cn]
    - [pos] is the number of positive values of the vector
    - [neg] is the number of negative values of the vector
    ( [neg] + [pos] is therefore the length of the vector)
    [v] is an upper-bound of the set of variables which appear in [s].
*)

(** To be thrown when a system has no solution *)
exception SystemContradiction of proof

(** Pretty printing *)
  let rec pp_proof o prf =
    match prf with
      | Assum i -> Printf.fprintf o "H%i" i
      | Elim(v, prf1,prf2) -> Printf.fprintf o "E(%i,%a,%a)" v pp_proof prf1 pp_proof prf2
      | And(prf1,prf2)   -> Printf.fprintf o "A(%a,%a)"  pp_proof prf1 pp_proof prf2

let pp_cstr o (vect,bnd) =
    let (l,r) = bnd in
      (match l with
	| None -> ()
	| Some n -> Printf.fprintf o "%s <= " (string_of_num n))
      ;
      pp_vect o vect ;
      (match r with
	      | None -> output_string o"\n"
	      | Some n -> Printf.fprintf o "<=%s\n" (string_of_num n))


let pp_system o sys=
  System.iter (fun vect ibnd ->
    pp_cstr o (vect,(!ibnd).bound)) sys

(** [merge_cstr_info] takes:
    - the intersection of bounds and
    - the union of proofs
    - [pos] and [neg] fields should be identical *)

let merge_cstr_info i1 i2 =
  let { pos = p1 ; neg = n1 ; bound = i1 ; prf = prf1 } = i1
  and { pos = p2 ; neg = n2 ; bound = i2 ; prf = prf2 } = i2 in
    assert (Int.equal p1 p2 && Int.equal n1 n2) ;
    match inter i1 i2 with
      | None -> None (* Could directly raise a system contradiction exception *)
      | Some bnd ->
	  Some { pos = p1 ; neg = n1 ; bound = bnd ; prf = And(prf1,prf2) }

(** [xadd_cstr vect cstr_info] loads an constraint into the system.
    The constraint is neither redundant nor contradictory.
    @raise SystemContradiction if [cstr_info] returns [None]
*)

let xadd_cstr vect cstr_info sys =
 try
    let info = System.find sys vect in
      match merge_cstr_info cstr_info !info with
	  | None       -> raise (SystemContradiction  (And(cstr_info.prf, (!info).prf)))
	  | Some info' -> info := info'
      with
	| Not_found -> System.replace  sys vect (ref cstr_info)

exception TimeOut
         
let xadd_cstr vect cstr_info sys = 
  if debug && Int.equal (System.length sys mod 1000) 0 then (print_string "*" ; flush stdout) ;
 if System.length sys < !max_nb_cstr
 then xadd_cstr vect cstr_info sys
 else raise TimeOut

type cstr_ext =
    | Contradiction (** The constraint is contradictory.
			Typically, a [SystemContradiction] exception will be raised. *)
    | Redundant  (** The constrain is redundant.
		     Typically, the constraint will be dropped *)
    | Cstr of vector * cstr_info (** Taken alone, the constraint is neither contradictory nor redundant.
				     Typically, it will be added to the constraint system. *)

(** [normalise_cstr] : vector -> cstr_info -> cstr_ext *)
let normalise_cstr vect cinfo =
  match norm_itv cinfo.bound with
    | None -> Contradiction
    | Some (l,r) ->
	match vect with
	  | [] -> if Itv.in_bound (l,r) (Int 0) then Redundant else Contradiction
	  | (_,n)::_ ->  Cstr(
	      (if n <>/ Int 1 then List.map (fun (x,nx) -> (x,nx // n)) vect else vect),
			     let divn x = x // n in
			       if Int.equal (sign_num n) 1
                               then{cinfo with bound = (Option.map divn l , Option.map  divn r) }
                               else {cinfo with pos = cinfo.neg ; neg = cinfo.pos ; bound = (Option.map divn r , Option.map divn l)})

(** For compatibility, there is an external representation of constraints *)


let eval_op = function
  | Eq -> (=/)
  | Ge ->  (>=/)

let count v =
  let rec count n p v =
    match v with
      | [] -> (n,p)
      | (_,vl)::v -> let sg = sign_num vl in
		       assert (sg <> 0) ;
	  if Int.equal sg 1 then count n (p+1) v else count (n+1) p v in
    count 0 0 v


let norm_cstr {coeffs = v ; op = o ; cst = c} idx =
  let (n,p) = count v in

  normalise_cstr v {pos = p ; neg = n ; bound =
  (match o with
	| Eq -> Some c , Some c
	| Ge -> Some c , None) ;
	    prf = Assum idx }


(** [load_system l] takes a list of constraints of type [cstr_compat]
    @return a system of constraints
    @raise SystemContradiction if a contradiction is found
*)
let load_system l =

  let sys = System.create 1000 in

  let li = List.mapi (fun i e -> (e,i)) l in

  let vars = List.fold_left (fun vrs (cstr,i) ->
    match norm_cstr cstr i with
      | Contradiction -> raise (SystemContradiction (Assum i))
      | Redundant      -> vrs
      | Cstr(vect,info) ->
	  xadd_cstr  vect info sys ;
	  List.fold_left (fun s (v,_) -> ISet.add v s) vrs cstr.coeffs) ISet.empty li   in

    {sys = sys ;vars = vars}

let system_list sys =
  let { sys = s ; vars  = v } = sys in
    System.fold (fun k bi l -> (k, !bi)::l) s []


(** [add (v1,c1)  (v2,c2)  ]
    precondition:  (c1 <>/ Int 0 && c2 <>/ Int 0)
    @return a pair [(v,ln)] such that
    [v] is the sum of vector [v1] divided by [c1] and vector [v2] divided by [c2]
    Note that the resulting vector is not normalised.
*)

let add (v1,c1)  (v2,c2)  =
    assert (c1 <>/ Int 0 && c2 <>/ Int 0) ;

  let rec xadd v1 v2  =
    match v1 , v2 with
      | (x1,n1)::v1' , (x2,n2)::v2' ->
	  if Int.equal x1 x2
	  then
	    let n' = (n1 // c1) +/ (n2 // c2) in
	      if n' =/ Int 0 then xadd v1' v2'
	      else
		let res = xadd v1' v2'  in
		  (x1,n') ::res
	  else if x1 < x2
	  then let res = xadd v1' v2   in
		 (x1, n1 // c1)::res
	  else let res = xadd v1 v2'  in
		 (x2, n2 // c2)::res
      |  [] , [] -> []
      |  [] ,  _ -> List.map (fun (x,vl) -> (x,vl // c2)) v2
      |  _  , [] -> List.map (fun (x,vl) -> (x,vl // c1)) v1 in

  let res = xadd v1 v2 in
    (res, count res)

let add (v1,c1)   (v2,c2)  =
  let res = add (v1,c1)   (v2,c2)  in
    (*    Printf.printf "add(%a,%s,%a,%s) -> %a\n" pp_vect v1 (string_of_num c1) pp_vect v2 (string_of_num c2) pp_vect (fst res) ;*)
    res

(** To perform Fourier elimination, constraints are categorised depending on the sign of the variable to eliminate. *)

(** [split x vect info (l,m,r)]
    @param v is the variable to eliminate
    @param l contains constraints such that (e + a*x) // a >= c / a
    @param r contains constraints such that (e + a*x) // - a >= c / -a
    @param m contains constraints which do not mention [x]
*)

let split x (vect: vector) info (l,m,r) =
    match get x vect with
      | None -> (* The constraint does not mention [x], store it in m *)
	  (l,(vect,info)::m,r)
      | Some vl -> (* otherwise *)

          let cons_bound lst bd =
            match  bd with
              | None -> lst
              | Some bnd -> (vl,vect,{info with bound = Some bnd,None})::lst in

          let lb,rb = info.bound in
            if Int.equal (sign_num vl) 1
            then  (cons_bound l lb,m,cons_bound r rb)
            else (* sign_num vl = -1 *)
              (cons_bound l rb,m,cons_bound r lb)


(** [project vr sys] projects system [sys] over the set of variables [ISet.remove vr sys.vars ].
    This is a one step Fourier elimination.
*)
let project vr sys =

  let (l,m,r)  = System.fold (fun vect rf l_m_r -> split vr vect !rf l_m_r) sys.sys  ([],[],[])  in

  let new_sys = System.create (System.length sys.sys) in

    (* Constraints in [m] belong to the projection - for those [vr] is already projected out *)
    List.iter (fun  (vect,info) -> System.replace new_sys vect (ref info) )  m ;

    let elim (v1,vect1,info1) (v2,vect2,info2) =
      let {neg = n1 ; pos = p1 ; bound = bound1 ; prf = prf1} = info1
      and {neg = n2 ; pos = p2 ; bound = bound2 ; prf = prf2} = info2 in

      let bnd1 = Option.get (fst bound1)
      and bnd2 = Option.get (fst bound2) in
      let bound = (bnd1 // v1) +/ (bnd2 // minus_num v2) in
      let vres,(n,p) = add (vect1,v1) (vect2,minus_num v2)  in
        (vres,{neg = n ; pos = p ; bound = (Some bound, None); prf = Elim(vr,info1.prf,info2.prf)}) in

      List.iter(fun  l_elem -> List.iter (fun r_elem ->
        let (vect,info) = elim l_elem r_elem in
	  match normalise_cstr vect info with
	    | Redundant -> ()
	    | Contradiction -> raise (SystemContradiction  info.prf)
	    | Cstr(vect,info)   -> xadd_cstr vect info new_sys) r ) l;
      {sys = new_sys ; vars = ISet.remove  vr sys.vars}


(** [project_using_eq] performs elimination by pivoting using an equation.
    This is the counter_part of the [elim] sub-function of [!project].
    @param vr is the variable to be used as pivot
    @param c is the coefficient of variable [vr] in vector [vect]
    @param len is the length of the equation
    @param bound is the bound of the equation
    @param prf is the proof of the equation
*)

let project_using_eq vr c vect bound  prf (vect',info') =
    match get vr vect' with
    | Some c2 ->
	let c1 = if c2 >=/ Int 0 then minus_num c else c in

	let c2 = abs_num c2 in

	let (vres,(n,p)) = add (vect,c1) (vect', c2)  in

	let cst = bound // c1 in

	let bndres =
	  let f x = cst +/ x // c2 in
	  let (l,r) = info'.bound in
            (Option.map f l , Option.map f r) in

	  (vres,{neg = n ; pos = p ; bound = bndres ; prf = Elim(vr,prf,info'.prf)})
    | None -> (vect',info')

let elim_var_using_eq vr vect cst  prf sys =
  let c = Option.get (get vr vect) in

  let elim_var = project_using_eq vr c vect cst prf  in

  let  new_sys  =  System.create (System.length sys.sys) in

    System.iter(fun vect iref ->
      let (vect',info') = elim_var (vect,!iref) in
	match normalise_cstr vect' info' with
	    | Redundant -> ()
	    | Contradiction -> raise (SystemContradiction info'.prf)
	    | Cstr(vect,info')   -> xadd_cstr vect info' new_sys) sys.sys ;

    {sys = new_sys ; vars = ISet.remove  vr sys.vars}


(** [size sys] computes the number of entries in the system of constraints *)
let size sys = System.fold (fun v iref s -> s + (!iref).neg + (!iref).pos) sys 0

module IMap = CMap.Make(Int)

(** [eval_vect map vect] evaluates vector [vect] using the values of [map].
    If [map] binds all the variables of [vect], we get
    [eval_vect map [(x1,v1);...;(xn,vn)] = (IMap.find x1 map * v1) + ... + (IMap.find xn map) * vn , []]
    The function returns as second argument, a sub-vector consisting in the variables that are not in [map]. *)

let  eval_vect map vect =
  let rec xeval_vect vect sum rst =
    match vect with
      | [] -> (sum,rst)
      | (v,vl)::vect ->
	  try
	    let val_v = IMap.find v map in
	      xeval_vect vect (sum +/ (val_v */ vl)) rst
	  with
	      Not_found -> xeval_vect vect sum ((v,vl)::rst) in
    xeval_vect vect (Int 0) []


(** [restrict_bound n sum itv] returns the interval of [x]
    given that (fst itv) <=  x * n + sum <= (snd itv) *)
let restrict_bound n sum (itv:interval) =
  let f x  = (x -/ sum) // n in
  let l,r = itv in
    match sign_num n with
      | 0 -> if in_bound itv sum
	then (None,None) (* redundant *)
	else failwith "SystemContradiction"
      | 1 ->  Option.map f l , Option.map f r
      | _ -> Option.map f r , Option.map f l


(** [bound_of_variable map v sys] computes the interval of [v] in
    [sys] given a mapping [map] binding all the other variables *)
let bound_of_variable map v sys =
  System.fold (fun vect iref bnd  ->
    let sum,rst = eval_vect  map vect in
    let vl = match get v rst with
      | None -> Int 0
      | Some v -> v in
      match inter bnd (restrict_bound vl sum (!iref).bound) with
	| None -> failwith "bound_of_variable: impossible"
	| Some itv -> itv) sys  (None,None)


(** [pick_small_value bnd] picks a value being closed to zero within the interval *)
let pick_small_value bnd =
  match bnd with
    | None , None   ->  Int 0
    | None , Some i ->  if  (Int 0) <=/ (floor_num  i) then Int 0 else floor_num i
    | Some i,None   ->  if i <=/ (Int 0) then Int 0 else ceiling_num i
    | Some i,Some j ->
	if i <=/ Int 0 && Int 0 <=/ j
	then Int 0
	else if ceiling_num i <=/ floor_num j
	then ceiling_num i (* why not *) else i


(** [solution s1 sys_l  = Some(sn,\[(vn-1,sn-1);...; (v1,s1)\]\@sys_l)]
    then [sn] is a  system which contains only [black_v] -- if it existed in [s1]
    and [sn+1] is obtained by projecting [vn] out of [sn]
    @raise SystemContradiction if  system [s] has no solution
*)

let solve_sys black_v choose_eq choose_variable sys sys_l =

  let rec solve_sys sys sys_l =
    if debug then Printf.printf "S #%i size %i\n" (System.length sys.sys) (size sys.sys);

    let eqs = choose_eq sys in
      try
	let (v,vect,cst,ln) =  fst (List.find (fun ((v,_,_,_),_) -> v <> black_v) eqs) in
	  if debug then
	    (Printf.printf "\nE %a = %s variable %i\n" pp_vect vect (string_of_num cst) v ;
	     flush stdout);
	  let sys' = elim_var_using_eq v vect cst ln sys in
	    solve_sys sys' ((v,sys)::sys_l)
    with Not_found ->
      let vars = choose_variable  sys in
	try
	  let (v,est) =  (List.find (fun (v,_) -> v <> black_v) vars) in
	    if debug then (Printf.printf "\nV : %i estimate %f\n" v est ; flush stdout) ;
	    let sys' =  project v sys in
	      solve_sys sys' ((v,sys)::sys_l)
	with Not_found ->  (* we are done *) Inl (sys,sys_l)  in
    solve_sys sys sys_l




let  solve black_v choose_eq choose_variable cstrs =

  try
    let sys = load_system cstrs in
      if debug then Printf.printf "solve :\n %a" pp_system sys.sys ; 
      solve_sys black_v choose_eq choose_variable sys []
  with SystemContradiction prf -> Inr prf


(** The  purpose of module [EstimateElimVar] is to try to estimate the cost of eliminating a variable.
    The output is an ordered list of (variable,cost).
*)

module EstimateElimVar =
struct
  type sys_list = (vector * cstr_info) list

  let abstract_partition (v:int) (l: sys_list) =

    let rec xpart (l:sys_list) (ltl:sys_list) (n:int list) (z:int) (p:int list) =
      match l with
        | [] -> (ltl, n,z,p)
        | (l1,info) ::rl ->
            match  l1 with
            | [] -> xpart rl (([],info)::ltl) n (info.neg+info.pos+z) p
            | (vr,vl)::rl1 ->
		if Int.equal v vr
		then
		  let cons_bound lst bd =
		    match  bd with
		      | None -> lst
		      | Some bnd -> info.neg+info.pos::lst in

		  let lb,rb = info.bound in
		    if Int.equal (sign_num vl) 1
		    then  xpart rl ((rl1,info)::ltl) (cons_bound n lb) z (cons_bound p rb)
		    else  xpart rl ((rl1,info)::ltl) (cons_bound n rb) z (cons_bound p lb)
		else
		  (* the variable is greater *)
		  xpart rl ((l1,info)::ltl) n (info.neg+info.pos+z) p

    in
    let (sys',n,z,p) =  xpart l [] [] 0 []  in

    let ln = float_of_int (List.length n) in
    let sn = float_of_int (List.fold_left (+) 0 n) in
    let lp = float_of_int (List.length p) in
    let sp = float_of_int (List.fold_left (+) 0 p) in
      (sys',  float_of_int z +.  lp *.  sn +.  ln *.  sp -. lp*.ln)


  let choose_variable   sys =
    let {sys = s ; vars = v} = sys in

    let sl = system_list sys in

    let evals  = fst
      (ISet.fold (fun v (eval,s) -> let ts,vl = abstract_partition v s  in
                                      ((v,vl)::eval, ts)) v ([],sl)) in

      List.sort (fun x y -> compare_float (snd x) (snd y) ) evals


end
open EstimateElimVar

(** The  module [EstimateElimEq] is similar to [EstimateElimVar] but it orders equations.
*)
module EstimateElimEq =
struct

  let itv_point bnd =
    match bnd with
      |(Some a, Some b) -> a =/ b
      | _   -> false

  let rec unroll_until v l =
    match l with
      | [] -> (false,[])
      | (i,_)::rl -> if Int.equal i v
	then (true,rl)
	else if i < v then unroll_until v rl else (false,l)


  let rec choose_simple_equation eqs = 
    match eqs with
      | [] -> None
      | (vect,a,prf,ln)::eqs -> 
	  match vect with 
	    | [i,_] -> Some (i,vect,a,prf,ln)
	    |   _   -> choose_simple_equation eqs 



  let choose_primal_equation eqs sys_l =

    (* Counts the number of equations referring to variable [v] --
       It looks like nb_cst is dead...
    *)
    let is_primal_equation_var v =
      List.fold_left (fun nb_eq (vect,info) ->
	if fst (unroll_until v vect)
	then if itv_point  info.bound then nb_eq +  1 else nb_eq
	else nb_eq) 0 sys_l in

    let rec find_var vect =
      match vect with
	| [] -> None
	| (i,_)::vect ->
	    let nb_eq = is_primal_equation_var i in
	      if Int.equal nb_eq 2 
	      then Some i else find_var vect in

    let rec find_eq_var eqs =
      match eqs with
	| [] -> None
	| (vect,a,prf,ln)::l ->
	    match find_var vect with
		| None -> find_eq_var l
		| Some r -> Some (r,vect,a,prf,ln)
    in
      match choose_simple_equation eqs with
	| None -> find_eq_var eqs
	| Some res -> Some res



  let choose_equality_var  sys =

    let sys_l = system_list sys in

    let equalities = List.fold_left
      (fun  l (vect,info) ->
	match  info.bound with
	  | Some a , Some b ->
	      if a =/ b then (* This an equation *)
		(vect,a,info.prf,info.neg+info.pos)::l else l
	  |   _ -> l
      ) [] sys_l  in

    let rec estimate_cost v ct sysl acc tlsys =
      match sysl with
	| [] -> (acc,tlsys)
	| (l,info)::rsys ->
	    let ln = info.pos + info.neg in
	    let (b,l) = unroll_until v l in
	    match b with
	      | true ->
		  if itv_point info.bound
		  then estimate_cost  v ct rsys (acc+ln) ((l,info)::tlsys) (* this is free *)
		  else estimate_cost v ct rsys (acc+ln+ct) ((l,info)::tlsys)  (* should be more ? *)
	      | false -> estimate_cost v ct rsys (acc+ln) ((l,info)::tlsys) in

      match choose_primal_equation equalities sys_l with
	| None ->
	    let cost_eq eq const prf ln acc_costs =

	      let rec cost_eq eqr sysl costs =
		match eqr with
		  | [] -> costs
		  | (v,_) ::eqr -> let (cst,tlsys) = estimate_cost v (ln-1) sysl 0 [] in
				     cost_eq eqr tlsys (((v,eq,const,prf),cst)::costs) in
		cost_eq eq sys_l acc_costs     in

	    let all_costs = List.fold_left (fun all_costs (vect,const,prf,ln) -> cost_eq vect const prf ln all_costs) [] equalities in

	      (*      pp_list (fun o ((v,eq,_,_),cst) -> Printf.fprintf o "((%i,%a),%i)\n" v pp_vect eq cst) stdout all_costs ; *)

	      List.sort (fun x y -> Int.compare (snd x) (snd y) ) all_costs
	| Some (v,vect, const,prf,_) -> [(v,vect,const,prf),0]


end
open EstimateElimEq

module Fourier =
struct

  let optimise vect l =
    (* We add a dummy (fresh) variable for vector *)
    let fresh =
      List.fold_left (fun fr c -> Pervasives.max fr (Vect.fresh c.coeffs)) 0 l in
    let cstr = {
      coeffs = Vect.set fresh (Int (-1)) vect ;
      op = Eq ;
      cst = (Int 0)} in
      match solve fresh choose_equality_var choose_variable (cstr::l) with
	| Inr prf -> None (* This is an unsatisfiability proof *)
	| Inl (s,_) ->
	    try
	      Some (bound_of_variable IMap.empty fresh s.sys)
	    with x when CErrors.noncritical x ->
	      Printf.printf "optimise Exception : %s" (Printexc.to_string x);
              None


  let find_point cstrs =

    match solve max_int choose_equality_var choose_variable cstrs with
      | Inr prf -> Inr prf
      | Inl (_,l) ->

	let rec rebuild_solution l map =
	  match l with
	    | [] -> map
	    | (v,e)::l ->
		let itv = bound_of_variable map v e.sys in
		let map = IMap.add v (pick_small_value itv) map in
		  rebuild_solution l map
	in

	let map = rebuild_solution l IMap.empty in
	  let vect = List.rev (IMap.fold (fun v i vect -> (v,i)::vect) map []) in
(*	    Printf.printf "SOLUTION %a" pp_vect vect ; *)
	  let res = Inl vect in
	    res


end


module Proof =
struct




(** A proof term in the sense of a ZMicromega.RatProof is a positive combination of the hypotheses which leads to a contradiction.
    The proofs constructed by Fourier elimination are more like execution traces:
         - certain facts are recorded but are useless
         - certain inferences are implicit.
    The following code implements proof reconstruction.
*)
  let add x y = fst (add x y)


  let forall_pairs f l1 l2 =
    List.fold_left (fun acc e1 ->
      List.fold_left (fun acc e2 ->
	match f e1 e2 with
	  | None -> acc
	  | Some v -> v::acc) acc l2) [] l1


  let add_op x y =
    match x , y with
      | Eq , Eq -> Eq
      |     _   -> Ge


  let pivot v (p1,c1) (p2,c2) =
    let {coeffs = v1 ; op = op1 ; cst = n1} = c1
    and {coeffs = v2 ; op = op2 ; cst = n2} = c2 in

      match Vect.get v v1 , Vect.get v v2 with
        | None , _ | _ , None -> None
        | Some a   , Some b   ->
            if Int.equal ((sign_num a) * (sign_num b)) (-1)
            then 
	      Some (add (p1,abs_num a) (p2,abs_num b) ,
                      {coeffs = add (v1,abs_num a) (v2,abs_num b) ;
                       op = add_op op1 op2 ;
                       cst = n1 // (abs_num a) +/ n2 // (abs_num b) })
            else if op1 == Eq
            then Some (add (p1,minus_num (a // b)) (p2,Int 1),
                      {coeffs = add (v1,minus_num (a// b)) (v2 ,Int 1) ;
                       op     = add_op op1 op2;
                       cst    = n1 // (minus_num (a// b)) +/ n2 // (Int 1)})
            else if op2 == Eq
	    then
	      Some (add (p2,minus_num (b // a)) (p1,Int 1),
                   {coeffs = add (v2,minus_num (b// a)) (v1 ,Int 1) ;
                    op     = add_op op1 op2;
                    cst    = n2 // (minus_num (b// a)) +/ n1 // (Int 1)})
	    else  None (* op2 could be Eq ... this might happen *)


  let normalise_proofs l =
    List.fold_left (fun acc (prf,cstr) ->
      match acc with
        | Inr _ -> acc (* I already found a contradiction *)
        | Inl acc ->
            match norm_cstr cstr 0 with
              | Redundant -> Inl acc
              | Contradiction -> Inr (prf,cstr)
              | Cstr(v,info)  -> Inl ((prf,cstr,v,info)::acc)) (Inl []) l


  type oproof = (vector * cstr_compat * num) option

  let merge_proof (oleft:oproof) (prf,cstr,v,info) (oright:oproof) =
    let (l,r) = info.bound in

    let keep p ob bd =
      match ob , bd with
        | None , None -> None
        | None , Some b -> Some(prf,cstr,b)
        | Some _ , None -> ob
        | Some(prfl,cstrl,bl) , Some b -> if p bl b then Some(prf,cstr, b) else ob in

    let oleft  = keep (<=/) oleft l in
    let oright = keep (>=/) oright r in
      (* Now, there might be a contradiction *)
      match oleft , oright with
        | None , _ | _ , None -> Inl (oleft,oright)
        | Some(prfl,cstrl,l) , Some(prfr,cstrr,r) ->
            if l <=/ r
            then Inl (oleft,oright)
            else (* There is a contradiction - it should show up by scaling up the vectors - any pivot should do*)
              match cstrr.coeffs with
                | [] -> Inr (add (prfl,Int 1) (prfr,Int 1), cstrr) (* this is wrong *)
                | (v,_)::_ ->
                    match pivot v (prfl,cstrl) (prfr,cstrr) with
                      | None -> failwith "merge_proof : pivot is not possible"
                      | Some x -> Inr x

let  mk_proof hyps prf =
  (* I am keeping list - I might have a proof for the left bound and a proof for the right bound.
     If I perform aggressive elimination of redundancies, I expect the list to be of length at most 2.
     For each proof list, all the vectors should be of the form a.v for different constants a.
  *)

  let rec mk_proof prf =
    match prf with
      | Assum i -> [ ([i, Int 1] , List.nth hyps i) ]

      | Elim(v,prf1,prf2) ->
          let prfsl = mk_proof prf1
          and prfsr = mk_proof prf2 in
            (* I take only the pairs for which the elimination is meaningful *)
            forall_pairs (pivot v) prfsl prfsr
      | And(prf1,prf2) ->
          let prfsl1 = mk_proof prf1
          and prfsl2 = mk_proof prf2 in
          (* detect trivial redundancies and contradictions *)
            match normalise_proofs (prfsl1@prfsl2) with
              | Inr x -> [x] (* This is a contradiction - this should be the end of the proof *)
              | Inl l -> (* All the vectors are the same *)
                  let prfs =
                    List.fold_left (fun acc e ->
                      match acc with
                        | Inr _ -> acc (* I have a contradiction *)
                        | Inl (oleft,oright) -> merge_proof oleft e oright) (Inl(None,None)) l in
                    match prfs with
                      | Inr x -> [x]
                      | Inl (oleft,oright) ->
			  match oleft , oright with
			    | None , None -> []
			    | None , Some(prf,cstr,_) | Some(prf,cstr,_) , None -> [prf,cstr]
			    | Some(prf1,cstr1,_) , Some(prf2,cstr2,_) -> [prf1,cstr1;prf2,cstr2] in

    mk_proof prf


end

