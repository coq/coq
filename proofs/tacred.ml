
(* $Id$ *)

let is_elim env sigma c =
  let (sp, cl) = destConst c in
  if (evaluable_constant env c) && (defined_constant env c) then begin
    let cb = lookup_constant sp env in 
    (match cb.cONSTEVAL with
       | Some _ -> ()
       | None -> 
	   (match cb.cONSTBODY with
	      | Some{contents=COOKED b} ->
		  cb.cONSTEVAL <- Some(compute_consteval b)
	      | Some{contents=RECIPE _} ->
		  anomalylabstrm "Reduction.is_elim"
		    [< 'sTR"Found an uncooked transparent constant,"; 'sPC ;
		       'sTR"which is supposed to be impossible" >]
	      | _ -> assert false));
    (match (cb.cONSTEVAL) with
       | Some (Some x) -> x
       | Some None -> raise Elimconst
       | _ -> assert false)
  end else 
    raise Elimconst

let make_elim_fun sigma f largs =
  try 
    let (lv,n,b) = is_elim sigma f 
    and ll = List.length largs in 
    if ll < n then raise Redelimination;
    if b then
      let labs,_ = chop_list n largs in
      let p = List.length lv in
      let la' = map_i (fun q aq ->
			 try (Rel (p+1-(index (n+1-q) (List.map fst lv)))) 
			 with Failure _ -> aq) 1
                  (List.map (lift p) labs) 
      in
      it_list_i (fun i c (k,a) -> 
                   DOP2(Lambda,(substl (rev_firstn_liftn (n-k) (-i) la') a),
                   	DLAM(Name(id_of_string"x"),c))) 0 (applistc f la') lv
    else 
      f
  with Elimconst | Failure _ -> 
    raise Redelimination

let rec red_elim_const env sigma k largs =
  if not (evaluable_constant env k) then raise Redelimination;
  let f = make_elim_fun sigma k largs in
  match whd_betadeltaeta_stack sigma (const_value sigma k) largs with
    | (DOPN(MutCase _,_) as mc,lrest) ->
        let (ci,p,c,lf) = destCase mc in
        (special_red_case sigma (construct_const sigma) p c ci lf, lrest)
    | (DOPN(Fix _,_) as fix,lrest) -> 
        let (b,(c,rest)) = 
	  reduce_fix_use_function f (construct_const sigma) fix lrest
        in 
	if b then (nf_beta c, rest) else raise Redelimination
    | _ -> assert false

and construct_const sigma c stack = 
  let rec hnfstack x stack =
    match x with
      | (DOPN(Const _,_)) as k  ->
          (try
             let (c',lrest) = red_elim_const sigma k stack in hnfstack c' lrest
           with Redelimination ->
             if evaluable_const sigma k then 
	       let cval = const_value sigma k in
	       (match cval with
                  | DOPN (CoFix _,_) -> (k,stack)
                  | _                -> hnfstack cval stack) 
             else 
	       raise Redelimination)
      | (DOPN(Abst _,_) as a) ->
          if evaluable_abst a then 
	    hnfstack (abst_value a) stack
          else 
	    raise Redelimination
      | DOP2(Cast,c,_)   -> hnfstack c stack
      | DOPN(AppL,cl)    -> hnfstack (hd_vect cl) (app_tl_vect cl stack)
      | DOP2(Lambda,_,DLAM(_,c)) ->
          (match stack with 
             | [] -> assert false
             | c'::rest -> stacklam hnfstack [c'] c rest)
    | DOPN(MutCase _,_) as c_0 ->
        let (ci,p,c,lf) = destCase c_0 in
        hnfstack (special_red_case sigma (construct_const sigma) p c ci lf) 
	  stack
    | DOPN(MutConstruct _,_) as c_0 -> c_0,stack
    | DOPN(CoFix _,_) as c_0 -> c_0,stack
    | DOPN(Fix (_) ,_) as fix -> 
        let (reduced,(fix,stack')) = reduce_fix hnfstack fix stack in 
	if reduced then hnfstack fix stack' else raise Redelimination
    | _ -> raise Redelimination
  in 
  hnfstack c stack

(* Hnf reduction tactic: *)

let hnf_constr sigma c = 
  let rec redrec x largs =
    match x with
      | DOP2(Lambda,t,DLAM(n,c)) ->
          (match largs with
             | []      -> applist(x,largs)
             | a::rest -> stacklam redrec [a] c rest)
      | DOPN(AppL,cl)   -> redrec (array_hd cl) (array_app_tl cl largs)
      | DOPN(Const _,_) ->
          (try
             let (c',lrest) = red_elim_const sigma x largs in 
	     redrec c' lrest
           with Redelimination ->
             if evaluable_const sigma x then
               let c = const_value sigma x in
	       (match c with 
                  | DOPN(CoFix _,_) -> applist(x,largs)
		  | _ ->  redrec c largs)
             else 
	       applist(x,largs))
      | DOPN(Abst _,_) ->
          if evaluable_abst x then 
	    redrec (abst_value x) largs
          else 
	    applist(x,largs)
      | DOP2(Cast,c,_) -> redrec c largs
      | DOPN(MutCase _,_) ->
          let (ci,p,c,lf) = destCase x in
          (try
             redrec (special_red_case sigma (whd_betadeltaiota_stack sigma) 
		       p c ci lf) largs
           with Redelimination -> 
	     applist(x,largs))
      | (DOPN(Fix _,_)) ->
          let (reduced,(fix,stack)) = 
            reduce_fix (whd_betadeltaiota_stack sigma) x largs
          in 
	  if reduced then redrec fix stack else applist(x,largs)
      | _         -> applist(x,largs)
  in 
  redrec c []

(* Simpl reduction tactic: same as simplify, but also reduces
   elimination constants *)

let whd_nf sigma c = 
  let rec nf_app c stack =
    match c with
      | DOP2(Lambda,c1,DLAM(name,c2))    ->
          (match stack with
             | [] -> (c,[])
             | a1::rest -> stacklam nf_app [a1] c2 rest)
      | DOPN(AppL,cl) -> nf_app (hd_vect cl) (app_tl_vect cl stack)
      | DOP2(Cast,c,_) -> nf_app c stack
      | DOPN(Const _,_) ->
          (try
             let (c',lrest) = red_elim_const sigma c stack in 
	     nf_app c' lrest
           with Redelimination -> 
	     (c,stack))
      | DOPN(MutCase _,_) ->
          let (ci,p,d,lf) = destCase c in
          (try
             nf_app (special_red_case sigma nf_app p d ci lf) stack
           with Redelimination -> 
	     (c,stack))
      | DOPN(Fix _,_) ->
          let (reduced,(fix,rest)) = reduce_fix nf_app c stack in 
	  if reduced then nf_app fix rest else (fix,stack)
      | _ -> (c,stack)
  in 
  applist (nf_app c [])

let nf sigma c = strong (whd_nf sigma) c

(* Generic reduction: reduction functions used in reduction tactics *)

type red_expr =
  | Red
  | Hnf
  | Simpl
  | Cbv of flags
  | Lazy of flags
  | Unfold of (int list * section_path) list
  | Fold of constr list
  | Change of constr
  | Pattern of (int list * constr * constr) list

let reduction_of_redexp = function
  | Red -> red_product
  | Hnf -> hnf_constr
  | Simpl -> nf
  | Cbv f -> cbv_norm_flags f
  | Lazy f -> clos_norm_flags f
  | Unfold ubinds -> unfoldn ubinds
  | Fold cl -> fold_commands cl
  | Change t -> (fun _ _ -> t)
  | Pattern lp -> (fun _ -> pattern_occs lp)
