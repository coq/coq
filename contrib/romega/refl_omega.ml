(*************************************************************************

   PROJET RNRT Calife - 2001
   Author: Pierre Crégut - France Télécom R&D
   Licence : LGPL version 2.1

 *************************************************************************)

open Const_omega


(* \section{Utilitaires} *)

let debug = ref false 

let (>>) = Tacticals.tclTHEN

let index t = 
  let rec loop i = function
    | (u::l) -> if u = t then i else loop (i+1) l
    | [] -> raise Not_found in
  loop 0

let mkApp = Term.mkApp

(* \section{Formules réifiables} *)
type oformula =
  | Oplus of oformula * oformula
  | Ominus of oformula * oformula
  | Oinv of  oformula
  | Otimes of oformula * oformula
  | Oatom of  int
  | Oz of int
  | Oufo of oformula

let rec oprint = function 
  | Oplus(t1,t2) -> 
      print_string "("; oprint t1; print_string "+"; 
      oprint t2; print_string ")"
  | Ominus(t1,t2) -> 
      print_string "("; oprint t1; print_string "-"; 
      oprint t2; print_string ")"
  | Oinv t -> print_string "~"; oprint t
  | Otimes (t1,t2) -> 
      print_string "("; oprint t1; print_string "*"; 
      oprint t2; print_string ")"
  | Oatom i ->print_string "V";  print_int i
  | Oz i -> print_int i
  | Oufo f -> print_string "?"

(* \section{Tables} *)

let get_hyp env_hyp id = 
  try index id env_hyp 
  with Not_found -> failwith ("get_hyp " ^ string_of_int id)

let tag_equation,tag_of_equation, clear_tags  =
  let l = ref ([]:(int * Names.identifier) list) in
  (fun id h -> l := (h,id):: !l),
  (fun h -> try List.assoc h !l with Not_found-> failwith "tag_hypothesis"),
  (fun () -> l := [])

let add_atom t env =
  try index t env, env
  with Not_found ->  List.length env, (env@[t])

let get_atom v env = 
  try List.nth v env with _ -> failwith "get_atom"

(* compilation des environnements *)

let intern_id, intern_id_force, unintern_id, clear_intern =
  let c = ref 0 in
  let l = ref [] in
  (fun t -> 
     try List.assoc t !l 
     with Not_found -> incr c; let v = !c in l := (t,v)::!l; v),
  (fun t v -> l := (t,v) :: !l),
  (fun i ->
    let rec loop = function 
	[] -> failwith "unintern" 
      | ((t,j)::l) -> if i = j then t else loop l in
    loop !l),
  (fun () -> c := 0; l := [])

(* Le poids d'un terme : fondamental pour classer les variables *)

let rec weight = function
  | Oatom _ as c -> intern_id c
  | Oz _ -> -1
  | Oinv c -> weight c
  | Otimes(c,_) -> weight c
  | Oplus _ -> failwith "weight"
  | Ominus _ -> failwith "weight minus"
  | Oufo _ -> -1

(* \section{Passage entre oformules et 
               représentation interne de Omega} *)

(* \subsection{Oformula vers Omega} *)

let compile name kind = 
  let rec loop accu = function
    | Oplus(Otimes(v,Oz n),r) -> 
	loop ({Omega.v=intern_id v; Omega.c=n} :: accu) r
    | Oz n ->
	let id = Omega.new_id () in
	tag_equation name id;
	{Omega.kind = kind; Omega.body = List.rev accu; 
	 Omega.constant = n; Omega.id = id}
    | t -> print_string "CO"; oprint t; failwith "compile_equation" in
  loop []

(* \subsection{Omega vers Oformula} *)

let rec decompile af = 
  let rec loop = function
    | ({Omega.v=v; Omega.c=n}::r) -> Oplus(Otimes(unintern_id v,Oz n),loop r) 
    | [] -> Oz af.Omega.constant in
  loop af.Omega.body

(* \subsection{Oformula vers COQ reel} *)

let rec coq_of_formula env t =
  let rec loop = function
  | Oplus (t1,t2) -> mkApp(Lazy.force coq_Zplus, [| loop t1; loop t2 |])
  | Oinv t -> mkApp(Lazy.force coq_Zopp, [| loop t |])
  | Otimes(t1,t2) -> mkApp(Lazy.force coq_Zmult, [| loop t1; loop t2 |])
  | Oz v ->  mk_Z v
  | Oufo t -> loop t
  | Oatom i -> get_atom env i
  | Ominus(t1,t2) -> mkApp(Lazy.force coq_Zminus, [| loop t1; loop t2 |]) in
  loop t

(* \subsection{Oformula vers COQ reifié} *)

let rec val_of_formula = function
  | Oplus (t1,t2) ->
      mkApp(Lazy.force coq_t_plus, [| val_of_formula t1; val_of_formula t2 |])
  | Oinv t ->
      mkApp(Lazy.force coq_t_opp, [| val_of_formula t |])
  | Otimes(t1,t2) ->
      mkApp(Lazy.force coq_t_mult, [| val_of_formula t1; val_of_formula t2 |])
  | Oz v ->  mkApp (Lazy.force coq_t_nat, [| mk_Z v |])
  | Oufo t -> val_of_formula t
  | Oatom i -> mkApp(Lazy.force coq_t_var, [| mk_nat i |])
  | Ominus(t1,t2) ->
      mkApp(Lazy.force coq_t_minus, [| val_of_formula t1; val_of_formula t2 |])

(* \subsection{Omega vers COQ réifié} *)

let val_of body constant = 
  let coeff_constant = 
    mkApp(Lazy.force coq_t_nat, [| mk_Z constant |]) in
  let mk_coeff {Omega.c=c; Omega.v=v} t =
    let coef = mkApp(Lazy.force coq_t_mult,
		     [|val_of_formula (unintern_id v );
		       mkApp(Lazy.force coq_t_nat, [| mk_Z c |]) |]) in
    mkApp(Lazy.force coq_t_plus, [|coef; t |]) in
  List.fold_right mk_coeff body coeff_constant

(* \section{Opérations sur les équations}
Ces fonctions préparent les traces utilisées par la tactique réfléchie
pour faire des opérations de normalisation sur les équations.  *)

(* \subsection{Multiplication par un scalaire} *)
let rec scalar n = function
   Oplus(t1,t2) -> 
     let tac1,t1' = scalar  n t1 and 
         tac2,t2' = scalar  n t2 in
     do_list [Lazy.force coq_c_mult_plus_distr; do_both tac1 tac2], 
     Oplus(t1',t2')
 | Oinv t ->
     do_list [Lazy.force coq_c_mult_opp_left], Otimes(t,Oz(-n))
 | Otimes(t1,Oz x) -> 
     do_list [Lazy.force coq_c_mult_assoc_reduced], Otimes(t1,Oz (n*x))
 | Otimes(t1,t2) -> 
     Util.error "Omega: Can't solve a goal with non-linear products"
 | (Oatom _ as t) -> do_list [], Otimes(t,Oz n)
 | Oz i -> do_list [Lazy.force coq_c_reduce],Oz(n*i)
 | (Oufo _ as t)-> do_list [], Oufo (Otimes(t,Oz n))
 | Ominus _ -> failwith "scalar minus"

(* \subsection{Propagation de l'inversion} *)
let rec negate = function
   Oplus(t1,t2) -> 
     let tac1,t1' = negate t1 and 
         tac2,t2' = negate t2 in
     do_list [Lazy.force coq_c_opp_plus ; (do_both tac1 tac2)],
     Oplus(t1',t2')
 | Oinv t ->
     do_list [Lazy.force coq_c_opp_opp], t
 | Otimes(t1,Oz x) -> 
     do_list [Lazy.force coq_c_opp_mult_r], Otimes(t1,Oz (-x))
 | Otimes(t1,t2) -> 
     Util.error "Omega: Can't solve a goal with non-linear products"
 | (Oatom _ as t) ->
     do_list [Lazy.force coq_c_opp_one], Otimes(t,Oz(-1))
 | Oz i -> do_list [Lazy.force coq_c_reduce] ,Oz(-i)
 | Oufo c -> do_list [], Oufo (Oinv c)
 | Ominus _ -> failwith "negate minus"

let rec norm l = (List.length l)

(* \subsection{Mélange (fusion) de deux équations} *)

let rec shuffle_path k1 e1 k2 e2 =
  let rec loop = function
      (({Omega.c=c1;Omega.v=v1}::l1) as l1'),
      (({Omega.c=c2;Omega.v=v2}::l2) as l2') ->
	if v1 = v2 then
          if k1*c1 + k2 * c2 = 0 then (
            Lazy.force coq_f_cancel :: loop (l1,l2))
          else (
            Lazy.force coq_f_equal :: loop (l1,l2) )
	else if v1 > v2 then (
	  Lazy.force coq_f_left :: loop(l1,l2'))
	else (
	  Lazy.force coq_f_right :: loop(l1',l2))
    | ({Omega.c=c1;Omega.v=v1}::l1), [] -> 
	  Lazy.force coq_f_left :: loop(l1,[])
    | [],({Omega.c=c2;Omega.v=v2}::l2) -> 
	  Lazy.force coq_f_right :: loop([],l2)
    | [],[] -> flush stdout; [] in
  mk_shuffle_list (loop (e1,e2))

let rec shuffle (t1,t2) = 
  match t1,t2 with
    Oplus(l1,r1), Oplus(l2,r2) ->
      if weight l1 > weight l2 then 
	let l_action,t' = shuffle (r1,t2) in
	do_list [Lazy.force coq_c_plus_assoc_r;do_right l_action], Oplus(l1,t')
      else 
	let l_action,t' = shuffle (t1,r2) in
	do_list [Lazy.force coq_c_plus_permute;do_right l_action], Oplus(l2,t')
  | Oplus(l1,r1), t2 -> 
      if weight l1 > weight t2 then
        let (l_action,t') = shuffle  (r1,t2) in
	do_list [Lazy.force coq_c_plus_assoc_r;do_right l_action],Oplus(l1, t')
      else do_list [Lazy.force coq_c_plus_sym], Oplus(t2,t1)
  | t1,Oplus(l2,r2) -> 
      if weight l2 > weight t1 then
        let (l_action,t') = shuffle (t1,r2) in
	do_list [Lazy.force coq_c_plus_permute;do_right l_action], Oplus(l2,t')
      else do_list [],Oplus(t1,t2)
  | Oz t1,Oz t2 ->
      do_list [Lazy.force coq_c_reduce], Oz(t1+t2)
  | t1,t2 ->
      if weight t1 < weight t2 then
	do_list [Lazy.force coq_c_plus_sym], Oplus(t2,t1)
      else do_list [],Oplus(t1,t2)

(* \subsection{Fusion avec réduction} *)
let shrink_pair f1 f2 =
  begin match f1,f2 with
     Oatom v,Oatom _ -> 
       Lazy.force coq_c_red1, Otimes(Oatom v,Oz 2)
   | Oatom v, Otimes(_,c2) -> 
       Lazy.force coq_c_red2, Otimes(Oatom v,Oplus(c2,Oz 1))
   | Otimes (v1,c1),Oatom v -> 
       Lazy.force coq_c_red3, Otimes(Oatom v,Oplus(c1,Oz 1))
   | Otimes (Oatom v,c1),Otimes (v2,c2) ->
       Lazy.force coq_c_red4, Otimes(Oatom v,Oplus(c1,c2))
   | t1,t2 -> 
       oprint t1; print_newline (); oprint t2; print_newline (); 
       flush Pervasives.stdout; Util.error "shrink.1"
  end

(* \subsection{Calcul d'une sous formule constante} *)
let reduce_factor = function
   Oatom v ->
     let r = Otimes(Oatom v,Oz 1) in
       [Lazy.force coq_c_red0],r
  | Otimes(Oatom v,Oz n) as f -> [],f
  | Otimes(Oatom v,c) ->
      let rec compute = function
          Oz n -> n
	| Oplus(t1,t2) -> compute t1 + compute t2 
	| _ -> Util.error "condense.1" in
	[Lazy.force coq_c_reduce], Otimes(Oatom v,Oz(compute c))
  | t -> Util.error "reduce_factor.1"

(* \subsection{Réordonancement} *)

let rec condense = function
    Oplus(f1,(Oplus(f2,r) as t)) ->
      if weight f1 = weight f2 then begin
	let shrink_tac,t = shrink_pair f1 f2 in
	let assoc_tac = Lazy.force coq_c_plus_assoc_l in
	let tac_list,t' = condense (Oplus(t,r)) in
	assoc_tac :: do_left (do_list [shrink_tac]) :: tac_list, t'
      end else begin
	let tac,f = reduce_factor f1 in
	let tac',t' = condense t in 
	[do_both (do_list tac) (do_list tac')], Oplus(f,t') 
      end
  | (Oplus(f1,Oz n) as t) -> 
      let tac,f1' = reduce_factor f1 in 
      [do_left (do_list tac)],Oplus(f1',Oz n)
  | Oplus(f1,f2) -> 
      if weight f1 = weight f2 then begin
	let tac_shrink,t = shrink_pair f1 f2 in
	let tac,t' = condense t in
	tac_shrink :: tac,t'
      end else begin
	let tac,f = reduce_factor f1 in
	let tac',t' = condense f2 in 
	[do_both (do_list tac) (do_list tac')],Oplus(f,t') 
      end
  | (Oz _ as t)-> [],t
  | t -> 
      let tac,t' = reduce_factor t in
      let final = Oplus(t',Oz 0) in
      tac @ [Lazy.force coq_c_red6], final

(* \subsection{Elimination des zéros} *)

let rec clear_zero = function
   Oplus(Otimes(Oatom v,Oz 0),r) ->
     let tac',t = clear_zero r in
     Lazy.force coq_c_red5 :: tac',t
  | Oplus(f,r) -> 
      let tac,t = clear_zero r in 
      (if tac = [] then [] else [do_right (do_list tac)]),Oplus(f,t)
  | t -> [],t;;

(* \section{Transformation des hypothèses} *)

let rec reduce = function
    Oplus(t1,t2) ->
      let t1', trace1 = reduce t1 in
      let t2', trace2 = reduce t2 in
      let trace3,t' = shuffle (t1',t2') in
      t', do_list [do_both trace1 trace2; trace3]
  | Ominus(t1,t2) ->
      let t,trace = reduce (Oplus(t1, Oinv t2)) in
      t, do_list [Lazy.force coq_c_minus; trace]
  | Otimes(t1,t2) as t ->
      let t1', trace1 = reduce t1 in
      let t2', trace2 = reduce t2 in
      begin match t1',t2' with
      | (_, Oz n) ->
	  let tac,t' = scalar n t1' in
	  t', do_list [do_both trace1 trace2; tac]
      | (Oz n,_) ->
	  let tac,t' = scalar n t2' in
	  t', do_list [do_both trace1 trace2; Lazy.force coq_c_mult_sym; tac]
      | _ -> Oufo t, Lazy.force coq_c_nop
      end
  | Oinv t ->
      let t',trace = reduce  t in
      let trace',t'' = negate t' in
      t'', do_list [do_left trace; trace']
  | (Oz _ | Oatom _ | Oufo _) as t -> t, Lazy.force coq_c_nop

let rec ocompile env t =
  try match destructurate t with
  | Kapp("Zplus",[t1;t2]) ->
      let t1',env1 = ocompile env  t1 in
      let t2',env2 = ocompile env1 t2 in
      (Oplus (t1',t2'), env2)
  | Kapp("Zminus",[t1;t2]) ->
      let t1',env1 = ocompile env  t1 in
      let t2',env2 = ocompile env1 t2 in
      (Ominus (t1',t2'), env2)
  | Kapp("Zmult",[t1;t2]) ->
      let t1',env1 = ocompile env t1 in
      let t2',env2 = ocompile env1 t2 in
      (Otimes (t1',t2'), env2)
  | Kapp("Zs",[t]) ->  
      let t',env = ocompile env  t in
       (Oplus (t',Oz(1)), env)
  | Kapp(("POS"|"NEG"|"ZERO"),_) -> 
      begin try (Oz(recognize_number t),env) 
      with _ -> 
	let v,env' = add_atom t env in Oatom v, env'
      end
  | Kvar s ->
      let v,env' = add_atom t env in Oatom v, env'
  | Kapp("Zopp",[t]) ->
      let t',env1 = ocompile env t in Oinv t', env1
  | _ -> 
      let v,env' = add_atom t env in Oatom(v), env'
  with e when Logic.catchable_exception e ->
    let v,env' = add_atom t env in Oatom(v), env'

(*i  | Kapp("Zs",[t1]) ->
    | Kapp("inject_nat",[t']) -> i*)

let normalize_equation t =
  let t1,trace1 = reduce t in
  let trace2,t2 = condense t1 in
  let trace3,t3 = clear_zero t2 in
  do_list [trace1; do_list trace2; do_list trace3], t3

let destructure_omega gl (trace_norm, system, env) (id,c) = 
  let mk_step t1 t2 f kind coq_t_oper =
       let o1,env1 = ocompile env t1 in
       let o2,env2 = ocompile env1 t2 in
       let t = f o1 o2 in
       let trace, oterm = normalize_equation t in
       let equa = compile id kind oterm in
       let tterm =
	 mkApp (Lazy.force coq_t_oper,
		[| val_of_formula o1; val_of_formula o2 |]) in
       ((id,(trace,tterm)) :: trace_norm), (equa :: system), env2 in

  try match destructurate c with
    | Kapp("eq",[typ;t1;t2]) when destructurate (Tacmach.pf_nf gl typ) = 
	                          Kapp("Z",[]) ->
         mk_step t1 t2 (fun o1 o2 -> Oplus (o1,Oinv o2)) Omega.EQUA coq_t_equal
    | Kapp("Zne",[t1;t2]) ->
        mk_step t1 t2 (fun o1 o2 -> Oplus (o1,Oinv o2)) Omega.DISE coq_t_neq
    | Kapp("Zle",[t1;t2]) ->
        mk_step t1 t2 (fun o1 o2 -> Oplus (o2,Oinv o1)) Omega.INEQ coq_t_leq
    | Kapp("Zlt",[t1;t2]) ->
        mk_step t1 t2 
	  (fun o1 o2 -> Oplus (Oplus(o2,Oz (-1)),Oinv o1)) Omega.INEQ coq_t_lt
    | Kapp("Zge",[t1;t2]) ->
        mk_step t1 t2 (fun o1 o2 -> Oplus (o1,Oinv o2)) Omega.INEQ coq_t_geq
    | Kapp("Zgt",[t1;t2]) ->
        mk_step t1 t2 
	  (fun o1 o2 -> Oplus (Oplus(o1,Oz (-1)),Oinv o2)) Omega.INEQ coq_t_gt
    | _ -> trace_norm, system, env
  with e when Logic.catchable_exception e -> trace_norm, system, env

(* \section{Rejouer l'historique} *)

let replay_history env_hyp =
  let rec loop env_hyp t =
    match t with
      | Omega.CONTRADICTION (e1,e2) :: l -> 
	  let trace = mk_nat (List.length e1.Omega.body) in
	  mkApp (Lazy.force coq_s_contradiction,
		 [| trace ; mk_nat (get_hyp env_hyp e1.Omega.id); 
		    mk_nat (get_hyp env_hyp e2.Omega.id) |])
      | Omega.DIVIDE_AND_APPROX (e1,e2,k,d) :: l ->
	  mkApp (Lazy.force coq_s_div_approx,
		 [| mk_Z k; mk_Z d; val_of e2.Omega.body e2.Omega.constant;
		    mk_nat (List.length e2.Omega.body); 
		    loop env_hyp l; mk_nat (get_hyp env_hyp e1.Omega.id) |])
      | Omega.NOT_EXACT_DIVIDE (e1,k) :: l ->
	  let e2_constant = Omega.floor_div e1.Omega.constant k in
	  let d = e1.Omega.constant - e2_constant * k in
	  let e2_body = Omega.map_eq_linear (fun c -> c / k) e1.Omega.body in
          mkApp (Lazy.force coq_s_not_exact_divide,
		 [|mk_Z k; mk_Z d; val_of e2_body e2_constant; 
		   mk_nat (List.length e2_body); 
		   mk_nat (get_hyp env_hyp e1.Omega.id)|])
      | Omega.EXACT_DIVIDE (e1,k) :: l ->
	  let e2_body =  Omega.map_eq_linear (fun c -> c / k) e1.Omega.body in
	  let e2_constant = Omega.floor_div e1.Omega.constant k in
          mkApp (Lazy.force coq_s_exact_divide,
		 [|mk_Z k; val_of e2_body e2_constant; 
		   mk_nat (List.length e2_body);
		   loop env_hyp l; mk_nat (get_hyp env_hyp e1.Omega.id)|])
      | (Omega.MERGE_EQ(e3,e1,e2)) :: l ->
	  let n1 = get_hyp env_hyp e1.Omega.id and n2 = get_hyp env_hyp e2 in
          mkApp (Lazy.force coq_s_merge_eq,
		 [| mk_nat (List.length e1.Omega.body);
		    mk_nat n1; mk_nat n2;
		    loop (e3:: env_hyp) l |])
      | Omega.SUM(e3,(k1,e1),(k2,e2)) :: l ->
	  let n1 = get_hyp env_hyp e1.Omega.id 
	  and n2 = get_hyp env_hyp e2.Omega.id in
	  let trace = shuffle_path k1 e1.Omega.body k2 e2.Omega.body in
          mkApp (Lazy.force coq_s_sum,
		 [| mk_Z k1; mk_nat n1; mk_Z k2;
		    mk_nat n2; trace; (loop (e3 :: env_hyp) l) |])
      | Omega.CONSTANT_NOT_NUL(e,k) :: l -> 
          mkApp (Lazy.force coq_s_constant_not_nul,
		 [|  mk_nat (get_hyp env_hyp e) |])
      | Omega.CONSTANT_NEG(e,k) :: l ->
          mkApp (Lazy.force coq_s_constant_neg,
		 [|  mk_nat (get_hyp env_hyp e) |])
      | Omega.STATE (new_eq,def,orig,m,sigma) :: l ->
	  let n1 = get_hyp env_hyp orig.Omega.id 
	  and n2 = get_hyp env_hyp def.Omega.id in
	  let v = unintern_id sigma in
	  let o_def = decompile def in
	  let o_orig = decompile orig in
	  let body =
	     Oplus (o_orig,Otimes (Oplus (Oinv v,o_def), Oz m)) in
	  let trace,_ = normalize_equation body in
	  mkApp (Lazy.force coq_s_state,
		 [| mk_Z m; trace; mk_nat n1; mk_nat n2; 
		    loop (new_eq.Omega.id :: env_hyp) l |])
      |	Omega.HYP _ :: l -> loop env_hyp l
      |	Omega.CONSTANT_NUL e :: l ->
	  mkApp (Lazy.force coq_s_constant_nul, 
		 [|  mk_nat (get_hyp env_hyp e) |])
      |	Omega.NEGATE_CONTRADICT(e1,e2,b) :: l ->
	  if b then
	  mkApp (Lazy.force coq_s_negate_contradict, 
		 [|  mk_nat (get_hyp env_hyp e1.Omega.id);
		     mk_nat (get_hyp env_hyp e2.Omega.id) |])
	  else
	    mkApp (Lazy.force coq_s_negate_contradict_inv, 
		   [|  mk_nat (List.length e1.Omega.body);
                       mk_nat (get_hyp env_hyp e1.Omega.id);
                       mk_nat (get_hyp env_hyp e2.Omega.id) |])

      | Omega.SPLIT_INEQ(e,(e1,l1),(e2,l2)) :: l ->
	  let i =  get_hyp env_hyp e.Omega.id in
	  let r1 = loop (e1 :: env_hyp) l1 in
	  let r2 = loop (e2 :: env_hyp) l2 in
	  mkApp (Lazy.force coq_s_split_ineq, 
                  [| mk_nat (List.length e.Omega.body); mk_nat i; r1 ; r2 |])
      |	(Omega.FORGET_C _ | Omega.FORGET _ | Omega.FORGET_I _) :: l ->
	  loop env_hyp l
      | (Omega.WEAKEN  _ ) :: l -> failwith "not_treated"
      |	[] -> failwith "no contradiction"
  in loop env_hyp

let show_goal gl =
  if !debug then Pp.ppnl (Tacmach.pr_gls gl); Tacticals.tclIDTAC gl

(* Cette fonction prépare le rejeu puis l'appelle :
   \begin{itemize}
   \item elle isole les hypothèses utiles et les mets dans 
   le but réifié
   \item elle prépare l'introduction de nouvelles variables pour le test
    de Banerjee (opération STATE) 
   \end{itemize}
*)

let prepare_and_play env tac_hyps trace_solution =   
  let rec loop ((l_tac_norm, l_terms, l_id, l_e) as result) = function
    Omega.HYP e :: l ->
      let id = tag_of_equation e.Omega.id in
      let (tac_norm,term) = 
	try List.assoc id tac_hyps
        with Not_found -> failwith "what eqn" in
      loop (tac_norm :: l_tac_norm,term :: l_terms,
	    Term.mkVar id :: l_id, e.Omega.id :: l_e ) l
  |  Omega.SPLIT_INEQ(e,(e1,l1),(e2,l2)) :: l ->
      loop (loop result l1) l2
  | _ :: l -> loop result l
  | [] -> result in
  let l_tac_norms, l_terms,l_generalized, l_e = 
    loop ([],[],[],[]) trace_solution in

  let rec loop ((env,l_tac_norm, l_terms,l_gener, l_e) as result) = function
    Omega.STATE (new_eq,def,orig,m,sigma) :: l ->
      let o_def = decompile def in
      let coq_def = coq_of_formula env o_def in
      let v,env' = add_atom coq_def env in
      intern_id_force (Oatom v) sigma;
      let term_to_generalize =
	mkApp(Lazy.force coq_refl_equal,[|Lazy.force coq_Z; coq_def|]) in
      let reified_term =
	 mkApp (Lazy.force coq_t_equal,	
		[| val_of_formula o_def; val_of_formula (Oatom v) |]) in
      loop (env', Lazy.force coq_c_nop :: l_tac_norm,
	    reified_term :: l_terms ,term_to_generalize :: l_gener, 
	    def.Omega.id :: l_e)  l
  | Omega.SPLIT_INEQ(e,(e1,l1),(e2,l2)) :: l ->
      loop (loop result l1) l2
  | _ :: l -> loop result l
  | [] -> result in
  let env, l_tac_norms, l_terms,l_generalized, l_e = 
    loop (env, l_tac_norms, l_terms,l_generalized, l_e) trace_solution in

  (* Attention Generalize ajoute les buts dans l'ordre inverse *)
  let l_reified_terms = mk_list (Lazy.force coq_proposition) l_terms in
  let l_reified_tac_norms = mk_list (Lazy.force coq_step) l_tac_norms in
  let env_reified = mk_list (Lazy.force coq_Z) env in
  let reified = 
    mkApp(Lazy.force coq_interp_sequent, [| env_reified; l_reified_terms |]) in
  let reified_trace_solution = replay_history l_e trace_solution in
  if !debug then begin
    Pp.ppnl (Printer.prterm reified);
    Pp.ppnl (Printer.prterm l_reified_tac_norms);
    Pp.ppnl (Printer.prterm reified_trace_solution);
  end;
  Tactics.generalize l_generalized >>
  Tactics.change_in_concl None reified >>
  Tacticals.tclTRY 
    (Tactics.apply (mkApp (Lazy.force coq_normalize_sequent, 
			   [|l_reified_tac_norms |]))) >>
  Tacticals.tclTRY 
    (Tactics.apply (mkApp (Lazy.force coq_execute_sequent, 
			   [|reified_trace_solution |]))) >>
  Tactics.normalise_in_concl >> Auto.auto 5 []
  
let coq_omega gl =
  clear_tags (); clear_intern ();
  let tactic_hyps, system, env = 
    List.fold_left (destructure_omega gl) ([],[],[])
      (Tacmach.pf_hyps_types gl) in
  if !debug then begin Omega.display_system system;  print_newline () end;
  begin try
    let trace = Omega.simplify_strong system in 
    if !debug then Omega.display_action trace;
    prepare_and_play env tactic_hyps trace gl
  with Omega.NO_CONTRADICTION -> Util.error "Omega can't solve this system"
  end

(*
let refl_omega = Tacmach.hide_atomic_tactic "StepOmega" coq_omega 
*)

(* \section{Encapsulation ROMEGA} *)

(* Toute cette partie est héritée de [OMEGA]. Seule modification : l'appel
   à [coq_omega] qui correspond à la version réflexive. Il suffirait de 
   paramétrer le code par cette tactique.

   \paragraph{Note :} cette partie aussi devrait être réfléchie.  *)

open Reduction
open Proof_type
open Ast
open Names
open Term
open Environ
open Sign
open Inductive
open Tacticals
open Tacmach
open Tactics
open Tacticals
open Clenv
open Logic
open Omega

let nat_inject gl = Coq_omega.nat_inject gl
let elim_id id gl = simplest_elim (pf_global gl id) gl
let resolve_id id gl = apply (pf_global gl id) gl
let generalize_tac = Coq_omega.generalize_tac
let coq_imp_simp = Coq_omega.coq_imp_simp
let decidability = Coq_omega.decidability
let coq_not_or = Coq_omega.coq_not_or
let coq_not_and = Coq_omega.coq_not_and
let coq_not_imp = Coq_omega.coq_not_imp
let coq_not_not = Coq_omega.coq_not_not
let coq_not_Zle = Coq_omega.coq_not_Zle
let coq_not_Zge = Coq_omega.coq_not_Zge
let coq_not_Zlt = Coq_omega.coq_not_Zlt
let coq_not_Zgt = Coq_omega.coq_not_Zgt
let coq_not_le = Coq_omega.coq_not_le
let coq_not_ge = Coq_omega.coq_not_ge
let coq_not_lt = Coq_omega.coq_not_lt
let coq_not_gt = Coq_omega.coq_not_gt
let coq_not_eq = Coq_omega.coq_not_eq
let coq_not_Zeq = Coq_omega.coq_not_Zeq
let coq_neq = Coq_omega.coq_neq
let coq_Zne = Coq_omega.coq_Zne
let coq_dec_not_not = Coq_omega.coq_dec_not_not
let old_style_flag = Coq_omega.old_style_flag
let unfold = Coq_omega.unfold
let sp_not = Coq_omega.sp_not
let all_time = Coq_omega.all_time
let mkNewMeta = Coq_omega.mkNewMeta
	  
let destructure_hyps gl =
  let rec loop evbd = function
    | [] -> (tclTHEN nat_inject coq_omega)
    | (i,body,t)::lit ->
	begin try match destructurate t with
          | Kapp(("Zle"|"Zge"|"Zgt"|"Zlt"|"Zne"),[t1;t2]) -> loop evbd lit
          | Kapp("or",[t1;t2]) ->
              (tclTHENS
                (tclTHENSEQ [elim_id i; clear [i]; intros_using [i]])
		[ loop evbd ((i,None,t1)::lit); 
                  loop evbd ((i,None,t2)::lit) ])
          | Kapp("and",[t1;t2]) ->
              let i1 = id_of_string (string_of_id i ^ "_left") in
              let i2 = id_of_string (string_of_id i ^ "_right") in
              (tclTHENSEQ
		 [elim_id i;
                  clear [i];
		  intros_using [i1;i2];
		  loop (i1::i2::evbd) ((i1,None,t1)::(i2,None,t2)::lit)])
          | Kimp(t1,t2) ->
              if isprop (pf_type_of gl t1) & closed0 t2 then begin
		(tclTHENSEQ
                  [generalize_tac [mkApp (Lazy.force coq_imp_simp,
                                          [| t1; t2; 
					     decidability gl t1;
					     mkVar i|])]; 
		   clear [i];
		   intros_using [i]; 
		   loop evbd ((i,None,mk_or (mk_not t1) t2)::lit)])
              end else loop evbd lit
          | Kapp("not",[t]) -> 
              begin match destructurate t with 
		  Kapp("or",[t1;t2]) -> 
                    (tclTHENSEQ
		      [generalize_tac [mkApp (Lazy.force coq_not_or,
                                              [| t1; t2; mkVar i |])];
		       clear [i]; 
		       intros_using [i]; 
                       loop evbd 
                         ((i,None,mk_and (mk_not t1) (mk_not t2)):: lit)])
		| Kapp("and",[t1;t2]) -> 
                    (tclTHENSEQ
		      [generalize_tac
				[mkApp (Lazy.force coq_not_and, [| t1; t2;
					   decidability gl t1;mkVar i|])];
		       clear [i];
		       intros_using [i];
                       loop evbd ((i,None,mk_or (mk_not t1) (mk_not t2))::lit)])
		| Kimp(t1,t2) ->
                    (tclTHENSEQ
		      [generalize_tac 
				[mkApp (Lazy.force coq_not_imp, [| t1; t2; 
					   decidability gl t1;mkVar i |])];
		       clear [i];
		       intros_using [i];
                       loop evbd ((i,None,mk_and t1 (mk_not t2)) :: lit)])
		| Kapp("not",[t]) ->
                    (tclTHENSEQ
                      [generalize_tac
				[mkApp (Lazy.force coq_not_not, [| t;
					    decidability gl t; mkVar i |])];
		       clear [i]; 
		       intros_using [i];
                       loop evbd ((i,None,t)::lit)])
		| Kapp("Zle", [t1;t2]) ->
                    (tclTHENSEQ
		      [generalize_tac [mkApp (Lazy.force coq_not_Zle,
					      [| t1;t2;mkVar i|])];
		       clear [i];
		       intros_using [i];
		       loop evbd lit])
		| Kapp("Zge", [t1;t2]) ->
                    (tclTHENSEQ
		      [generalize_tac [mkApp (Lazy.force coq_not_Zge,
					      [| t1;t2;mkVar i|])];
		       clear [i];
		       intros_using [i];
		       loop evbd lit])
		| Kapp("Zlt", [t1;t2]) ->
                    (tclTHENSEQ
		      [generalize_tac [mkApp (Lazy.force coq_not_Zlt,
					      [| t1;t2;mkVar i|])];
		       clear [i];
		       intros_using [i];
		       loop evbd lit])
		| Kapp("Zgt", [t1;t2]) ->
                    (tclTHENSEQ
		      [generalize_tac [mkApp (Lazy.force coq_not_Zgt,
					      [| t1;t2;mkVar i|])];
		       clear [i];
		       intros_using [i];
		       loop evbd lit])
		| Kapp("le", [t1;t2]) ->
                    (tclTHENSEQ
		      [generalize_tac [mkApp (Lazy.force coq_not_le,
					      [| t1;t2;mkVar i|])];
		       clear [i];
		       intros_using [i];
		       loop evbd lit])
		| Kapp("ge", [t1;t2]) ->
                    (tclTHENSEQ
		      [generalize_tac [mkApp (Lazy.force coq_not_ge,
					      [| t1;t2;mkVar i|])];
		       clear [i];
		       intros_using [i];
		       loop evbd lit])
		| Kapp("lt", [t1;t2]) ->
                    (tclTHENSEQ
		      [generalize_tac [mkApp (Lazy.force coq_not_lt,
					      [| t1;t2;mkVar i|])];
		       clear [i];
		       intros_using [i];
		       loop evbd lit])
		| Kapp("gt", [t1;t2]) ->
                    (tclTHENSEQ
		      [generalize_tac [mkApp (Lazy.force coq_not_gt,
					      [| t1;t2;mkVar i|])];
		       clear [i];
		       intros_using [i];
		       loop evbd lit])
		| Kapp("eq",[typ;t1;t2]) ->
                    if !old_style_flag then begin 
		      match destructurate (pf_nf gl typ) with
			| Kapp("nat",_) -> 
                            (tclTHENSEQ
			      [simplest_elim 
				(applist 
				  (Lazy.force coq_not_eq,[t1;t2;mkVar i]));
			        clear [i];
			        intros_using [i];
			        loop evbd lit])
			| Kapp("Z",_) ->
                            (tclTHENSEQ
			      [simplest_elim 
				(applist 
				  (Lazy.force coq_not_Zeq,[t1;t2;mkVar i]));
			       clear [i];
			       intros_using [i];
			       loop evbd lit])
			| _ -> loop evbd lit
                    end else begin 
		      match destructurate (pf_nf gl typ) with
			| Kapp("nat",_) -> 
                            (tclTHEN 
			       (convert_hyp_no_check
                                  (i,body,
				  (mkApp (Lazy.force coq_neq, [| t1;t2|]))))
			       (loop evbd lit))
			| Kapp("Z",_) ->
                            (tclTHEN 
			       (convert_hyp_no_check
                                  (i,body,
				  (mkApp (Lazy.force coq_Zne, [| t1;t2|]))))
			       (loop evbd lit))
			| _ -> loop evbd lit
                    end
		| _ -> loop evbd lit
              end 
          | _ -> loop evbd lit 
	with e when catchable_exception e -> loop evbd lit
	end 
  in
  loop (pf_ids_of_hyps gl) (pf_hyps gl) gl

let omega_solver gl =
  Library.check_required_library ["Coq";"romega";"ROmega"];
  let concl = pf_concl gl in
  let rec loop t =
    match destructurate t with
      | Kapp("not",[t1;t2]) -> 
          (tclTHENSEQ [unfold sp_not; intro; destructure_hyps])
      | Kimp(a,b) -> (tclTHEN intro (loop b))
      | Kapp("False",[]) -> destructure_hyps
      | _ ->
          (tclTHENSEQ
	    [Tactics.refine 
	      (mkApp (Lazy.force coq_dec_not_not,
                      [| t; decidability gl t; mkNewMeta () |]));
	     intro;
	     destructure_hyps])
  in
  (loop concl) gl

(*
let omega = hide_atomic_tactic "ReflOmega" omega_solver
*)

