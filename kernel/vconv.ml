open Util
open Names
open Term
open Environ
open Conv_oracle
open Reduction
open Closure
open Vm
open Csymtable
open Univ

let val_of_constr env c =
  val_of_constr (pre_env env) c

(* Test la structure des piles *)

let compare_zipper z1 z2 =
  match z1, z2 with
  | Zapp args1, Zapp args2 -> Int.equal (nargs args1) (nargs args2)
  | Zfix(f1,args1), Zfix(f2,args2) ->  Int.equal (nargs args1) (nargs args2)
  | Zswitch _, Zswitch _ -> true
  | _ , _ -> false

let rec compare_stack stk1 stk2 =
  match stk1, stk2 with
  | [], [] -> true
  | z1::stk1, z2::stk2 ->
      if compare_zipper z1 z2 then compare_stack stk1 stk2
      else false
  | _, _ -> false

(* Conversion *)
let conv_vect fconv vect1 vect2 cu =
  let n = Array.length vect1 in
  if Int.equal n (Array.length vect2) then
    let rcu = ref cu in
    for i = 0 to n - 1 do
      rcu := fconv vect1.(i) vect2.(i) !rcu
    done;
    !rcu
  else raise NotConvertible

let infos = ref (create_clos_infos betaiotazeta Environ.empty_env)

let eq_table_key = Names.eq_table_key eq_constant

let rec conv_val env pb k v1 v2 cu =
  if v1 == v2 then cu
  else conv_whd env pb k (whd_val v1) (whd_val v2) cu

and conv_whd env pb k whd1 whd2 cu =
  match whd1, whd2 with
  | Vsort s1, Vsort s2 -> check_sort_cmp_universes env pb s1 s2 cu; cu
  | Vprod p1, Vprod p2 ->
      let cu = conv_val env CONV k (dom p1) (dom p2) cu in
      conv_fun env pb k (codom p1) (codom p2) cu
  | Vfun f1, Vfun f2 -> conv_fun env CONV k f1 f2 cu
  | Vfix (f1,None), Vfix (f2,None) -> conv_fix env k f1 f2 cu
  | Vfix (f1,Some args1), Vfix(f2,Some args2) ->
      if nargs args1 <> nargs args2 then raise NotConvertible
      else conv_arguments env k args1 args2 (conv_fix env k f1 f2 cu)
  | Vcofix (cf1,_,None), Vcofix (cf2,_,None) -> conv_cofix env k cf1 cf2 cu
  | Vcofix (cf1,_,Some args1), Vcofix (cf2,_,Some args2) ->
      if nargs args1 <> nargs args2 then raise NotConvertible
      else conv_arguments env k args1 args2 (conv_cofix env k cf1 cf2 cu)
  | Vconstr_const i1, Vconstr_const i2 ->
      if Int.equal i1 i2 then cu else raise NotConvertible
  | Vconstr_block b1, Vconstr_block b2 ->
      let sz = bsize b1 in
      if Int.equal (btag b1) (btag b2) && Int.equal sz (bsize b2) then
	let rcu = ref cu in
	for i = 0 to sz - 1 do
	  rcu := conv_val env CONV k (bfield b1 i) (bfield b2 i) !rcu
	done;
	!rcu
      else raise NotConvertible
  | Vatom_stk(a1,stk1), Vatom_stk(a2,stk2) ->
      conv_atom env pb k a1 stk1 a2 stk2 cu
  | Vfun _, _ | _, Vfun _ ->
      conv_val env CONV (k+1) (eta_whd k whd1) (eta_whd k whd2) cu
  | _, Vatom_stk(Aiddef(_,v),stk) ->
      conv_whd env pb k whd1 (force_whd v stk) cu
  | Vatom_stk(Aiddef(_,v),stk), _ ->
      conv_whd env pb k (force_whd v stk) whd2 cu
  | _, _ -> raise NotConvertible

and conv_atom env pb k a1 stk1 a2 stk2 cu =
  match a1, a2 with
  | Aind ind1, Aind ind2 ->
      if eq_puniverses eq_ind ind1 ind2 && compare_stack stk1 stk2
      then
	conv_stack env k stk1 stk2 cu
      else raise NotConvertible
  | Aid ik1, Aid ik2 ->
      if Vars.eq_id_key ik1 ik2 && compare_stack stk1 stk2 then
	conv_stack env k stk1 stk2 cu
      else raise NotConvertible
  | Aiddef(ik1,v1), Aiddef(ik2,v2) ->
      begin
	try
	  if Vars.eq_id_key ik1 ik2 && compare_stack stk1 stk2 then
	    conv_stack env k stk1 stk2 cu
	  else raise NotConvertible
	with NotConvertible ->
	  if oracle_order Univ.out_punivs (oracle_of_infos !infos) 
	    false ik1 ik2 then
            conv_whd env pb k (whd_stack v1 stk1) (Vatom_stk(a2,stk2)) cu
          else conv_whd env pb k (Vatom_stk(a1,stk1)) (whd_stack v2 stk2) cu
      end
  | Aiddef(ik1,v1), _ ->
      conv_whd env pb k (force_whd v1 stk1) (Vatom_stk(a2,stk2)) cu
  | _, Aiddef(ik2,v2) ->
      conv_whd env pb k (Vatom_stk(a1,stk1)) (force_whd v2 stk2) cu
  | _, _ -> raise NotConvertible

and conv_stack env k stk1 stk2 cu =
  match stk1, stk2 with
  | [], [] -> cu
  | Zapp args1 :: stk1, Zapp args2 :: stk2 ->
      conv_stack env k stk1 stk2 (conv_arguments env k args1 args2 cu)
  | Zfix(f1,args1) :: stk1, Zfix(f2,args2) :: stk2 ->
      conv_stack env k stk1 stk2
	(conv_arguments env k args1 args2 (conv_fix env k f1 f2 cu))
  | Zswitch sw1 :: stk1, Zswitch sw2 :: stk2 ->
      if check_switch sw1 sw2 then
	let vt1,vt2 = type_of_switch sw1, type_of_switch sw2 in
	let rcu = ref (conv_val env CONV k vt1 vt2 cu) in
	let b1, b2 = branch_of_switch k sw1, branch_of_switch k sw2 in
	for i = 0 to Array.length b1 - 1 do
	  rcu :=
	    conv_val env CONV (k + fst b1.(i)) (snd b1.(i)) (snd b2.(i)) !rcu
	done;
	conv_stack env k stk1 stk2 !rcu
      else raise NotConvertible
  | _, _ -> raise NotConvertible

and conv_fun env pb k f1 f2 cu =
  if f1 == f2 then cu
  else
    let arity,b1,b2 = decompose_vfun2 k f1 f2 in
    conv_val env pb (k+arity) b1 b2 cu

and conv_fix env k f1 f2 cu =
  if f1 == f2 then cu
  else
    if check_fix f1 f2 then
      let bf1, tf1 = reduce_fix k f1 in
      let bf2, tf2 = reduce_fix k f2 in
      let cu = conv_vect (conv_val env CONV k) tf1 tf2 cu in
      conv_vect (conv_fun env CONV (k + Array.length tf1)) bf1 bf2 cu
    else raise NotConvertible

and conv_cofix env k cf1 cf2 cu =
  if cf1 == cf2 then cu
  else
    if check_cofix cf1 cf2 then
      let bcf1, tcf1 = reduce_cofix k cf1 in
      let bcf2, tcf2 = reduce_cofix k cf2 in
      let cu = conv_vect (conv_val env CONV k) tcf1 tcf2 cu in
      conv_vect (conv_val env CONV (k + Array.length tcf1)) bcf1 bcf2 cu
    else raise NotConvertible

and conv_arguments env k args1 args2 cu =
  if args1 == args2 then cu
  else
    let n = nargs args1 in
    if Int.equal n (nargs args2) then
      let rcu = ref cu in
      for i = 0 to n - 1 do
	rcu := conv_val env CONV k (arg args1 i) (arg args2 i) !rcu
      done;
      !rcu
    else raise NotConvertible

let rec eq_puniverses f (x,l1) (y,l2) cu =
  if f x y then conv_universes l1 l2 cu
  else raise NotConvertible

and conv_universes l1 l2 cu =
  if Univ.Instance.equal l1 l2 then cu else raise NotConvertible

let rec conv_eq env pb t1 t2 cu =
  if t1 == t2 then cu
  else
    match kind_of_term t1, kind_of_term t2 with
    | Rel n1, Rel n2 ->
	if Int.equal n1 n2 then cu else raise NotConvertible
    | Meta m1, Meta m2 ->
	if Int.equal m1 m2 then cu else raise NotConvertible
    | Var id1, Var id2 ->
	if Id.equal id1 id2 then cu else raise NotConvertible
    | Sort s1, Sort s2 -> check_sort_cmp_universes env pb s1 s2 cu; cu
    | Cast (c1,_,_), _ -> conv_eq env pb c1 t2 cu
    | _, Cast (c2,_,_) -> conv_eq env pb t1 c2 cu
    | Prod (_,t1,c1), Prod (_,t2,c2) ->
	conv_eq env pb c1 c2 (conv_eq env CONV t1 t2 cu)
    | Lambda (_,t1,c1), Lambda (_,t2,c2) -> conv_eq env CONV c1 c2 cu
    | LetIn (_,b1,t1,c1), LetIn (_,b2,t2,c2) ->
	conv_eq env pb c1 c2 (conv_eq env CONV b1 b2 cu)
    | App (c1,l1), App (c2,l2) ->
	conv_eq_vect env l1 l2 (conv_eq env CONV c1 c2 cu)
    | Evar (e1,l1), Evar (e2,l2) ->
	if Evar.equal e1 e2 then conv_eq_vect env l1 l2 cu
	else raise NotConvertible
    | Const c1, Const c2 -> eq_puniverses eq_constant c1 c2 cu
    | Proj (p1,c1), Proj (p2,c2) ->
	if eq_constant (Projection.constant p1) (Projection.constant p2) then
	  conv_eq env pb c1 c2 cu 
	else raise NotConvertible
    | Ind c1, Ind c2 ->
       eq_puniverses eq_ind c1 c2 cu
    | Construct c1, Construct c2 ->
       eq_puniverses eq_constructor c1 c2 cu
    | Case (_,p1,c1,bl1), Case (_,p2,c2,bl2) ->
	let pcu = conv_eq env CONV p1 p2 cu in
	let ccu = conv_eq env CONV c1 c2 pcu in
	conv_eq_vect env bl1 bl2 ccu
    | Fix ((ln1, i1),(_,tl1,bl1)), Fix ((ln2, i2),(_,tl2,bl2)) ->
	if Int.equal i1 i2 && Array.equal Int.equal ln1 ln2 then conv_eq_vect env tl1 tl2 (conv_eq_vect env bl1 bl2 cu)
	else raise NotConvertible
    | CoFix(ln1,(_,tl1,bl1)), CoFix(ln2,(_,tl2,bl2)) ->
	if Int.equal ln1 ln2 then conv_eq_vect env tl1 tl2 (conv_eq_vect env bl1 bl2 cu)
	else raise NotConvertible
    | _ -> raise NotConvertible

and conv_eq_vect env vt1 vt2 cu =
  let len = Array.length vt1 in
  if Int.equal len (Array.length vt2) then
    let rcu = ref cu in
    for i = 0 to len-1 do
      rcu := conv_eq env CONV vt1.(i) vt2.(i) !rcu
    done; !rcu
  else raise NotConvertible

let vconv pb env t1 t2 =
  infos := create_clos_infos betaiotazeta env;
  let _cu =
    try conv_eq env pb t1 t2 (universes env)
    with NotConvertible ->
      let v1 = val_of_constr env t1 in
      let v2 = val_of_constr env t2 in
      let cu = conv_val env pb (nb_rel env) v1 v2 (universes env) in
      cu
  in ()

let _ = Reduction.set_vm_conv vconv

let use_vm = ref false

let set_use_vm b =
  use_vm := b;
  if b then Reduction.set_default_conv (fun cv_pb ?(l2r=false) -> vconv cv_pb)
  else Reduction.set_default_conv (fun cv_pb ?(l2r=false) -> Reduction.conv_cmp cv_pb)

let use_vm _ = !use_vm


