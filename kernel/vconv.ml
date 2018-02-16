open Util
open Names
open Environ
open Reduction
open Vm
open Vmvalues
open Csymtable

(* Test la structure des piles *)

let compare_zipper z1 z2 =
  match z1, z2 with
  | Zapp args1, Zapp args2 -> Int.equal (nargs args1) (nargs args2)
  | Zfix(_f1,args1), Zfix(_f2,args2) ->  Int.equal (nargs args1) (nargs args2)
  | Zswitch _, Zswitch _ | Zproj _, Zproj _ -> true
  | Zapp _ , _ | Zfix _, _ | Zswitch _, _ | Zproj _, _ -> false

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

let rec conv_val env pb k v1 v2 cu =
  if v1 == v2 then cu
  else conv_whd env pb k (whd_val v1) (whd_val v2) cu

and conv_whd env pb k whd1 whd2 cu =
(*  Pp.(msg_debug (str "conv_whd(" ++ pr_whd whd1 ++ str ", " ++ pr_whd whd2 ++ str ")")) ; *)
  match whd1, whd2 with
  | Vuniv_level _ , _
  | _ , Vuniv_level _ ->
    (** Both of these are invalid since universes are handled via
     ** special cases in the code.
     **)
    assert false
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
      let tag1 = btag b1 and tag2 = btag b2 in
      let sz = bsize b1 in
      if Int.equal tag1 tag2 && Int.equal sz (bsize b2) then
	let rcu = ref cu in
	for i = 0 to sz - 1 do
	  rcu := conv_val env CONV k (bfield b1 i) (bfield b2 i) !rcu
	done;
	!rcu
      else raise NotConvertible
  | Vint64 i1, Vint64 i2 ->
    if Int64.equal i1 i2 then cu else raise NotConvertible
  | Vatom_stk(a1,stk1), Vatom_stk(a2,stk2) ->
      conv_atom env pb k a1 stk1 a2 stk2 cu
  | Vfun _, _ | _, Vfun _ ->
     (* on the fly eta expansion *)
      conv_val env CONV (k+1) (apply_whd k whd1) (apply_whd k whd2) cu

  | Vprod _, _ | Vfix _, _ | Vcofix _, _  | Vconstr_const _, _ | Vint64 _, _
  | Vconstr_block _, _ | Vatom_stk _, _ -> raise NotConvertible


and conv_atom env pb k a1 stk1 a2 stk2 cu =
(*  Pp.(msg_debug (str "conv_atom(" ++ pr_atom a1 ++ str ", " ++ pr_atom a2 ++ str ")")) ; *)
  match a1, a2 with
  | Aind ((mi,_i) as ind1) , Aind ind2 ->
    if eq_ind ind1 ind2 && compare_stack stk1 stk2 then
      if Environ.polymorphic_ind ind1 env then
        let mib = Environ.lookup_mind mi env in
	let ulen = 
          match mib.Declarations.mind_universes with
          | Declarations.Monomorphic_ind ctx -> Univ.ContextSet.size ctx
          | Declarations.Polymorphic_ind auctx -> Univ.AUContext.size auctx
          | Declarations.Cumulative_ind cumi -> 
            Univ.AUContext.size (Univ.ACumulativityInfo.univ_context cumi)
        in
        match stk1 , stk2 with
	| [], [] -> assert (Int.equal ulen 0); cu
        | Zapp args1 :: stk1' , Zapp args2 :: stk2' ->
          assert (ulen <= nargs args1);
          assert (ulen <= nargs args2);
          let u1 = Array.init ulen (fun i -> uni_lvl_val (arg args1 i)) in
          let u2 = Array.init ulen (fun i -> uni_lvl_val (arg args2 i)) in
          let u1 = Univ.Instance.of_array u1 in
          let u2 = Univ.Instance.of_array u2 in
          let cu = convert_instances ~flex:false u1 u2 cu in
          conv_arguments env ~from:ulen k args1 args2
	    (conv_stack env k stk1' stk2' cu)
        | _, _ -> assert false (* Should not happen if problem is well typed *)
      else
	conv_stack env k stk1 stk2 cu
    else raise NotConvertible
  | Aid ik1, Aid ik2 ->
    if Vmvalues.eq_id_key ik1 ik2 && compare_stack stk1 stk2 then
	conv_stack env k stk1 stk2 cu
      else raise NotConvertible
  | Asort s1, Asort s2 ->
    sort_cmp_universes env pb s1 s2 cu
  | Asort _ , _ | Aind _, _ | Aid _, _ -> raise NotConvertible

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
  | Zproj p1 :: stk1, Zproj p2 :: stk2 ->
    if Projection.Repr.equal p1 p2 then conv_stack env k stk1 stk2 cu
    else raise NotConvertible
  | [], _ | Zapp _ :: _, _ | Zfix _ :: _, _ | Zswitch _ :: _, _
  | Zproj _ :: _, _ -> raise NotConvertible

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

and conv_arguments env ?from:(from=0) k args1 args2 cu =
  if args1 == args2 then cu
  else
    let n = nargs args1 in
    if Int.equal n (nargs args2) then
      let rcu = ref cu in
      for i = from to n - 1 do
	rcu := conv_val env CONV k (arg args1 i) (arg args2 i) !rcu
      done;
      !rcu
    else raise NotConvertible

let warn_bytecode_compiler_failed =
  let open Pp in
  CWarnings.create ~name:"bytecode-compiler-failed" ~category:"bytecode-compiler"
         (fun () -> strbrk "Bytecode compiler failed, " ++
                      strbrk "falling back to standard conversion")

let vm_conv_gen cv_pb env univs t1 t2 =
  if not (typing_flags env).Declarations.enable_VM then
    Reduction.generic_conv cv_pb ~l2r:false (fun _ -> None)
      TransparentState.full env univs t1 t2
  else
  try
    let v1 = val_of_constr env t1 in
    let v2 = val_of_constr env t2 in
    fst (conv_val env cv_pb (nb_rel env) v1 v2 univs)
  with Not_found | Invalid_argument _ ->
    warn_bytecode_compiler_failed ();
    Reduction.generic_conv cv_pb ~l2r:false (fun _ -> None)
      TransparentState.full env univs t1 t2

let vm_conv cv_pb env t1 t2 =
  let univs = Environ.universes env in
  let b =
    if cv_pb = CUMUL then Constr.leq_constr_univs univs t1 t2
    else Constr.eq_constr_univs univs t1 t2
  in
  if not b then
    let univs = (univs, checked_universes) in
    let _ = vm_conv_gen cv_pb env univs t1 t2 in ()
