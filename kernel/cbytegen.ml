open Util
open Names
open Cbytecodes
open Cemitcodes
open Term
open Declarations
open Environ

(*i Compilation des variables + calcul des variables libres *)

(* Representation des environnements machines :                       *)
(*[t0|C0| ... |tc|Cc| ... |t(nbr-1)|C(nbr-1)| fv1 | fv1 | .... | fvn] *)
(*               ^<----------offset--------->                         *)


type fv = fv_elem list

type vm_env = {size : int; fv_rev : fv}
    (* size = n;   fv_rev = [fvn; ... ;fv1] *)
         
type t = {
    nb_stack : int;        (* nbre de variables sur la pile *)
    in_stack : int list;   (* position dans la pile *)
    nb_rec : int;          (* nbre de fonctions mutuellement recursives = 
			                                              nbr *)
    pos_rec : int;         (* position de la fonction courante = c *)
    offset : int;          
    in_env : vm_env ref
  }	

let empty_fv = {size= 0; fv_rev = []}

let fv r = !(r.in_env)

(* [add_param n] rend la liste [sz+1;sz+2;...;sz+n] *)
let rec add_param n sz l =
  if n = 0 then l else add_param (n - 1) sz (n+sz::l) 

(* [push_param ] ajoute les parametres de fonction dans la pile *)
let push_param n sz r =
  { r with
    nb_stack = r.nb_stack + n;
    in_stack = add_param n sz r.in_stack }

(* [push_local e sz] ajoute une nouvelle variable dans la pile a la position *)
let push_local sz r = 
  { r with 
    nb_stack = r.nb_stack + 1;
    in_stack = (sz + 1) :: r.in_stack }

(* Table de relocation initiale *)
let empty () = 
  { nb_stack = 0; in_stack = [];
    nb_rec = 0;pos_rec = 0;
    offset = 0; in_env = ref empty_fv }

let init_fun arity = 
  { nb_stack = arity; in_stack = add_param arity 0 [];
    nb_rec = 0; pos_rec = 0;
    offset = 1; in_env = ref empty_fv } 

let init_type ndef rfv =
  { nb_stack = 0; in_stack = [];
    nb_rec = 0; pos_rec = 0;
    offset = 2*(ndef-1)+1; in_env = rfv }

let init_fix ndef pos_rec arity rfv =
  { nb_stack = arity; in_stack = add_param arity 0 [];
    nb_rec = ndef; pos_rec = pos_rec;
    offset = 2 * (ndef - pos_rec - 1)+1; in_env = rfv} 

let find_at el l = 
  let rec aux n = function
    | [] -> raise Not_found
    | hd :: tl -> if hd = el then n else aux (n+1) tl
  in aux 1 l

let pos_named id r =
  let env = !(r.in_env) in
  let cid = FVnamed id in
  try Kenvacc(r.offset + env.size - (find_at cid env.fv_rev))
  with Not_found ->
    let pos = env.size in
    r.in_env := { size = pos+1; fv_rev =  cid:: env.fv_rev};
    Kenvacc (r.offset + pos)

let pos_rel i r sz = 
  if i <= r.nb_stack then
    Kacc(sz - (List.nth r.in_stack (i-1)))
  else if i <= r.nb_stack + r.nb_rec 
  then Koffsetclosure (2 * (r.nb_rec + r.nb_stack - r.pos_rec - i))
  else 
    let db = FVrel(i - r.nb_stack - r.nb_rec) in
    let env = !(r.in_env) in
    try Kenvacc(r.offset + env.size - (find_at db env.fv_rev))
    with Not_found ->
      let pos = env.size in
      r.in_env := { size = pos+1; fv_rev =  db:: env.fv_rev};
      Kenvacc(r.offset + pos)


(*i  Examination of the continuation *)

(* Discard all instructions up to the next label.
   This function is to be applied to the continuation before adding a
   non-terminating instruction (branch, raise, return, appterm)
   in front of it. *)

let rec discard_dead_code cont = cont
(*function
    [] -> []
  | (Klabel _ | Krestart ) :: _ as cont -> cont
  | _ :: cont -> discard_dead_code cont
*)

(* Return a label to the beginning of the given continuation.
   If the sequence starts with a branch, use the target of that branch
   as the label, thus avoiding a jump to a jump. *)

let label_code = function
  | Klabel lbl :: _ as cont -> (lbl, cont)
  | cont -> let lbl = Label.create() in (lbl, Klabel lbl :: cont)

(* Return a branch to the continuation. That is, an instruction that,
   when executed, branches to the continuation or performs what the
   continuation performs. We avoid generating branches to returns. *)

let make_branch cont =
  match cont with
  | (Kreturn _ as return) :: cont' -> return, cont'
  | Klabel lbl as b :: _ -> b, cont
  | _ -> let b = Klabel(Label.create()) in b,b::cont

(* Check if we're in tailcall position *)

let rec is_tailcall = function
  | Kreturn k :: _ -> Some k
  | Klabel _ :: c -> is_tailcall c
  | _ -> None

(* Extention of the continuation ****)
	
(* Add a Kpop n instruction in front of a continuation *)
let rec add_pop n = function
  | Kpop m :: cont -> add_pop (n+m) cont
  | Kreturn m:: cont -> Kreturn (n+m) ::cont
  | cont -> if n = 0 then cont else Kpop n :: cont

let add_grab arity lbl cont =
  if arity = 1 then Klabel lbl :: cont
  else Krestart :: Klabel lbl :: Kgrab (arity - 1) :: cont
 

(* Environnement global *****)

let global_env = ref empty_env

let set_global_env env = global_env := env


(* Code des fermetures ****)
let fun_code = ref []

let init_fun_code () = fun_code := []

(* Compilation des constructeurs et des inductifs *)

(* Inv : nparam + arity > 0 *)
let code_construct tag nparams arity cont =
  let f_cont =
      add_pop nparams
      (if arity = 0 then 
	[Kconst (Const_b0 tag); Kreturn 0]
       else [Kacc 0; Kpop 1; Kmakeblock(arity, tag); Kreturn 0])
    in 
    let lbl = Label.create() in
    fun_code := [Ksequence (add_grab (nparams+arity) lbl f_cont,!fun_code)];
    Kclosure(lbl,0) :: cont

type block = 
  | Bconstr of constr
  | Bstrconst of structured_constant
  | Bmakeblock of int * block array
  | Bconstruct_app of int * int * int * block array
                  (* tag , nparams, arity *)

let get_strcst = function
  | Bstrconst sc -> sc
  | _ -> raise Not_found 

let rec str_const c =
  match kind_of_term c with
  | Sort s -> Bstrconst (Const_sorts s)
  | Cast(c,_) -> str_const c 
  | App(f,args) -> 
      begin
	match kind_of_term f with
	| Construct((kn,j),i) -> 
	    let oib = (lookup_mind kn !global_env).mind_packets.(j) in
	    let num,arity = oib.mind_reloc_tbl.(i-1) in
	    let nparams = oib.mind_nparams in
	    if nparams + arity = Array.length args then
	    if arity = 0 then Bstrconst(Const_b0 num)
	    else
	      let rargs = Array.sub args nparams arity in
	      let b_args = Array.map str_const rargs in
	      try 
		let sc_args = Array.map get_strcst b_args in
		Bstrconst(Const_bn(num, sc_args))
	      with Not_found ->
		Bmakeblock(num,b_args)
	    else  
	    let b_args = Array.map str_const args in
	    Bconstruct_app(num, nparams, arity, b_args)
	| _ -> Bconstr c
      end
  | Ind ind -> Bstrconst (Const_ind ind)
  | Construct ((kn,j),i) ->  
      let oib = (lookup_mind kn !global_env).mind_packets.(j) in
      let num,arity = oib.mind_reloc_tbl.(i-1) in
      let nparams = oib.mind_nparams in
      if nparams + arity = 0 then Bstrconst(Const_b0 num)
      else Bconstruct_app(num,nparams,arity,[||])
  | _ -> Bconstr c

(* compilation des applications *)
let comp_args comp_expr reloc args sz cont =
  let nargs_m_1 = Array.length args - 1 in  
  let c = ref (comp_expr reloc args.(0) (sz + nargs_m_1) cont) in
  for i = 1 to nargs_m_1 do
    c := comp_expr reloc args.(i) (sz + nargs_m_1 - i) (Kpush :: !c)
  done; 
  !c
  
let comp_app comp_fun comp_arg reloc f args sz cont =
  let nargs = Array.length args in
  match is_tailcall cont with
  | Some k -> 
      comp_args comp_arg reloc args sz
	(Kpush ::
	 comp_fun reloc f (sz + nargs)
	   (Kappterm(nargs, k + nargs) :: (discard_dead_code cont)))
  | None ->
      if nargs < 4 then
	comp_args comp_arg reloc args sz
	  (Kpush :: (comp_fun reloc f (sz+nargs) (Kapply nargs :: cont)))
      else 
	let lbl,cont1 = label_code cont in
	Kpush_retaddr lbl ::
	(comp_args comp_arg reloc args (sz + 3)
	   (Kpush :: (comp_fun reloc f (sz+3+nargs) (Kapply nargs :: cont1))))

(* Compilation des variables libres *)
  
let compile_fv_elem reloc fv sz cont =
  match fv with
  | FVrel i -> pos_rel i reloc sz :: cont
  | FVnamed id -> pos_named id reloc :: cont

(* compilation des constantes *)

let rec get_allias env kn =
  let tps = (lookup_constant kn env).const_body_code in
  match Cemitcodes.force tps with
  | BCallias kn' -> get_allias env kn'
  | _ -> kn

(* compilation des expressions *)
 
let rec compile_constr reloc c sz cont =
  match kind_of_term c with
  | Meta _ -> raise (Invalid_argument "Cbytegen.gen_lam : Meta")
  | Evar _ -> raise (Invalid_argument "Cbytegen.gen_lam : Evar")
 
  | Cast(c,_) -> compile_constr reloc c sz cont

  | Rel i -> pos_rel i reloc sz :: cont
  | Var id -> pos_named id reloc :: cont
  | Const kn -> Kgetglobal (get_allias !global_env kn) :: cont
  
  | Sort _  | Ind _ | Construct _ ->
      compile_str_cst reloc (str_const c) sz cont
  
  | LetIn(_,xb,_,body) ->
      compile_constr reloc xb sz 
	(Kpush :: 
	(compile_constr (push_local sz reloc) body (sz+1) (add_pop 1 cont)))
  | Prod(id,dom,codom) ->
      let cont1 = 
	Kpush :: compile_constr reloc dom (sz+1) (Kmakeprod :: cont) in
      compile_constr reloc (mkLambda(id,dom,codom)) sz cont1
  | Lambda _ ->
      let params, body = decompose_lam c in
      let arity = List.length params in
      let r_fun = init_fun arity in
      let lbl_fun = Label.create() in
      let cont_fun = 
	compile_constr r_fun body arity [Kreturn arity] in
      fun_code := [Ksequence(add_grab arity lbl_fun cont_fun,!fun_code)];
      let fv = fv r_fun in
      compile_fv reloc fv.fv_rev sz (Kclosure(lbl_fun,fv.size) :: cont)
 
  | App(f,args) -> 
      begin 
	match kind_of_term f with
	| Construct _ -> compile_str_cst reloc (str_const c) sz cont
	| _ -> comp_app compile_constr compile_constr reloc f args sz cont 
      end
  | Fix ((rec_args,init),(_,type_bodies,rec_bodies)) ->
      let ndef = Array.length type_bodies in
      let rfv = ref empty_fv in
      let lbl_types = Array.create ndef Label.no in
      let lbl_bodies = Array.create ndef Label.no in
      (* Compilation des types *)
      let rtype = init_type ndef rfv in
      for i = 0 to ndef - 1 do
	let lbl,fcode = 
	  label_code 
	    (compile_constr rtype type_bodies.(i) 0 [Kstop]) in 
	lbl_types.(i) <- lbl; 
	fun_code := [Ksequence(fcode,!fun_code)]
      done;
      (* Compilation des corps *)
      for i = 0 to ndef - 1 do
	let params,body = decompose_lam rec_bodies.(i) in
	let arity = List.length params in
	let rbody = init_fix ndef i arity rfv in
	let cont1 = 
	  compile_constr rbody body arity [Kreturn arity] in
	let lbl = Label.create () in
	lbl_bodies.(i) <- lbl;
	let fcode =  
	  if arity = 1 then 
	    Klabel lbl :: Kgrabrec 0 :: Krestart :: cont1
	  else
	    Krestart :: Klabel lbl :: Kgrabrec rec_args.(i) ::
	    Krestart :: Kgrab (arity - 1) :: cont1
	in
	fun_code := [Ksequence(fcode,!fun_code)]
      done;
      let fv = !rfv in
      compile_fv reloc fv.fv_rev sz 
	(Kclosurerec(fv.size,init,lbl_types,lbl_bodies) :: cont)
  
  | CoFix(init,(_,type_bodies,rec_bodies)) ->
      let ndef = Array.length type_bodies in
      let rfv = ref empty_fv in
      let lbl_types = Array.create ndef Label.no in
      let lbl_bodies = Array.create ndef Label.no in
      (* Compilation des types *)
      let rtype = init_type ndef rfv in
      for i = 0 to ndef - 1 do
	let lbl,fcode = 
	  label_code 
	    (compile_constr rtype type_bodies.(i) 0 [Kstop]) in
	lbl_types.(i) <- lbl; 
	fun_code := [Ksequence(fcode,!fun_code)]
      done;
      (* Compilation des corps *)
      for i = 0 to ndef - 1 do
	let params,body = decompose_lam rec_bodies.(i) in
	let arity = List.length params in
	let rbody = init_fix ndef i arity rfv in
	let lbl = Label.create () in

	let cont1 = 
	  compile_constr rbody body arity [Kreturn(arity)] in
	let cont2 = 
	  if arity <= 1 then cont1 else Kgrab (arity - 1) :: cont1 in
	let cont3 = 
	  Krestart :: Klabel lbl :: Kcograb arity :: Krestart :: cont2 in
	fun_code := [Ksequence(cont3,!fun_code)];
	lbl_bodies.(i) <- lbl
      done;
      let fv = !rfv in
      compile_fv reloc fv.fv_rev sz 
	(Kclosurerec(fv.size,init,lbl_types,lbl_bodies) :: cont)
  
  | Case(ci,t,a,branchs) ->
      let ind = ci.ci_ind in
      let mib = lookup_mind (fst ind) !global_env in
      let oib = mib.mind_packets.(snd ind) in
      let tbl = oib.mind_reloc_tbl in
      let lbl_consts = Array.create oib.mind_nb_constant Label.no in
      let lbl_blocks = Array.create (oib.mind_nb_args+1) Label.no in
      let branch1,cont = make_branch cont in
      (* Compilation du type *)
      let lbl_typ,fcode = 	
	label_code (compile_constr reloc t sz [Kpop sz; Kstop])
      in fun_code := [Ksequence(fcode,!fun_code)];
      (* Compilation des branches *) 
      let lbl_sw = Label.create () in
      let sz_b,branch,is_tailcall =
	match branch1 with 
	| Kreturn k -> assert (k = sz); sz, branch1, true
	| _ -> sz+3, Kjump, false
      in
      let annot = {ci = ci; rtbl = tbl; tailcall = is_tailcall} in
     (* Compilation de la branche accumulate *)
      let lbl_accu, code_accu = 
	label_code(Kmakeswitchblock(lbl_typ,lbl_sw,annot,sz) :: branch::cont) 
      in
      lbl_blocks.(0) <- lbl_accu;
      let c = ref code_accu in
      (* Compilation des branches constructeurs *)
      for i = 0 to Array.length tbl - 1 do
	let tag, arity = tbl.(i) in
	if arity = 0 then
	  let lbl_b,code_b = 
	    label_code(compile_constr reloc branchs.(i) sz_b (branch :: !c)) in
	  lbl_consts.(tag) <- lbl_b; 
	  c := code_b
	else 
	  let args, body = decompose_lam branchs.(i) in
	  let nargs = List.length args in
	  let lbl_b,code_b = 
	    label_code(
	    if nargs = arity then
	      Kpushfield arity ::
	      compile_constr (push_param arity sz_b reloc)
		body (sz_b+arity) (add_pop arity (branch :: !c))
	    else
	      let sz_appterm = if is_tailcall then sz_b + arity else arity in
	      Kpushfield arity :: 
	      compile_constr reloc branchs.(i) (sz_b+arity)
		(Kappterm(arity,sz_appterm) :: !c))
	  in
	  lbl_blocks.(tag) <- lbl_b;
	  c := code_b
      done;
      c :=  Klabel lbl_sw :: Kswitch(lbl_consts,lbl_blocks) :: !c;
      let code_sw = 
	match branch1 with
	| Klabel lbl -> Kpush_retaddr lbl ::  !c
	| _ -> !c 
      in
      let cont_a = if mib.mind_finite then code_sw else Kforce :: code_sw in
      compile_constr reloc a sz cont_a 
 
and compile_fv reloc l sz cont =
  match l with
  | [] -> cont
  | [fvn] -> compile_fv_elem reloc fvn sz cont
  | fvn :: tl ->
      compile_fv_elem reloc fvn sz 
	(Kpush :: compile_fv reloc tl (sz + 1) cont)
      
and compile_str_cst reloc sc sz cont =
  match sc with
  | Bconstr c -> compile_constr reloc c sz cont
  | Bstrconst sc -> Kconst sc :: cont
  | Bmakeblock(tag,args) ->
      let nargs = Array.length args in
      comp_args compile_str_cst reloc args sz (Kmakeblock(nargs,tag) :: cont)
  | Bconstruct_app(tag,nparams,arity,args) ->
      if args = [||] then code_construct tag nparams arity cont
      else
	comp_app 
	  (fun _ _ _ cont -> code_construct tag nparams arity cont) 
	  compile_str_cst reloc () args sz cont
      
let compile env c =
  set_global_env env;
  init_fun_code ();
  Label.reset_label_counter ();
  let reloc = empty () in
  let init_code = compile_constr reloc c 0 [Kstop] in
  let fv = List.rev (!(reloc.in_env).fv_rev) in
  if Options.print_bytecodes() then 
    (draw_instr init_code; draw_instr !fun_code);
  init_code,!fun_code, Array.of_list fv


let compile_constant_body env kn body opaque boxed =
  if opaque then BCconstant
  else match body with
  | None -> BCconstant
  | Some sb ->
      let body = Declarations.force sb in
      match kind_of_term body with
      | Const kn' -> BCallias (get_allias env kn')
      | Construct _ ->
	  let res = compile env body in
	  let to_patch = to_memory res in
	  BCdefined (false,to_patch)

      | _ -> 
	  let res = compile env body in
	  let to_patch = to_memory res in
	  (*if Options.print_bytecodes() then 
	    (let init,fun_code,_= res in
	    draw_instr init; draw_instr fun_code);*)
	  BCdefined (boxed && Options.boxed_definitions (),to_patch)

