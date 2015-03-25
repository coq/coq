open Util
open Names
open Cbytecodes
open Cemitcodes
open Term
open Declarations
open Pre_env


(* Compilation des variables + calcul des variables libres               *)

(* Dans la machine virtuel il n'y a pas de difference entre les           *)
(* fonctions et leur environnement                                        *)

(* Representation de l'environnements des fonctions :                     *)
(*        [clos_t | code | fv1 | fv2 | ... | fvn ]                        *)
(*                ^                                                       *)
(*  l'offset pour l'acces au variable libre est 1 (il faut passer le      *)
(*  pointeur de code).                                                    *)
(*  Lors de la compilation, les variables libres sont stock'ees dans      *)
(*  [in_env] dans l'ordre inverse de la representation machine, ceci      *)
(* permet de rajouter des nouvelles variables dans l'environnememt        *)
(* facilement.                                                            *)
(* Les arguments de la fonction arrive sur la pile dans l'ordre de        *)
(* l'application :  f arg1 ... argn                                       *)
(*   - la pile est alors :                                                *)
(*        arg1 : ... argn : extra args : return addr : ...                *)
(* Dans le corps de la fonction [arg1] est repr'esent'e par le de Bruijn  *)
(*  [n], [argn] par le de Bruijn [1]                                      *)

(* Representation des environnements des points fix mutuels :             *)
(* [t1|C1| ... |tc|Cc| ... |t(nbr)|C(nbr)| fv1 | fv2 | .... | fvn | type] *)
(*                ^<----------offset--------->                            *)
(* type = [Ct1 | .... | Ctn]                                              *)
(* Ci est le code correspondant au corps du ieme point fix                *)
(* Lors de l'evaluation d'un point fix l'environnement est un pointeur    *)
(* sur la position correspondante a son code.                             *)
(* Dans le corps de chaque point fix le de Bruijn [nbr] represente,       *)
(* le 1er point fix de la declaration mutuelle, le de Bruijn [1] le       *)
(* nbr-ieme.                                                              *)
(* L'acces a ces variables se fait par l'instruction [Koffsetclosure]     *)
(*  (decalage de l'environnement)                                         *)

(* Ceci permet de representer tout les point fix mutuels en un seul bloc  *)
(* [Ct1 | ... | Ctn] est un tableau contant le code d'evaluation des      *)
(* types des points fixes, ils sont utilises pour tester la conversion    *)
(* Leur environnement d'execution est celui du dernier point fix :        *)
(* [t1|C1| ... |tc|Cc| ... |t(nbr)|C(nbr)| fv1 | fv2 | .... | fvn | type] *)
(*                                ^                                       *)


(* Representation des cofix mutuels :                                     *)
(*  a1 =   [A_t | accumulate | [Cfx_t | fcofix1 ] ]                       *)
(*                ...                                                     *)
(*  anbr = [A_t | accumulate | [Cfx_t | fcofixnbr ] ]                     *)
(*                                                                        *)
(*  fcofix1 = [clos_t   | code1   | a1 |...| anbr | fv1 |...| fvn | type] *)
(*                      ^                                                 *)
(*                ...                                                     *)
(*  fcofixnbr = [clos_t | codenbr | a1 |...| anbr | fv1 |...| fvn | type] *)
(*                      ^                                                 *)
(*  Les block [ai] sont des fonctions qui accumulent leurs arguments :    *)
(*           ai arg1  argp --->                                           *)
(*    ai' = [A_t | accumulate | [Cfx_t | fcofixi] | arg1 | ... | argp ]   *)
(* Si un tel bloc arrive sur un [match] il faut forcer l'evaluation,      *)
(* la fonction [fcofixi] est alors appliqu'ee a [ai'] [arg1] ... [argp]   *)
(* A la fin de l'evaluation [ai'] est mis a jour avec le resultat de      *)
(* l'evaluation :                                                         *)
(*  ai' <--                                                               *)
(*   [A_t | accumulate | [Cfxe_t |fcofixi|result] | arg1 | ... | argp ]   *)
(* L'avantage de cette representation est qu'elle permet d'evaluer qu'une *)
(* fois l'application d'un cofix (evaluation lazy)                        *)
(* De plus elle permet de creer facilement des cycles quand les cofix ne  *)
(* n'ont pas d'aruments, ex:                                              *)
(*   cofix one := cons 1 one                                              *)
(*   a1 = [A_t | accumulate | [Cfx_t|fcofix1] ]                           *)
(*   fcofix1 = [clos_t | code | a1]                                       *)
(*  Quand on force l'evaluation de [a1] le resultat est                   *)
(*    [cons_t | 1 | a1]                                                   *)
(*  [a1] est mis a jour :                                                 *)
(*  a1 = [A_t | accumulate | [Cfxe_t | fcofix1 | [cons_t | 1 | a1]] ]     *)
(* Le cycle est cree ...                                                  *)
   
(* On conserve la fct de cofix pour la conversion                         *)
   
type vm_env = {
    size : int;              (* longueur de la liste [n] *)
    fv_rev : fv_elem list    (* [fvn; ... ;fv1] *)
  }    
   
let empty_fv = { size= 0;  fv_rev = [] }
   
type comp_env = { 
    nb_stack : int;              (* nbre de variables sur la pile          *)
    in_stack : int list;         (* position dans la pile                  *)
    nb_rec : int;                (* nbre de fonctions mutuellement         *)
                                 (* recursives =  nbr                      *)
    pos_rec  : instruction list; (* instruction d'acces pour les variables *)
                                 (*  de point fix ou de cofix              *)
    offset : int;                 
    in_env : vm_env ref 
  } 

let fv r = !(r.in_env)
   
let empty_comp_env ()= 
  { nb_stack = 0; 
    in_stack = [];
    nb_rec = 0;
    pos_rec = [];
    offset = 0; 
    in_env = ref empty_fv;
  } 

(*i Creation functions for comp_env *)

let rec add_param n sz l =
  if n = 0 then l else add_param (n - 1) sz (n+sz::l) 
   
let comp_env_fun arity = 
  { nb_stack = arity; 
    in_stack = add_param arity 0 [];
    nb_rec = 0;
    pos_rec = [];
    offset = 1; 
    in_env = ref empty_fv 
  } 
    

let comp_env_type rfv = 
  { nb_stack = 0; 
    in_stack = [];
    nb_rec = 0;
    pos_rec = [];
    offset = 1; 
    in_env = rfv 
  }
   
let comp_env_fix ndef curr_pos arity rfv =
   let prec = ref [] in
   for i = ndef downto 1 do
     prec := Koffsetclosure (2 * (ndef - curr_pos - i)) :: !prec 
   done;
   { nb_stack = arity; 
     in_stack = add_param arity 0 [];
     nb_rec = ndef; 
     pos_rec = !prec;
     offset = 2 * (ndef - curr_pos - 1)+1;
     in_env = rfv 
   } 

let comp_env_cofix ndef arity rfv =
   let prec = ref [] in
   for i = 1 to ndef do
     prec := Kenvacc i :: !prec
   done;
   { nb_stack = arity; 
     in_stack = add_param arity 0 [];
     nb_rec = ndef; 
     pos_rec = !prec;
     offset = ndef+1;
     in_env = rfv 
   }

(* [push_param ] ajoute les parametres de fonction dans la pile *)
let push_param n sz r =
  { r with
    nb_stack = r.nb_stack + n;
    in_stack = add_param n sz r.in_stack }

(* [push_local e sz] ajoute une nouvelle variable dans la pile a la *)
(* position [sz]                                                    *)
let push_local sz r = 
  { r with 
    nb_stack = r.nb_stack + 1;
    in_stack = (sz + 1) :: r.in_stack }



(*i Compilation of variables *)
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
  else
    let i = i - r.nb_stack in
    if i <= r.nb_rec then 
      try List.nth r.pos_rec (i-1)
      with _ -> assert false
    else
      let i = i - r.nb_rec in
      let db = FVrel(i) in
      let env = !(r.in_env) in
      try Kenvacc(r.offset + env.size - (find_at db env.fv_rev))
      with Not_found ->
	let pos = env.size in
	r.in_env := { size = pos+1; fv_rev =  db:: env.fv_rev};
	Kenvacc(r.offset + pos)

(*i  Examination of the continuation *)

(* Discard all instructions up to the next label.                        *)
(* This function is to be applied to the continuation before adding a    *)
(* non-terminating instruction (branch, raise, return, appterm)          *)
(* in front of it.                                                       *)

let rec discard_dead_code cont = cont
(*function
    [] -> []
  | (Klabel _ | Krestart ) :: _ as cont -> cont
  | _ :: cont -> discard_dead_code cont
*)

(* Return a label to the beginning of the given continuation.            *)
(*   If the sequence starts with a branch, use the target of that branch *)
(*   as the label, thus avoiding a jump to a jump.                       *)

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

(* Extention of the continuation *)
	
(* Add a Kpop n instruction in front of a continuation *)
let rec add_pop n = function
  | Kpop m :: cont -> add_pop (n+m) cont
  | Kreturn m:: cont -> Kreturn (n+m) ::cont
  | cont -> if n = 0 then cont else Kpop n :: cont

let add_grab arity lbl cont =
  if arity = 1 then Klabel lbl :: cont
  else Krestart :: Klabel lbl :: Kgrab (arity - 1) :: cont
 
let add_grabrec rec_arg arity lbl cont =
  if arity = 1 then 
    Klabel lbl :: Kgrabrec 0 :: Krestart :: cont
  else
    Krestart :: Klabel lbl :: Kgrabrec rec_arg ::
    Krestart :: Kgrab (arity - 1) :: cont

(* continuation of a cofix *)

let cont_cofix arity =
    (* accu = res                                                         *)
    (* stk  = ai::args::ra::...                                           *)
    (* ai   = [At|accumulate|[Cfx_t|fcofix]|args]                         *)
  [ Kpush;
    Kpush;        (*                 stk = res::res::ai::args::ra::...    *)
    Kacc 2;
    Kfield 1;
    Kfield 0;
    Kmakeblock(2, cofix_evaluated_tag); 
    Kpush;        (*  stk = [Cfxe_t|fcofix|res]::res::ai::args::ra::...*)
    Kacc 2;
    Ksetfield 1;  (*   ai = [At|accumulate|[Cfxe_t|fcofix|res]|args]      *)
                  (*  stk = res::ai::args::ra::...                        *)   
    Kacc 0;       (* accu = res                                           *)
    Kreturn (arity+2) ]


(*i Global environment global *)

let global_env = ref empty_env

let set_global_env env = global_env := env


(* Code des fermetures *)
let fun_code = ref []

let init_fun_code () = fun_code := []

(* Compilation des constructeurs et des inductifs *)


(* Limitation due to OCaml's representation of non-constant
  constructors: limited to 245 + 1 (0 tag) cases. *)

exception TooLargeInductive of identifier

let max_nb_const = 0x1000000 
let max_nb_block = 0x1000000 + last_variant_tag - 1

let str_max_constructors = 
  Format.sprintf 
    " which has more than %i constant constructors or more than %i non-constant constructors" max_nb_const max_nb_block

let check_compilable ib = 
  
  if not (ib.mind_nb_args <= max_nb_block && ib.mind_nb_constant <= max_nb_const) then 
    raise (TooLargeInductive ib.mind_typename)

(* Inv: arity > 0 *)

let const_bn tag args = 
  if tag < last_variant_tag then Const_bn(tag, args)
  else
    Const_bn(last_variant_tag, Array.append [|Const_b0 (tag - last_variant_tag) |] args)

  
let code_makeblock arity tag cont = 
  if tag < last_variant_tag then
    Kmakeblock(arity, tag) :: cont
  else
    Kpush :: Kconst (Const_b0 (tag - last_variant_tag)) ::
    Kmakeblock(arity+1, last_variant_tag) :: cont

(* Inv : nparam + arity > 0 *)
let code_construct tag nparams arity cont =
  let f_cont =
      add_pop nparams
      (if arity = 0 then 
	[Kconst (Const_b0 tag); Kreturn 0]
       else if tag < last_variant_tag then
         [Kacc 0; Kpop 1; Kmakeblock(arity, tag); Kreturn 0]
       else 
         [Kconst (Const_b0 (tag - last_variant_tag)); 
          Kmakeblock(arity+1, last_variant_tag); Kreturn 0])
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
  | Cast(c,_,_) -> str_const c 
  | App(f,args) -> 
      begin
	match kind_of_term f with
	| Construct((kn,j),i) -> 
	    let oib = lookup_mind kn !global_env in
	    let oip = oib.mind_packets.(j) in
	    let () = check_compilable oip in
	    let tag,arity = oip.mind_reloc_tbl.(i-1) in
	    let nparams = oib.mind_nparams in
	    if nparams + arity = Array.length args then
	      if arity = 0 then Bstrconst(Const_b0 tag)
	      else
		let rargs = Array.sub args nparams arity in
		let b_args = Array.map str_const rargs in
		try 
		  let sc_args = Array.map get_strcst b_args in
		  Bstrconst(const_bn tag sc_args)
		with Not_found ->
		  Bmakeblock(tag,b_args)
	    else  
	      let b_args = Array.map str_const args in
	      Bconstruct_app(tag, nparams, arity, b_args)
	| _ -> Bconstr c
      end
  | Ind ind -> Bstrconst (Const_ind ind)
  | Construct ((kn,j),i) ->  
      let oib = lookup_mind kn !global_env in 
      let oip = oib.mind_packets.(j) in
      let () = check_compilable oip in
      let num,arity = oip.mind_reloc_tbl.(i-1) in
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

let rec compile_fv reloc l sz cont =
  match l with
  | [] -> cont
  | [fvn] -> compile_fv_elem reloc fvn sz cont
  | fvn :: tl ->
      compile_fv_elem reloc fvn sz 
	(Kpush :: compile_fv reloc tl (sz + 1) cont)

(* compilation des constantes *)

let rec get_allias env kn =
  let cb = lookup_constant kn env in
  let tps = cb.const_body_code in
    match tps with
    | None -> kn
    | Some tps ->
       (match Cemitcodes.force tps with
	| BCallias kn' -> get_allias env kn'
	| _ -> kn)

(* Compiling expressions *)

let rec compile_constr reloc c sz cont =
  match kind_of_term c with
  | Meta _ -> raise (Invalid_argument "Cbytegen.compile_constr : Meta")
  | Evar _ -> raise (Invalid_argument "Cbytegen.compile_constr : Evar")
 
  | Cast(c,_,_) -> compile_constr reloc c sz cont

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
      let r_fun = comp_env_fun arity in
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
      let env_type = comp_env_type rfv in
      for i = 0 to ndef - 1 do
	let lbl,fcode = 
	  label_code 
	    (compile_constr env_type type_bodies.(i) 0 [Kstop]) in 
	lbl_types.(i) <- lbl; 
	fun_code := [Ksequence(fcode,!fun_code)]
      done;
      (* Compilation des corps *)
      for i = 0 to ndef - 1 do
	let params,body = decompose_lam rec_bodies.(i) in
	let arity = List.length params in
	let env_body = comp_env_fix ndef i arity rfv in
	let cont1 = 
	  compile_constr env_body body arity [Kreturn arity] in
	let lbl = Label.create () in
	lbl_bodies.(i) <- lbl;
	let fcode =  add_grabrec rec_args.(i) arity lbl cont1 in
	fun_code := [Ksequence(fcode,!fun_code)]
      done;
      let fv = !rfv in
      compile_fv reloc fv.fv_rev sz 
	(Kclosurerec(fv.size,init,lbl_types,lbl_bodies) :: cont)
  
  | CoFix(init,(_,type_bodies,rec_bodies)) ->
      let ndef = Array.length type_bodies in
      let lbl_types = Array.create ndef Label.no in
      let lbl_bodies = Array.create ndef Label.no in
      (* Compilation des types *)
      let rfv = ref empty_fv in
      let env_type = comp_env_type rfv in
      for i = 0 to ndef - 1 do
	let lbl,fcode = 
	  label_code 
	    (compile_constr env_type type_bodies.(i) 0 [Kstop]) in
	lbl_types.(i) <- lbl; 
	fun_code := [Ksequence(fcode,!fun_code)]
      done;
      (* Compilation des corps *)
      for i = 0 to ndef - 1 do
	let params,body = decompose_lam rec_bodies.(i) in
	let arity = List.length params in
	let env_body = comp_env_cofix ndef arity rfv in
	let lbl = Label.create () in
	let cont1 = 
	  compile_constr env_body body (arity+1) (cont_cofix arity) in
	let cont2 = 
	  add_grab (arity+1) lbl cont1 in
	lbl_bodies.(i) <- lbl;
	fun_code := [Ksequence(cont2,!fun_code)];
      done;
      let fv = !rfv in
      compile_fv reloc fv.fv_rev sz 
	(Kclosurecofix(fv.size, init, lbl_types, lbl_bodies) :: cont)
  
  | Case(ci,t,a,branchs) ->
      let ind = ci.ci_ind in
      let mib = lookup_mind (fst ind) !global_env in
      let oib = mib.mind_packets.(snd ind) in
      let () = check_compilable oib in
      let tbl = oib.mind_reloc_tbl in
      let lbl_consts = Array.make oib.mind_nb_constant Label.no in
      let nallblock = oib.mind_nb_args + 1 in (* +1 : accumulate *)
      let nblock = min nallblock (last_variant_tag + 1) in
      let lbl_blocks = Array.make nblock Label.no in
      let neblock = max 0 (nallblock - last_variant_tag) in
      let lbl_eblocks = Array.make neblock Label.no in 
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
      (* perform the extra match if needed (to many block constructors) *)
      if neblock <> 0 then begin
        let lbl_b, code_b = 
          label_code (
            Kpush :: Kfield 0 :: Kswitch(lbl_eblocks, [||]) :: !c) in
        lbl_blocks.(last_variant_tag) <- lbl_b;
        c := code_b
      end;  
      
      (* Compiling regular constructor branches *)
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
          let code_b =  
            if nargs = arity then
	      compile_constr (push_param arity sz_b reloc)
		body (sz_b+arity) (add_pop arity (branch :: !c))
	    else
	      let sz_appterm = if is_tailcall then sz_b + arity else arity in
	      compile_constr reloc branchs.(i) (sz_b+arity)
		(Kappterm(arity,sz_appterm) :: !c) in
          let code_b = 
            if tag < last_variant_tag then Kpushfields arity :: code_b
            else Kacc 0::Kpop 1::Kpushfields(arity+1)::Kpop 1::code_b in
          let lbl_b,code_b = label_code code_b in
          if tag < last_variant_tag then lbl_blocks.(tag) <- lbl_b
          else lbl_eblocks.(tag - last_variant_tag) <- lbl_b;
	  c := code_b
      done;
      c := Klabel lbl_sw :: Kswitch(lbl_consts,lbl_blocks) :: !c;
      let code_sw = 
	match branch1 with
	| Klabel lbl -> Kpush_retaddr lbl ::  !c
	| _ -> !c 
      in
      compile_constr reloc a sz code_sw
       
and compile_str_cst reloc sc sz cont =
  match sc with
  | Bconstr c -> compile_constr reloc c sz cont
  | Bstrconst sc -> Kconst sc :: cont
  | Bmakeblock(tag,args) ->
      let nargs = Array.length args in
      comp_args compile_str_cst reloc args sz (code_makeblock nargs tag cont)
  | Bconstruct_app(tag,nparams,arity,args) ->
      if Array.length args = 0 then code_construct tag nparams arity cont
      else
	comp_app 
	  (fun _ _ _ cont -> code_construct tag nparams arity cont) 
	  compile_str_cst reloc () args sz cont

open Pp
      
let compile fail_on_error env c =
  set_global_env env;
  init_fun_code ();
  Label.reset_label_counter ();
  let reloc = empty_comp_env () in
  try 
    let init_code = compile_constr reloc c 0 [Kstop] in
    let fv = List.rev (!(reloc.in_env).fv_rev) in
    Some (init_code,!fun_code, Array.of_list fv)
  with TooLargeInductive tname ->
    let fn = 
      (* if fail_on_error then Errors.errorlabstrm "compile" else *) 
      msg_warning in
    (fn
	   (str "Cannot compile code for virtual machine as it uses inductive " ++
	      (str (Names.string_of_id tname) ++ str str_max_constructors));
       None)

let compile_constant_body fail_on_error env body opaque boxed =
  if opaque then Some BCconstant
  else match body with
  | None -> Some BCconstant
  | Some sb ->
    let body = Declarations.force sb in
    if boxed then
      let res = compile fail_on_error env body in
      option_map (fun x -> BCdefined(true, to_memory x)) res
    else
      match kind_of_term body with
      | Const kn' -> Some (BCallias (get_allias env kn'))
      | _ ->
        let res = compile fail_on_error env body in
	option_map (fun x -> BCdefined (false, to_memory x)) res
