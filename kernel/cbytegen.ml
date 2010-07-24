(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Author: Benjamin Grégoire as part of the bytecode-based virtual reduction
   machine, Oct 2004 *)
(* Extension: Arnaud Spiwack (support for native arithmetic), May 2005 *)

open Util
open Names
open Cbytecodes
open Cemitcodes
open Term
open Declarations
open Pre_env


(* Compilation des variables + calcul des variables libres                *)

(* Dans la machine virtuelle il n'y a pas de difference entre les         *)
(* fonctions et leur environnement                                        *)

(* Representation de l'environnement des fonctions :                      *)
(*        [clos_t | code | fv1 | fv2 | ... | fvn ]                        *)
(*                ^                                                       *)
(*  l'offset pour l'acces aux variables libres est 1 (il faut passer le   *)
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

(* Representation des environnements des points fixes mutuels :           *)
(* [t1|C1| ... |tc|Cc| ... |t(nbr)|C(nbr)| fv1 | fv2 | .... | fvn | type] *)
(*                ^<----------offset--------->                            *)
(* type = [Ct1 | .... | Ctn]                                              *)
(* Ci est le code correspondant au corps du ieme point fixe               *)
(* Lors de l'evaluation d'un point fixe l'environnement est un pointeur   *)
(* sur la position correspondante a son code.                             *)
(* Dans le corps de chaque point fixe le de Bruijn [nbr] represente,      *)
(* le 1er point fixe de la declaration mutuelle, le de Bruijn [1] le      *)
(* nbr-ieme.                                                              *)
(* L'acces a ces variables se fait par l'instruction [Koffsetclosure]     *)
(*  (decalage de l'environnement)                                         *)

(* Ceci permet de representer les points fixes mutuels en un seul bloc    *)
(* [Ct1 | ... | Ctn] est un tableau contenant le code d'evaluation des    *)
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
(*  Les blocs [ai] sont des fonctions qui accumulent leurs arguments :    *)
(*           ai arg1  argp --->                                           *)
(*    ai' = [A_t | accumulate | [Cfx_t | fcofixi] | arg1 | ... | argp ]   *)
(* Si un tel bloc arrive sur un [match] il faut forcer l'evaluation,      *)
(* la fonction [fcofixi] est alors appliqu'ee a [ai'] [arg1] ... [argp]   *)
(* A la fin de l'evaluation [ai'] est mis a jour avec le resultat de      *)
(* l'evaluation :                                                         *)
(*  ai' <--                                                               *)
(*   [A_t | accumulate | [Cfxe_t |fcofixi|result] | arg1 | ... | argp ]   *)
(* L'avantage de cette representation est qu'elle permet de n'evaluer     *)
(* qu'une fois l'application d'un cofix (evaluation lazy)                 *)
(* De plus elle permet de creer facilement des cycles quand les cofix     *)
(* n'ont pas d'argument, ex:                                              *)
(*   cofix one := cons 1 one                                              *)
(*   a1 = [A_t | accumulate | [Cfx_t|fcofix1] ]                           *)
(*   fcofix1 = [clos_t | code | a1]                                       *)
(*  Quand on force l'evaluation de [a1] le resultat est                   *)
(*    [cons_t | 1 | a1]                                                   *)
(*  [a1] est mis a jour :                                                 *)
(*  a1 = [A_t | accumulate | [Cfxe_t | fcofix1 | [cons_t | 1 | a1]] ]     *)
(* Le cycle est cree ...                                                  *)

(* On conserve la fct de cofix pour la conversion                         *)


let empty_fv = { size= 0;  fv_rev = [] }

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
  | Kbranch lbl :: _ as cont -> (lbl, cont)
  | cont -> let lbl = Label.create() in (lbl, Klabel lbl :: cont)

(* Return a branch to the continuation. That is, an instruction that,
   when executed, branches to the continuation or performs what the
   continuation performs. We avoid generating branches to returns. *)
(* spiwack: make_branch was only used once. Changed it back to the ZAM
      one to match the appropriate semantics (old one avoided the
      introduction of an unconditional branch operation, which seemed
      appropriate for the 31-bit integers' code). As a memory, I leave
      the former version in this comment.
let make_branch cont =
  match cont with
  | (Kreturn _ as return) :: cont' -> return, cont'
  | Klabel lbl as b :: _ -> b, cont
  | _ -> let b = Klabel(Label.create()) in b,b::cont
*)

let rec make_branch_2 lbl n cont =
  function
    Kreturn m :: _ -> (Kreturn (n + m), cont)
  | Klabel _ :: c  -> make_branch_2 lbl n cont c
  | Kpop m :: c    -> make_branch_2 lbl (n + m) cont c
  | _              ->
      match lbl with
        Some lbl -> (Kbranch lbl, cont)
      | None     -> let lbl = Label.create() in (Kbranch lbl, Klabel lbl :: cont)

let make_branch cont =
  match cont with
    (Kbranch _ as branch) :: _ -> (branch, cont)
  | (Kreturn _ as return) :: _ -> (return, cont)
  | Klabel lbl :: _ -> make_branch_2 (Some lbl) 0 cont cont
  | _ ->  make_branch_2 (None) 0 cont cont

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
            begin
	    let oib = lookup_mind kn !global_env in
	    let oip = oib.mind_packets.(j) in
	    let num,arity = oip.mind_reloc_tbl.(i-1) in
	    let nparams = oib.mind_nparams in
	    if nparams + arity = Array.length args then
              (* spiwack: *)
              (* 1/ tries to compile the constructor in an optimal way,
                    it is supposed to work only if the arguments are
                    all fully constructed, fails with Cbytecodes.NotClosed.
                    it can also raise Not_found when there is no special
                    treatment for this constructor
                    for instance: tries to to compile an integer of the
                        form I31 D1 D2 ... D31 to [D1D2...D31] as
                        a processor number (a caml number actually) *)
              try
		try
		  Bstrconst (Retroknowledge.get_vm_constant_static_info
                                              (!global_env).retroknowledge
                                              (kind_of_term f) args)
                with NotClosed ->
		  (* 2/ if the arguments are not all closed (this is
                        expectingly (and it is currently the case) the only
                        reason why this exception is raised) tries to
                        give a clever, run-time behavior to the constructor.
                        Raises Not_found if there is no special treatment
                        for this integer.
                        this is done in a lazy fashion, using the constructor
                        Bspecial because it needs to know the continuation
                        and such, which can't be done at this time.
                        for instance, for int31: if one of the digit is
                            not closed, it's not impossible that the number
                            gets fully instanciated at run-time, thus to ensure
                            uniqueness of the representation in the vm
                            it is necessary to try and build a caml integer
                            during the execution *)
		  let rargs = Array.sub args nparams arity in
		  let b_args = Array.map str_const rargs in
		  Bspecial ((Retroknowledge.get_vm_constant_dynamic_info
                                           (!global_env).retroknowledge
                                           (kind_of_term f)),
                           b_args)
              with Not_found ->
		(* 3/ if no special behavior is available, then the compiler
		      falls back to the normal behavior *)
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
	     (* spiwack: tries first to apply the run-time compilation
                behavior of the constructor, as in 2/ above *)
	      try
		Bspecial ((Retroknowledge.get_vm_constant_dynamic_info
                                           (!global_env).retroknowledge
                                           (kind_of_term f)),
                         b_args)
	      with Not_found ->
	        Bconstruct_app(num, nparams, arity, b_args)
              end
	| _ -> Bconstr c
      end
  | Ind ind -> Bstrconst (Const_ind ind)
  | Construct ((kn,j),i) ->  
      begin
      (* spiwack: tries first to apply the run-time compilation
           behavior of the constructor, as in 2/ above *)
      try
	Bspecial ((Retroknowledge.get_vm_constant_dynamic_info
                                           (!global_env).retroknowledge
                                           (kind_of_term c)),
                         [| |])
      with Not_found ->
	let oib = lookup_mind kn !global_env in
	let oip = oib.mind_packets.(j) in
	let num,arity = oip.mind_reloc_tbl.(i-1) in
	let nparams = oib.mind_nparams in
	if nparams + arity = 0 then Bstrconst(Const_b0 num)
	else Bconstruct_app(num,nparams,arity,[||])
      end
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
  let tps = (lookup_constant kn env).const_body_code in
  match Cemitcodes.force tps with
  | BCallias kn' -> get_allias env kn'
  | _ -> kn


(* compilation des expressions *)

let rec compile_constr reloc c sz cont =
  match kind_of_term c with
  | Meta _ -> raise (Invalid_argument "Cbytegen.compile_constr : Meta")
  | Evar _ -> raise (Invalid_argument "Cbytegen.compile_constr : Evar")

  | Cast(c,_,_) -> compile_constr reloc c sz cont

  | Rel i -> pos_rel i reloc sz :: cont
  | Var id -> pos_named id reloc :: cont
  | Const kn -> compile_const reloc kn [||] sz cont
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
        | Const kn -> compile_const reloc kn args sz cont
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
	      Kpushfields arity ::
	      compile_constr (push_param arity sz_b reloc)
		body (sz_b+arity) (add_pop arity (branch :: !c))
	    else
	      let sz_appterm = if is_tailcall then sz_b + arity else arity in
	      Kpushfields arity ::
	      compile_constr reloc branchs.(i) (sz_b+arity)
		(Kappterm(arity,sz_appterm) :: !c))
	  in
	  lbl_blocks.(tag) <- lbl_b;
	  c := code_b
      done;
      c :=  Klabel lbl_sw :: Kswitch(lbl_consts,lbl_blocks) :: !c;
      let code_sw =
 	match branch1 with
        (* spiwack : branch1 can't be a lbl anymore it's a Branch instead
	| Klabel lbl -> Kpush_retaddr lbl ::  !c *)
        | Kbranch lbl -> Kpush_retaddr lbl ::  !c
	| _ -> !c
      in
      compile_constr reloc a sz
      (try
	let entry = Term.Ind ind in
	Retroknowledge.get_vm_before_match_info (!global_env).retroknowledge
	                                       entry code_sw
      with Not_found ->
	code_sw)

and compile_str_cst reloc sc sz cont =
  match sc with
  | Bconstr c -> compile_constr reloc c sz cont
  | Bstrconst sc -> Kconst sc :: cont
  | Bmakeblock(tag,args) ->
      let nargs = Array.length args in
      comp_args compile_str_cst reloc args sz (Kmakeblock(nargs,tag) :: cont)
  | Bconstruct_app(tag,nparams,arity,args) ->
      if Array.length args = 0 then code_construct tag nparams arity cont
      else
	comp_app
	  (fun _ _ _ cont -> code_construct tag nparams arity cont)
	  compile_str_cst reloc () args sz cont
  | Bspecial (comp_fx, args) -> comp_fx reloc args sz cont


(* spiwack : compilation of constants with their arguments.
   Makes a special treatment with 31-bit integer addition *)
and compile_const =
  fun reloc-> fun  kn -> fun args -> fun sz -> fun cont ->
  let nargs = Array.length args in
  (* spiwack: checks if there is a specific way to compile the constant
              if there is not, Not_found is raised, and the function
              falls back on its normal behavior *)
  try
    Retroknowledge.get_vm_compiling_info (!global_env).retroknowledge
                  (kind_of_term (mkConst kn)) reloc args sz cont
  with Not_found ->
    if nargs = 0 then
      Kgetglobal (get_allias !global_env kn) :: cont
    else
      comp_app (fun _ _ _ cont ->
                   Kgetglobal (get_allias !global_env kn) :: cont)
        compile_constr reloc () args sz cont

let compile env c =
  set_global_env env;
  init_fun_code ();
  Label.reset_label_counter ();
  let reloc = empty_comp_env () in
  let init_code = compile_constr reloc c 0 [Kstop] in
  let fv = List.rev (!(reloc.in_env).fv_rev) in
(*  draw_instr init_code;
  draw_instr !fun_code;
  Format.print_string "fv = ";
  List.iter (fun v ->
    match v with
    | FVnamed id -> Format.print_string ((string_of_id id)^"; ")
    | FVrel i -> Format.print_string ((string_of_int i)^"; ")) fv;  Format
    .print_string "\n";
  Format.print_flush();  *)
  init_code,!fun_code, Array.of_list fv

let compile_constant_body env body opaque boxed =
  if opaque then BCconstant
  else match body with
  | None -> BCconstant
  | Some sb ->
      let body = Declarations.force sb in
      if boxed then
	let res = compile env body in
	let to_patch = to_memory res in
	BCdefined(true, to_patch)
      else
	match kind_of_term body with
	| Const kn' ->
	    (* we use the canonical name of the constant*)
	    let con= constant_of_kn (canonical_con kn') in
	      BCallias (get_allias env con)
	| _ ->
	    let res = compile env body in
	    let to_patch = to_memory res in
	    BCdefined (false, to_patch)


(* spiwack: additional function which allow different part of compilation of the
      31-bit integers *)

let make_areconst n else_lbl cont =
  if n <=0 then
    cont
  else
    Kareconst (n, else_lbl)::cont


(* try to compile int31 as a const_b0. Succeed if all the arguments are closed
   fails otherwise by raising NotClosed*)
let compile_structured_int31 fc args =
  if not fc then raise Not_found else
  Const_b0
    (Array.fold_left
       (fun temp_i -> fun t -> match kind_of_term t with
          | Construct (_,d) -> 2*temp_i+d-1
          | _ -> raise NotClosed)
       0 args
    )

(* this function is used for the compilation of the constructor of
   the int31, it is used when it appears not fully applied, or
   applied to at least one non-closed digit *)
let dynamic_int31_compilation fc reloc args sz cont =
  if not fc then raise Not_found else
    let nargs = Array.length args in
      if nargs = 31 then
	let (escape,labeled_cont) = make_branch cont in
	let else_lbl = Label.create() in
	  comp_args compile_str_cst reloc args sz
            ( Kisconst else_lbl::Kareconst(30,else_lbl)::Kcompint31::escape::Klabel else_lbl::Kmakeblock(31, 1)::labeled_cont)
      else
	let code_construct cont = (* spiwack: variant of the global code_construct
                                     which handles dynamic compilation of
                                     integers *)
          let f_cont =
            let else_lbl = Label.create () in
	      [Kacc 0; Kpop 1; Kisconst else_lbl; Kareconst(30,else_lbl);
               Kcompint31; Kreturn 0; Klabel else_lbl; Kmakeblock(31, 1); Kreturn 0]
	  in
	  let lbl = Label.create() in
	    fun_code := [Ksequence (add_grab 31 lbl f_cont,!fun_code)];
	    Kclosure(lbl,0) :: cont
	in
	  if nargs = 0 then
	    code_construct cont
	  else
	    comp_app (fun _ _ _ cont -> code_construct cont)
              compile_str_cst reloc () args sz cont

(*(* template compilation for 2ary operation, it probably possible
   to make a generic such function with arity abstracted *)
let op2_compilation op =
  let code_construct normal cont =  (*kn cont =*)
     let f_cont =
         let else_lbl = Label.create () in
         Kareconst(2, else_lbl):: Kacc 0:: Kpop 1::
          op:: Kreturn 0:: Klabel else_lbl::
         (* works as comp_app with nargs = 2 and tailcall cont [Kreturn 0]*)
          (*Kgetglobal (get_allias !global_env kn):: *)
          normal::
          Kappterm(2, 2):: [] (* = discard_dead_code [Kreturn 0] *)
     in
     let lbl = Label.create () in
     fun_code := [Ksequence (add_grab 2 lbl f_cont, !fun_code)];
     Kclosure(lbl, 0)::cont
  in
  fun normal fc _ reloc args sz cont ->
  if not fc then raise Not_found else
  let nargs = Array.length args in
  if nargs=2 then (*if it is a fully applied addition*)
    let (escape, labeled_cont) = make_branch cont in
    let else_lbl = Label.create () in
      comp_args compile_constr reloc args sz
	(Kisconst else_lbl::(make_areconst 1  else_lbl
           (*Kaddint31::escape::Klabel else_lbl::Kpush::*)
           (op::escape::Klabel else_lbl::Kpush::
           (* works as comp_app with nargs = 2 and non-tailcall cont*)
           (*Kgetglobal (get_allias !global_env kn):: *)
           normal::
           Kapply 2::labeled_cont)))
  else if nargs=0 then
    code_construct normal cont
  else
    comp_app (fun _ _ _ cont -> code_construct normal cont)
      compile_constr reloc () args sz cont *)

(*template for n-ary operation, invariant: n>=1,
  the operations does the following :
  1/ checks if all the arguments are constants (i.e. non-block values)
  2/ if they are, uses the "op" instruction to execute
  3/ if at least one is not, branches to the normal behavior:
      Kgetglobal (get_allias !global_env kn) *)
let op_compilation n op =
  let code_construct kn cont =
     let f_cont =
         let else_lbl = Label.create () in
         Kareconst(n, else_lbl):: Kacc 0:: Kpop 1::
          op:: Kreturn 0:: Klabel else_lbl::
         (* works as comp_app with nargs = n and tailcall cont [Kreturn 0]*)
          Kgetglobal (get_allias !global_env kn)::
          Kappterm(n, n):: [] (* = discard_dead_code [Kreturn 0] *)
     in
     let lbl = Label.create () in
     fun_code := [Ksequence (add_grab n lbl f_cont, !fun_code)];
     Kclosure(lbl, 0)::cont
  in
  fun kn fc reloc args sz cont ->
  if not fc then raise Not_found else
  let nargs = Array.length args in
  if nargs=n then (*if it is a fully applied addition*)
    let (escape, labeled_cont) = make_branch cont in
    let else_lbl = Label.create () in
      comp_args compile_constr reloc args sz
	(Kisconst else_lbl::(make_areconst (n-1) else_lbl
           (*Kaddint31::escape::Klabel else_lbl::Kpush::*)
           (op::escape::Klabel else_lbl::Kpush::
           (* works as comp_app with nargs = n and non-tailcall cont*)
           Kgetglobal (get_allias !global_env kn)::
           Kapply n::labeled_cont)))
  else if nargs=0 then
    code_construct kn cont
  else
    comp_app (fun _ _ _ cont -> code_construct kn cont)
      compile_constr reloc () args sz cont

let int31_escape_before_match fc cont =
  if not fc then
    raise Not_found
  else
    let escape_lbl, labeled_cont = label_code cont in
      (Kisconst escape_lbl)::Kdecompint31::labeled_cont
