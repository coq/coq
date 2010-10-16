open Util
open Names
open Esubst
open Term
open Declarations
open Cbytecodes
open Pre_env

(* *)
open Pp
let pr_id id = str (string_of_id id)


let print_sort = function
  | Prop Pos -> (str "Set")
  | Prop Null -> (str "Prop")
  | Type u -> (str "Type(" ++ Univ.pr_uni u ++ str ")")

let pr_sort_family = function
  | InSet -> (str "Set")
  | InProp -> (str "Prop")
  | InType -> (str "Type")

let pr_name = function
  | Name id -> pr_id id
  | Anonymous -> str "_"

let pr_sp sp = str(string_of_kn sp)
let pr_con sp = str(string_of_label (con_label sp))

let rec pr_constr c = match kind_of_term c with
  | Rel n -> str "#"++int n
  | Meta n -> str "Meta(" ++ int n ++ str ")"
  | Var id -> pr_id id
  | Sort s -> print_sort s
  | Cast (c,_, t) -> hov 1 
      (str"(" ++ pr_constr c ++ cut() ++
       str":" ++ pr_constr t ++ str")")
  | Prod (Name(id),t,c) -> hov 1
      (str"forall " ++ pr_id id ++ str":" ++ pr_constr t ++ str"," ++
       spc() ++ pr_constr c)
  | Prod (Anonymous,t,c) -> hov 0
      (str"(" ++ pr_constr t ++ str " ->" ++ spc() ++
       pr_constr c ++ str")")
  | Lambda (na,t,c) -> hov 1
      (str"fun " ++ pr_name na ++ str":" ++
       pr_constr t ++ str" =>" ++ spc() ++ pr_constr c)
  | LetIn (na,b,t,c) -> hov 0
      (str"let " ++ pr_name na ++ str":=" ++ pr_constr b ++
       str":" ++ brk(1,2) ++ pr_constr t ++ cut() ++
       pr_constr c)
  | App (c,l) ->  hov 1
      (str"(" ++ pr_constr c ++ spc() ++
       prlist_with_sep spc pr_constr (Array.to_list l) ++ str")")
  | Evar (e,l) -> hov 1
      (str"Evar#" ++ int e ++ str"{" ++
       prlist_with_sep spc pr_constr (Array.to_list l) ++str"}")
  | Const c -> (*str (string_of_label (con_label c))*)
      str (string_of_con c)
  | Ind (mind,i) -> str (string_of_label (mind_label mind)) ++ str "_" ++ int i 
  | Construct ((mind,i),j) ->
      str (string_of_label (mind_label mind)) ++ str "_" ++ int i 
	++ str "_" ++ int j
  | Case (ci,p,c,bl) -> v 0
      (hv 0 (str"<"++pr_constr p++str">"++ cut() ++ str"Case " ++
             pr_constr c ++ str"of") ++ cut() ++
       prlist_with_sep (fun _ -> brk(1,2)) pr_constr (Array.to_list bl) ++
      cut() ++ str"end")
  | Fix ((t,i),(lna,tl,bl)) ->
      let fixl = Array.mapi (fun i na -> (na,t.(i),tl.(i),bl.(i))) lna in
      hov 1
        (str"fix " ++ int i ++ spc() ++  str"{" ++
         v 0 (prlist_with_sep spc (fun (na,i,ty,bd) ->
           pr_name na ++ str"/" ++ int i ++ str":" ++ pr_constr ty ++
           cut() ++ str":=" ++ pr_constr bd) (Array.to_list fixl)) ++
         str"}")
  | CoFix(i,(lna,tl,bl)) ->
      let fixl = Array.mapi (fun i na -> (na,tl.(i),bl.(i))) lna in
      hov 1
        (str"cofix " ++ int i ++ spc() ++  str"{" ++
         v 0 (prlist_with_sep spc (fun (na,ty,bd) ->
           pr_name na ++ str":" ++ pr_constr ty ++
           cut() ++ str":=" ++ pr_constr bd) (Array.to_list fixl)) ++
         str"}")
  | NativeInt i -> str (Native.Uint31.to_string  i)
  | NativeArr (t, p) ->
      str "[|" ++ pr_constr t ++ str ":" ++
      prlist_with_sep spc pr_constr (Array.to_list p)++ str "|]"

type annot_sw = {
    asw_ind : inductive;
    asw_ci : case_info;
    asw_reloc : reloc_table
  }
      
type lambda =
  | Lrel          of name * int 
  | Lvar          of identifier
  | Lprod         of lambda * lambda 
  | Llam          of name array * lambda  
  | Lrec          of name * lambda
  | Llet          of name * lambda * lambda
  | Lapp          of lambda * lambda array
  | Lconst        of constant
  | Lprim         of constant option * Native.prim_op * lambda array
  | Lcprim        of constant * Native.caml_prim * lambda array
	(* No check if None *)
  | Lcase         of annot_sw * lambda * lambda * lam_branches 
  | Lareint       of lambda array 
  | Lif           of lambda * lambda * lambda
  | Lfix          of (int array * int) * fix_decl 
  | Lcofix        of int * fix_decl 
  | Lmakeblock    of int * lambda array
  | Lint          of int
  | Lval          of values
  | Lsort         of sorts
  | Lind          of inductive

and lam_branches = lambda array * (name array * lambda) array 
      
and fix_decl =  name array * lambda array * lambda array
      
(** Printing **)
      
let pp_id id = str (string_of_id id)
    
let pp_name = function
  | Name id -> pp_id id
  | Anonymous -> str "_"
	
let pp_names ids =
  prlist_with_sep (fun _ -> brk(1,1)) pp_name (Array.to_list ids)
    
let pp_rel name n = 
  pp_name name ++  str "##" ++ int n



let pp_sort s = 
  match family_of_sort s with
  | InSet -> str "Set"
  | InProp -> str "Prop"
  | InType -> str "Type"
    
let rec pp_lam lam =
  match lam with
  | Lrel (id,n) -> pp_rel id n
  | Lvar id -> pp_id id 
  | Lprod(dom,codom) -> hov 1
	(str "forall(" ++
	   pp_lam dom ++
	   str "," ++ spc() ++
	   pp_lam codom ++
	   str ")")
  | Llam(ids,body) -> hov 1
	(str "(fun " ++
	   pp_names ids ++
	   str " =>" ++
	   spc() ++
	   pp_lam body ++
	   str ")")
  | Lrec(id, body) ->  hov 1
	(str "(rec " ++
	   pp_name id ++
	   str " =>" ++
	   spc() ++
	   pp_lam body ++
	   str ")")
  | Llet(id,def,body) -> hov 0
	(str "let " ++ 
	   pp_name id ++
	   str ":=" ++ 
	   pp_lam def  ++
	   str " in" ++
	   spc() ++
	   pp_lam body)
  | Lapp(f, args) -> hov 1   
	(str "(" ++ pp_lam f ++ spc() ++
	   prlist_with_sep spc pp_lam (Array.to_list args) ++ 
	   str")")
  | Lconst kn -> pr_con kn
  | Lprim(Some kn,op,args) -> hov 1
	(str "(PRIM " ++ pr_con kn ++  spc() ++
	   prlist_with_sep spc pp_lam  (Array.to_list args) ++ 
	   str")")
  | Lprim(None,op,args) ->
      hov 1
	(str "(PRIM_NC " ++ str (Native.prim_to_string op) ++  spc() ++
	   prlist_with_sep spc pp_lam (Array.to_list args) ++ 
	   str")")
  | Lcprim(kn,op,args) -> hov 1
	(str "(CPRIM " ++ pr_con kn ++  spc() ++
	   prlist_with_sep spc pp_lam  (Array.to_list args) ++ 
	   str")")
  | Lcase(annot,t, a, (const, block)) ->
      let ic = ref (-1) in
      let ib = ref 0 in
      v 0 (str"<" ++ pp_lam t ++ str">" ++ cut() ++ 
             str "Case" ++ spc () ++ pp_lam a ++ spc() ++ str "of" ++ cut() ++
	     v 0 
	     ((prlist_with_sep (fun _ -> str "")
		 (fun c ->
		   cut () ++ str "| " ++
		     int (incr ic; !ic) ++ str " => " ++ pp_lam c)
		 (Array.to_list const)) ++
	      (prlist_with_sep (fun _ -> str "")
		 (fun (ids,c) ->
		   cut () ++ str "| " ++
		     int (incr ib; !ib) ++ str " " ++
		     pp_names ids ++ str " => " ++ pp_lam c)
		 (Array.to_list block)))
	     ++ cut() ++ str "end")
  | Lareint a->
      hov 1
	(str "(are_int " ++ (prlist_with_sep spc pp_lam (Array.to_list a))
	   ++ str ")")
  | Lif (t, bt, bf) ->
      v 0 (str "(if " ++ pp_lam t ++ 
	     cut () ++ str "then " ++ pp_lam bt ++ 
	     cut() ++ str "else " ++ pp_lam bf ++ str ")")
  | Lfix((t,i),(lna,tl,bl)) ->
      let fixl = Array.mapi (fun i id -> (id,t.(i),tl.(i),bl.(i))) lna in
      hov 1
        (str"fix " ++ int i ++ spc() ++  str"{" ++
           v 0 
	   (prlist_with_sep spc 
	      (fun (na,i,ty,bd) ->
		pp_name na ++ str"/" ++ int i ++ str":" ++ 
		  pp_lam ty ++ cut() ++ str":=" ++
		  pp_lam bd) (Array.to_list fixl)) ++
         str"}")

  | Lcofix (i,(lna,tl,bl)) ->
      let fixl = Array.mapi (fun i na -> (na,tl.(i),bl.(i))) lna in  
      hov 1
        (str"cofix " ++ int i ++ spc() ++  str"{" ++
           v 0 
	   (prlist_with_sep spc 
	      (fun (na,ty,bd) ->
		pp_name na ++ str":" ++ pp_lam ty ++
		  cut() ++ str":=" ++ pp_lam bd) (Array.to_list fixl)) ++
           str"}")
  | Lmakeblock(tag, args) -> 
      hov 1   
	(str "(makeblock " ++ int tag ++ spc() ++
	   prlist_with_sep spc pp_lam (Array.to_list args) ++ 
	   str")")	
  | Lint i -> int i
  | Lval _ -> str "values"
  | Lsort s -> pp_sort s
  | Lind (mind, i) -> pr_mind mind ++ str"#" ++ int i
  
(*s Constructors *)
  
let mkLapp f args =
  if Array.length args = 0 then f
  else
    match f with
    | Lapp(f', args') -> Lapp (f', Array.append args' args)
    | _ -> Lapp(f, args)
	  
let mkLlam ids body =
  if Array.length ids = 0 then body
  else 
    match body with
  | Llam(ids', body) -> Llam(Array.append ids ids', body)
  | _ -> Llam(ids, body)
  
let decompose_Llam lam =
  match lam with
  | Llam(ids,body) -> ids, body
  | _ -> [||], lam

(*s Operators on substitution *)
let subst_id = ESID 0
let lift = subs_lift 
let liftn = subs_liftn
let cons v subst = subs_cons([|v|], subst)
let shift subst = subs_shft (1, subst)
    
(* A generic map function *)

let map_lam_with_binders g f n lam =
  match lam with
  | Lrel _ | Lvar _  | Lconst _ | Lint _ | Lval _ | Lsort _ | Lind _ -> lam
  | Lprod(dom,codom) -> 
      let dom' = f n dom in
      let codom' = f n codom in
      if dom == dom' && codom == codom' then lam else Lprod(dom',codom')
  | Llam(ids,body) ->
      let body' = f (g (Array.length ids) n) body in
      if body == body' then lam else mkLlam ids body'
  | Lrec(id,body) ->
      let body' = f (g 1 n) body in
      if body == body' then lam else Lrec(id,body')
  | Llet(id,def,body) ->
      let def' = f n def in
      let body' = f (g 1 n) body in
      if body == body' && def == def' then lam else Llet(id,def',body')
  | Lapp(fct,args) ->
      let fct' = f n fct in
      let args' = array_smartmap (f n) args in
      if fct == fct' && args == args' then lam else mkLapp fct' args'
  | Lprim(kn,op,args) ->
      let args' = array_smartmap (f n) args in
      if args == args' then lam else Lprim(kn,op,args')
  | Lcprim(kn,op,args) ->
      let args' = array_smartmap (f n) args in
      if args == args' then lam else Lcprim(kn,op,args')
  | Lcase(annot,t,a,(const,block as br)) ->
      let t' = f n t in
      let a' = f n a in
      let const' = array_smartmap (f n) const in
      let on_b b = 
	let (ids,body) = b in
	let body' = f (g (Array.length ids) n) body in
	if body == body' then b else (ids,body') in
      let block' = array_smartmap on_b block in
      let br' = 
	if const == const' && block == block' then br else (const',block') in
      if t == t' && a == a' && br == br' then lam else Lcase(annot,t',a',br')
  | Lareint a ->
      let a' = array_smartmap (f n) a in
      if a == a' then lam else Lareint a' 
  | Lif(t,bt,bf) ->
      let t' = f n t in
      let bt' = f n bt in
      let bf' = f n bf in
      if t == t' && bt == bt' && bf == bf' then lam else Lif(t',bt',bf')
  | Lfix(init,(ids,ltypes,lbodies)) ->
      let ltypes' = array_smartmap (f n) ltypes in
      let lbodies' = array_smartmap (f (g (Array.length ids) n)) lbodies in
      if ltypes == ltypes' && lbodies == lbodies' then lam
      else Lfix(init,(ids,ltypes',lbodies'))
  | Lcofix(init,(ids,ltypes,lbodies)) ->
      let ltypes' = array_smartmap (f n) ltypes in
      let lbodies' = array_smartmap (f (g (Array.length ids) n)) lbodies in
      if ltypes == ltypes' && lbodies == lbodies' then lam
      else Lcofix(init,(ids,ltypes',lbodies'))
  | Lmakeblock(tag,args) ->
      let args' = array_smartmap (f n) args in
      if args == args' then lam else Lmakeblock(tag,args')


	

 
  

(*s Lift and substitution *)
 

let rec lam_exlift el lam =
  match lam with
  | Lrel(id,i) -> 
      let i' = reloc_rel i el in
      if i == i' then lam else Lrel(id,i')
  | _ -> map_lam_with_binders el_liftn lam_exlift el lam

let lam_lift k lam =
  if k = 0 then lam
  else lam_exlift (ELSHFT (ELID, k)) lam

let lam_subst_rel lam id n subst =
  match expand_rel n subst with
  | Inl(k,v) -> lam_lift k v
  | Inr(n',_) -> 
      if n == n' then lam
      else Lrel(id, n') 

let rec lam_exsubst subst lam =
  match lam with
  | Lrel(id,i) -> lam_subst_rel lam id i subst
  | _ -> map_lam_with_binders liftn lam_exsubst subst lam

let lam_subst subst lam =
  if is_subs_id subst then lam
  else lam_exsubst subst lam

let lam_subst_args subst args =
  if is_subs_id subst then args 
  else array_smartmap (lam_exsubst subst) args
  
(** Simplification of lambda expression *)
      
(* [simplify subst lam] simplify the expression [lam_subst subst lam] *)
(* that is :                                                          *)
(* - Reduce [let] is the definition can be substituted i.e:           *)
(*    - a variable (rel or identifier)                                *)
 (*    - a constant                                                    *)
(*    - a structured constant                                         *)
(*    - a function                                                    *)
(* - Transform beta redex into [let] expression                       *)
(* - Move arguments under [let]                                       *) 
(* Invariant : Terms in [subst] are already simplified and can be     *)
(*             substituted                                            *)
  
let can_subst lam = 
  match lam with
  | Lrel _ | Lvar _ | Lconst _ | Lint _ 
  | Lval _ | Lsort _ | Lind _ | Llam _ -> true
  | _ -> false


let can_merge_if bt bf =
  match bt, bf with
  | Llam(idst,_), Llam(idsf,_) -> true
  | _ -> false

let merge_if t bt bf =
  let (idst,bodyt) = decompose_Llam bt in
  let (idsf,bodyf) = decompose_Llam bf in
  let nt = Array.length idst in
  let nf = Array.length idsf in
  let common,idst,idsf = 
    if nt = nf then idst, [||], [||] 
    else
      if nt < nf then idst,[||], Array.sub idsf nt (nf - nt)
      else idsf, Array.sub idst nf (nt - nf), [||] in
  Llam(common,
       Lif(lam_lift (Array.length common) t, 
	   mkLlam idst bodyt,
	   mkLlam idsf bodyf))


let rec simplify subst lam =
  match lam with
  | Lrel(id,i) -> lam_subst_rel lam id i subst 

  | Llet(id,def,body) ->
      let def' = simplify subst def in
      if can_subst def' then simplify (cons def' subst) body
      else 
	let body' = simplify (lift subst) body in
	if def == def' && body == body' then lam
	else Llet(id,def',body')

  | Lapp(f,args) ->
      begin match simplify_app subst f subst args with
      | Lapp(f',args') when f == f' && args == args' -> lam
      | lam' -> lam'
      end

  | Lif(t,bt,bf) ->
      let t' = simplify subst t in
      let bt' = simplify subst bt in
      let bf' = simplify subst bf in
      if can_merge_if bt' bf' then merge_if t' bt' bf'
      else 
	if t == t' && bt == bt' && bf == bf' then lam
	else Lif(t',bt',bf')
  | _ -> map_lam_with_binders liftn simplify subst lam

and simplify_app substf f substa args =
  match f with
  | Lrel(id, i) ->
      begin match lam_subst_rel f id i substf with
      | Llam(ids, body) ->
	  reduce_lapp 
	    subst_id (Array.to_list ids) body  
	    substa (Array.to_list args)
      | f' -> mkLapp f' (simplify_args substa args)
      end
  | Llam(ids, body) ->
      reduce_lapp substf (Array.to_list ids) body substa (Array.to_list args)
  | Llet(id, def, body) ->
      let def' = simplify substf def in
      if can_subst def' then
	simplify_app (cons def' substf) body substa args
      else 
	Llet(id, def, simplify_app (lift substf) body (shift substa) args)
  | Lapp(f, args') ->
      let args = Array.append 
	  (lam_subst_args substf args') (lam_subst_args substa args) in
      simplify_app substf f subst_id args
  | _ -> mkLapp (simplify substf f) (simplify_args substa args)
  
and simplify_args subst args = array_smartmap (simplify subst) args

and reduce_lapp substf lids body substa largs =
  match lids, largs with
  | id::lids, a::largs ->
      let a = simplify substa a in
      if can_subst a then
	reduce_lapp (cons a substf) lids body substa largs
      else
	let body = reduce_lapp (lift substf) lids body (shift substa) largs in
	Llet(id, a, body)
  | [], [] -> simplify substf body
  | _::_, _ -> 
      Llam(Array.of_list lids,  simplify (liftn (List.length lids) substf) body)
  | [], _::_ -> simplify_app substf body substa (Array.of_list largs)




(* [occurence kind k lam]:
   If [kind] is [true] return [true] if the variable [k] does not appear in 
   [lam], return [false] if the variable appear one time and not
   under a lambda, a fixpoint, a cofixpoint; else raise Not_found.
   If [kind] is [false] return [false] if the variable does not appear in [lam]
   else raise [Not_found]
*)

let rec occurence k kind lam =   
  match lam with
  | Lrel (_,n) -> 
      if n = k then 
	if kind then false else raise Not_found
      else kind
  | Lvar _  | Lconst _  | Lint _ | Lval _ | Lsort _ | Lind _ -> kind
  | Lprod(dom, codom) ->
      occurence k (occurence k kind dom) codom
  | Llam(ids,body) ->
      let _ = occurence (k+Array.length ids) false body in kind
  | Lrec(id,body) ->
      let _ = occurence (k+1) false body in kind
  | Llet(_,def,body) ->
      occurence (k+1) (occurence k kind def) body
  | Lapp(f, args) ->
      occurence_args k (occurence k kind f) args
  | Lprim(_,_, args) | Lcprim(_,_,args) | Lmakeblock(_,args) ->
      occurence_args k kind args
  | Lcase(_,t,a,(const,block)) ->
      let kind = occurence k (occurence k kind t) a in
      let r = ref kind in
      Array.iter (fun c -> r := occurence k kind c  && !r) const;
      Array.iter (fun (ids,c) -> 
	r := occurence (k+Array.length ids) kind c && !r) block;
      !r 
  | Lareint a -> 
      occurence_args k kind a
  | Lif (t, bt, bf) ->
      let kind = occurence k kind t in
      kind && occurence k kind bt && occurence k kind bf
  | Lfix(_,(ids,ltypes,lbodies)) 
  | Lcofix(_,(ids,ltypes,lbodies)) ->
      let kind = occurence_args k kind ltypes in
      let _ = occurence_args (k+Array.length ids) false lbodies in
      kind 

and occurence_args k kind args = 
  Array.fold_left (occurence k) kind args
    
let occur_once lam = 
  try let _ = occurence 1 true lam in true
  with Not_found -> false
      
(* [remove_let lam] remove let expression in [lam] if the variable is *)
(* used at most once time in the body, and does not appear under      *)
(* a lambda or a fix or a cofix                                       *)
      
let rec remove_let subst lam =
  match lam with
  | Lrel(id,i) -> lam_subst_rel lam id i subst 
  | Llet(id,def,body) ->
      let def' = remove_let subst def in
      if occur_once body then remove_let (cons def' subst) body
      else 
	let body' = remove_let (lift subst) body in
	if def == def' && body == body' then lam else Llet(id,def',body')
  | _ -> map_lam_with_binders liftn remove_let subst lam


(*s Translation from [constr] to [lambda] *)

(* Translation of constructor *)

let is_value lc =
  match lc with
  | Lint _ | Lval _ -> true
  | _ -> false

let get_value lc =
  match lc with
  | Lint i -> ((Obj.magic i) : Obj.t)
  | Lval v -> ((Obj.magic v) : Obj.t)
  | _ -> raise Not_found

let mkConst_b0 n = Lint n

let make_args start _end =
  Array.init (start - _end + 1) (fun i -> Lrel (Anonymous, start - i))

(* Translation of constructors *)	
let expense_constructor tag nparams arity =
  let ids = Array.make (nparams + arity) Anonymous in
  if arity = 0 then mkLlam ids (mkConst_b0 tag)
  else
    let args = make_args arity 1 in
    Llam(ids, Lmakeblock (tag, args))

let makeblock tag nparams arity args = 
  let nargs = Array.length args in
  if nparams > 0 || nargs < arity then 
    mkLapp (expense_constructor tag nparams arity) args 
  else 
    (* The constructor is fully applied *)
    if arity = 0 then mkConst_b0 tag
    else 
      if array_for_all is_value args then
	let res = Obj.new_block tag nargs in
	for i = 0 to nargs - 1 do 
	  Obj.set_field res i (get_value args.(i)) 
	done;
	Lval ((Obj.magic res):values)
      else Lmakeblock(tag, args)

let makearray args =
  try
    let p = Array.map get_value args in
    Lval ((Obj.magic (Native.Parray.of_array p)):values)
  with Not_found ->
    let ar = Lmakeblock(0, args) in (* build the ocaml array *)
    let kind = Lmakeblock(0, [|ar|]) in (* Parray.Array *)
    Lmakeblock(0,[|kind|]) (* the reference *)
 (*

  if array_for_all is_value args then
    let p = Array.map get_value args in
    let kind = Obj.new_block 0 1 in (* Parray.Array *)
    Obj.set_field kind 0 ((Obj.magic p):Obj.t);
    let r = Obj.new_block 0 1 in (* reference *)
    Obj.set_field r 0 kind;
    Lval ((Obj.magic r):values)
  else
    let ar = Lmakeblock(0, args) in (* build the ocaml array *)
    let kind = Lmakeblock(0, [|ar|]) in (* Parray.Array *)
    Lmakeblock(0,[|kind|]) (* the reference *)
	
 *)
(* Translation of constants *)

let rec get_allias env kn =
  let tps = (lookup_constant kn env).const_body_code in
  match Cemitcodes.force tps with
  |  Cemitcodes.BCallias kn' -> get_allias env kn'
  | _ -> kn

(* Translation of iterators *)

let isle l1 l2 = Lprim(None, Native.Int31le, [|l1;l2|])
let islt l1 l2 = Lprim(None, Native.Int31lt, [|l1;l2|])
let areint l1 l2 = Lareint [|l1; l2|]
let isint l = Lareint [|l|]
let add31 l1 l2 =Lprim(None, Native.Int31add, [|l1;l2|]) 
let sub31 l1 l2 =Lprim(None, Native.Int31sub, [|l1;l2|]) 
let one31 = mkConst_b0 1

let _f = Name(id_of_string "f")
let _min = Name (id_of_string "min") 
let _max = Name (id_of_string "max") 
let _cont = Name (id_of_string "cont")
let _aux = Name (id_of_string "aux") 
let _i = Name (id_of_string "i") 
let _i' = Name (id_of_string "i'")
let _a = Name (id_of_string "a")

let mkLrel id i = Lrel(id,i) 

let r_f = mkLrel _f
let r_min = mkLrel _min
let r_max = mkLrel _max
let r_cont = mkLrel _cont
let r_aux = mkLrel _aux
let r_i = mkLrel _i
let r_i' = mkLrel _i'
let r_a = mkLrel _a

let lambda_of_iterator kn op args =
  match op with
  | Native.Int31foldi ->
      (* args = [|A;B;f;min;max;cont;extra|] *)
      (* 
         if min <= max then
           (rec aux i a =
              if i < max then f i (aux (i+1)) a
              else f i cont a) 
            min
         else
 	   (fun a => cont a)
       *)
      
      let extra =
	if Array.length args > 6 then
	  Array.sub args 6 (Array.length args - 6)
	else [||] in
      let extra4 = Array.map (lam_lift 4) extra in
      Llet(_cont, args.(5),
      Llet(_max, lam_lift 1 args.(4),
      Llet(_min, lam_lift 2 args.(3),
      Llet(_f, lam_lift 3 args.(2),
      (* f->#1;min->#2;max->#3;cont->#4 *)
      Lif(areint (r_min 2) (r_max 3), (*then*)
  	  Lif(isle (r_min 2) (r_max 3), (*then*)
	      Lapp(Lrec(_aux,
			Llam([|_i;_a|],
			     Lif(islt (r_i 2) (r_max 6),
				 Lapp(r_f 4,
				      [| r_i 2;
					 Llam([|_a|],
					      Lapp(r_aux 4,
						   [| add31 (r_i 3) one31; 
						      r_a 1|]));
					 r_a 1|]),
				 Lapp(r_f 4, [|r_i 2; r_cont 7; r_a 1|])))),
		   Array.append [|r_min 2|] extra4),
	      mkLapp 
		(Llam([|_a|],Lapp(r_cont 5,[|r_a 1|])))
		extra4),
	  Lapp(Lconst kn, 
	       Array.append
		 [|lam_lift 4 args.(0); lam_lift 4 args.(1);
		   r_f 1; r_min 2; r_max 3; r_cont 4|]
		 extra4))))))
	
   | Native.Int31foldi_down -> 
       (* args = [|A;B;f;max;min;cont;extra|] *)
      (* 
         if min <= max then
           (rec aux i a =
              if min < i then f i (aux (i-1)) a
              else f i cont a) 
            max
         else
 	   (fun a => cont a)
       *)
      
      let extra =
	if Array.length args > 6 then
	  Array.sub args 6 (Array.length args - 6)
	else [||] in
      let extra4 = Array.map (lam_lift 4) extra in
      Llet(_cont, args.(5),
      Llet(_max, lam_lift 1 args.(3),
      Llet(_min, lam_lift 2 args.(4),
      Llet(_f, lam_lift 3 args.(2),
      (* f->#1;min->#2;max->#3;cont->#4 *)
      Lif(areint (r_min 2) (r_max 3), (*then*)
  	  Lif(isle (r_min 2) (r_max 3), (*then*)
	      Lapp(Lrec(_aux,
			Llam([|_i;_a|],
			     Lif(islt (r_min 5) (r_i 2),
				 Lapp(r_f 4,
				      [| r_i 2;
					 Llam([|_a|],
					      Lapp(r_aux 4,
						   [| sub31 (r_i 3) one31; 
						      r_a 1|]));
					 r_a 1|]),
				 Lapp(r_f 4, [|r_i 2; r_cont 7; r_a 1|])))),
		   Array.append [|r_max 3|] extra4),
	      mkLapp 
		(Llam([|_a|],Lapp(r_cont 5,[|r_a 1|])))
		extra4),
	  Lapp(Lconst kn, 
	       Array.append
		 [|lam_lift 4 args.(0); lam_lift 4 args.(1);
		   r_f 1; r_max 3; r_min 2; r_cont 4|]
		 extra4))))))





(* Compilation of primitive *)
  
let _h =  Name(id_of_string "f")

let prim kn op args =
  match op with
  | Native.Oprim Native.Int31eqb_correct ->
      let h = Lrel(_h,1) in
      Llet(_h,args.(2),
	Lif(isint h,
            Lint 0 (* constructor eq_refl *),
	    Lapp(Lconst kn, [|lam_lift 1 args.(0);lam_lift 1 args.(1);h|])))
  | Native.Oprim p      -> Lprim(Some kn, p, args)
  | Native.Ocaml_prim p -> Lcprim(kn, p, args)
  | Native.Oiterator p  -> lambda_of_iterator kn p args

let expense_prim kn op arity =
  let ids = Array.make arity Anonymous in
  let args = make_args arity 1 in
  Llam(ids, prim kn op args)

let lambda_of_prim kn op args =
  let (nparams, arity) = Native.arity op in
  let expected = nparams + arity in
  if Array.length args >= expected then prim kn op args
  else mkLapp (expense_prim kn op expected) args

 

(*i Global environment *)


let global_env = ref empty_env 

let set_global_env env = global_env := env

let inline_global kn = 
  match (lookup_constant kn !global_env).const_body with
  | Def csubst -> force csubst
  | _ -> assert false
      
let get_names decl = 
  let decl = Array.of_list decl in
  Array.map fst decl


(* Rel Environment *)
module Vect = 
  struct
    type 'a t = {
	mutable elems : 'a array;
	mutable size : int;
      }

    let make n a = {
      elems = Array.make n a;
      size = 0;
    }

    let length v = v.size

    let extend v =
      if v.size = Array.length v.elems then 
	let new_size = min (2*v.size) Sys.max_array_length in
	if new_size <= v.size then raise (Invalid_argument "Vect.extend");
	let new_elems = Array.make new_size v.elems.(0) in
	Array.blit v.elems 0 new_elems 0 (v.size);
	v.elems <- new_elems

    let push v a = 
      extend v;
      v.elems.(v.size) <- a;
      v.size <- v.size + 1

    let push_pos v a =
      let pos = v.size in
      push v a;
      pos

    let popn v n =
      v.size <- max 0 (v.size - n)

    let pop v = popn v 1
	
    let get v n =
      if v.size <= n then raise 
	  (Invalid_argument "Vect.get:index out of bounds");
      v.elems.(n)

    let get_last v n =
      if v.size <= n then raise 
	  (Invalid_argument "Vect.get:index out of bounds");
      v.elems.(v.size - n - 1)


    let last v =
      if v.size = 0 then raise
	  (Invalid_argument "Vect.last:index out of bounds");
      v.elems.(v.size - 1)

    let clear v = v.size <- 0

    let to_array v = Array.sub v.elems 0 v.size
      
  end

let dummy_lambda = Lrel(Anonymous, 0)

let empty_args = [||]

module Renv = 
  struct

    type constructor_info = tag * int * int (* nparam nrealargs *)

    type t = {
	name_rel : name Vect.t;
	construct_tbl : (constructor, constructor_info) Hashtbl.t;

       }


    let make () = {
      name_rel = Vect.make 16 Anonymous;
      construct_tbl = Hashtbl.create 111
    }

    let push_rel env id = Vect.push env.name_rel id

    let push_rels env ids = 
      Array.iter (push_rel env) ids

    let pop env = Vect.pop env.name_rel
	    
    let popn env n =
      for i = 1 to n do pop env done

    let get env n =
      Lrel (Vect.get_last env.name_rel (n-1), n)

    let get_construct_info env c =
      try Hashtbl.find env.construct_tbl c 
      with Not_found -> 
	let ((mind,j), i) = c in
	let oib = lookup_mind mind !global_env in
	let oip = oib.mind_packets.(j) in
	let tag,arity = oip.mind_reloc_tbl.(i-1) in
	let nparams = oib.mind_nparams in
	let r = (tag, nparams, arity) in
	Hashtbl.add env.construct_tbl c r;
	r
  end

let rec lambda_of_constr env c =
(*  try *)
  match kind_of_term c with
  | Meta _ -> raise (Invalid_argument "Cbytegen.lambda_of_constr: Meta")
  | Evar _ -> raise (Invalid_argument "Cbytegen.lambda_of_constr : Evar")
	
  | Cast (c, _, _) -> lambda_of_constr env c
	
  | Rel i -> Renv.get env i
	
  | Var id -> Lvar id

  | Sort s -> Lsort s
  | Ind ind -> Lind ind
	
  | Prod(id, dom, codom) ->
      let ld = lambda_of_constr env dom in
      Renv.push_rel env id;
      let lc = lambda_of_constr env codom in
      Renv.pop env;
      Lprod(ld,  Llam([|id|], lc))

  | Lambda _ ->
      let params, body = decompose_lam c in
      let ids = get_names (List.rev params) in
      Renv.push_rels env ids;
      let lb = lambda_of_constr env body in
      Renv.popn env (Array.length ids);
      mkLlam ids lb

  | LetIn(id, def, _, body) ->
      let ld = lambda_of_constr env def in
      Renv.push_rel env id;
      let lb = lambda_of_constr env body in
      Renv.pop env;
      Llet(id, ld, lb)

  | App(f, args) -> lambda_of_app env f args

  | Const _ -> lambda_of_app env c empty_args

  | Construct _ ->  lambda_of_app env c empty_args

  | Case(ci,t,a,branches) ->  
      let ind = ci.ci_ind in
      let mib = lookup_mind (fst ind) !global_env in
      let oib = mib.mind_packets.(snd ind) in
      let tbl = oib.mind_reloc_tbl in 
      (* Building info *)
      let annot_sw = {asw_ind = ind; asw_ci = ci; asw_reloc = tbl} in
      (* translation of the argument *)
      let la = lambda_of_constr env a in
      (* translation of the type *)
      let lt = lambda_of_constr env t in
      (* translation of branches *)
      let consts = Array.create oib.mind_nb_constant dummy_lambda in
      let blocks = Array.create oib.mind_nb_args ([||],dummy_lambda) in
      for i = 0 to Array.length tbl - 1 do
	let tag, arity = tbl.(i) in
	let b = lambda_of_constr env branches.(i) in
	if arity = 0 then consts.(tag) <- b
	else 
	  let b = 
	    match b with
	    | Llam(ids, body) when Array.length ids = arity -> (ids, body)
	    | _ -> 
		let ids = Array.make arity Anonymous in
		let args = make_args arity 1 in
		let ll = lam_lift arity b in
		(ids, mkLapp  ll args)
	  in blocks.(tag-1) <- b
      done; 
      Lcase(annot_sw, lt, la, (consts, blocks))
	
  | Fix(rec_init,(names,type_bodies,rec_bodies)) ->
      let ltypes = lambda_of_args env 0 type_bodies in
      Renv.push_rels env names;
      let lbodies = lambda_of_args env 0 rec_bodies in
      Renv.popn env (Array.length names);
      Lfix(rec_init, (names, ltypes, lbodies))
	
  | CoFix(init,(names,type_bodies,rec_bodies)) ->
      let ltypes = lambda_of_args env 0 type_bodies in 
      Renv.push_rels env names;
      let lbodies = lambda_of_args env 0 rec_bodies in
      Renv.popn env (Array.length names);
      Lcofix(init, (names, ltypes, lbodies))
  | NativeInt i -> Lint (Native.Uint31.to_int i)
  | NativeArr(_,p) -> makearray (lambda_of_args env 0 p)


and lambda_of_app env f args =
  match kind_of_term f with
  | Const kn ->
      let kn = get_allias !global_env kn in
      let cb = lookup_constant kn !global_env in
      begin match (lookup_constant kn !global_env).const_body with
      | Primitive op -> lambda_of_prim kn op (lambda_of_args env 0 args)
      | Def csubst when cb.const_inline_code ->
	  lambda_of_app env (force csubst) args
      | Def _ | Opaque _ -> mkLapp (Lconst kn) (lambda_of_args env 0 args)
      end
  | Construct c ->
      let tag, nparams, arity = Renv.get_construct_info env c in
      let nargs = Array.length args in
      if nparams < nargs then
	let args = lambda_of_args env nparams args in
	makeblock tag 0 arity args
      else makeblock tag (nparams - nargs) arity empty_args
  | _ -> 
      let f = lambda_of_constr env f in
      let args = lambda_of_args env 0 args in
      mkLapp f args
	
and lambda_of_args env start args =
  let nargs = Array.length args in
  if start < nargs then
    Array.init (nargs - start) 
      (fun i -> lambda_of_constr env args.(start + i))
  else empty_args
 



(*********************************)


let optimize lam =
  let lam = simplify subst_id lam in
  if Flags.vm_draw_opt () then 
    (msgerrnl (str "Simplify = \n" ++ pp_lam lam);flush_all()); 
  let lam = remove_let subst_id lam in
  if Flags.vm_draw_opt () then 
    (msgerrnl (str "Remove let = \n" ++ pp_lam lam);flush_all()); 
  lam

let print_time = ref false

let time = ref 0.0

let init_time () =
  time :=  Sys.time ()

let get_time () =
  let t = Sys.time () in
  let diff = t -. !time in
  time := t;
  diff


let lambda_of_constr opt c =
  let env = Renv.make () in
  let ids = List.rev_map (fun (id, _, _) -> id) !global_env.env_rel_context in
  Renv.push_rels env (Array.of_list ids);
  let lam = lambda_of_constr env c in
  if Flags.vm_draw_opt () then begin
    (msgerrnl (str "Constr = \n" ++ pr_constr c);flush_all()); 
    (msgerrnl (str "Lambda = \n" ++ pp_lam lam);flush_all()); 
  end;
  if opt then optimize lam else lam 

