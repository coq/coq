(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Pp
open Util
open Names
open Nameops
open Sign
open Term
open Termops
open Declarations
open Inductive
open Inductiveops
open Reductionops
open Environ
open Declare
open Evd
open Pfedit
open Tacred
open Tacmach
open Proof_trees
open Proof_type
open Logic
open Evar_refiner
open Clenv
open Tacticals
open Hipattern
open Coqlib
open Nametab

exception Bound

let rec nb_prod x =
  let rec count n c =
    match kind_of_term c with
        Prod(_,_,t) -> count (n+1) t
      | LetIn(_,a,_,t) -> count n (subst1 a t)
      | Cast(c,_) -> count n c
      | _ -> n
  in count 0 x

(*********************************************)
(*                 Tactics                   *)
(*********************************************)

(****************************************)
(* General functions                    *)
(****************************************)

let get_pairs_from_bindings = 
  let pair_from_binding = function  
    | [(Bindings binds)] -> binds
    | _                  -> error "not a binding list!"
  in 
  List.map pair_from_binding

let string_of_inductive c = 
  try match kind_of_term c with
  | Ind ind_sp -> 
      let (mib,mip) = Global.lookup_inductive ind_sp in 
      string_of_id mip.mind_typename
  | _ -> raise Bound
  with Bound -> error "Bound head variable"

let rec head_constr_bound t l =
  let t = strip_outer_cast(collapse_appl t) in
  match kind_of_term t with
    | Prod (_,_,c2)  -> head_constr_bound c2 l 
    | LetIn (_,_,_,c2) -> head_constr_bound c2 l 
    | App (f,args)  -> 
	head_constr_bound f (Array.fold_right (fun a l -> a::l) args l)
    | Const _        -> t::l
    | Ind _       -> t::l
    | Construct _ -> t::l
    | Var _          -> t::l
    | _                -> raise Bound

let head_constr c = 
  try head_constr_bound c [] with Bound -> error "Bound head variable"

let bad_tactic_args s l =
  raise (RefinerError (BadTacticArgs (s,l)))

(******************************************)
(*           Primitive tactics            *)
(******************************************)

let introduction    = Tacmach.introduction 
let intro_replacing = Tacmach.intro_replacing 
let internal_cut    = Tacmach.internal_cut
let internal_cut_rev = Tacmach.internal_cut_rev
let refine          = Tacmach.refine
let convert_concl   = Tacmach.convert_concl
let convert_hyp     = Tacmach.convert_hyp
let thin            = Tacmach.thin 
let thin_body       = Tacmach.thin_body 
let move_hyp        = Tacmach.move_hyp
let rename_hyp      = Tacmach.rename_hyp

let mutual_fix   = Tacmach.mutual_fix
let fix f n      = mutual_fix [f] [n] []

let fix_noname n =  
  let id = Pfedit.get_current_proof_name () in
  fix id n

let dyn_mutual_fix argsl gl = 
  match argsl with 
    | [Integer n]                          -> fix_noname n gl
    | [Identifier id;Integer n]            -> fix id n gl
    | ((Identifier id)::(Integer n)::lfix) -> 
	let rec decomp lid ln lar = function
          | (Fixexp (id,n,ar)::rest) -> 
	      decomp (id::lid) (n::ln) (ar::lar) rest
          | [] -> (List.rev lid,List.rev ln,List.rev lar)
	  | _  -> bad_tactic_args "mutual_fix" argsl
	in
	let (lid,ln,lar) = decomp [] [] [] lfix in
	mutual_fix (id::lid) (n::ln) (List.map (pf_interp_constr gl) lar) gl
    | l -> bad_tactic_args "mutual_fix" l 

let mutual_cofix = Tacmach.mutual_cofix
let cofix f      =  mutual_cofix [f] []

let cofix_noname n =  
  let id = Pfedit.get_current_proof_name () in
  cofix id n

let dyn_mutual_cofix argsl gl = 
  match argsl with
    | []                       -> cofix_noname gl
    | [(Identifier id)]        -> cofix id gl
    | ((Identifier id)::lcofix) -> 
	let rec decomp lid lar = function 
          | (Cofixexp (id,ar)::rest) -> 
              decomp (id::lid) (ar::lar) rest
          | [] -> (List.rev lid,List.rev lar)
	  |  _ -> bad_tactic_args "mutual_cofix" argsl
	in
	let (lid,lar) = decomp [] [] lcofix in
        mutual_cofix (id::lid) (List.map (pf_interp_constr gl) lar) gl
   | l -> bad_tactic_args "mutual_cofix" l 


(**************************************************************)
(*          Reduction and conversion tactics                  *)
(**************************************************************)

type tactic_reduction = env -> evar_map -> constr -> constr

(* The following two tactics apply an arbitrary
   reduction function either to the conclusion or to a 
   certain hypothesis *)

let reduct_in_concl redfun gl = 
  convert_concl (pf_reduce redfun gl (pf_concl gl)) gl
    
let reduct_in_hyp redfun idref gl =
  let inhyp,id = match idref with
    | InHyp id -> true, id
    | InHypType id -> false, id in
  let (_,c, ty) = pf_get_hyp gl id in
  let redfun' = under_casts (pf_reduce redfun gl) in
  match c with
    | None -> convert_hyp id (redfun' ty) gl
    | Some b ->
	if inhyp then (* Default for defs: reduce in body *)
	  convert_defbody id (redfun' b) gl
	else
	  convert_deftype id (redfun' ty) gl

let reduct_option redfun = function
  | Some id -> reduct_in_hyp   redfun id 
  | None    -> reduct_in_concl redfun 

(* The following tactic determines whether the reduction
   function has to be applied to the conclusion or
   to the hypotheses. *) 

let in_combinator tac1 tac2 = function 
  | [] -> tac1 
  | x  -> (tclMAP tac2 x)
	
let redin_combinator redfun = function 
  | [] ->  reduct_in_concl redfun 
  | x  -> (tclMAP (reduct_in_hyp redfun) x)


(* Now we introduce different instances of the previous tacticals *)
let change_hyp_and_check t env sigma c =
  if is_conv env sigma t c then 
    t
  else 
    errorlabstrm "convert-check-hyp" (str "Not convertible")

let change_concl_and_check t env sigma c =
  if is_conv_leq env sigma t c then 
    t
  else 
    errorlabstrm "convert-check-concl" (str "Not convertible")

let change_in_concl t = reduct_in_concl (change_concl_and_check t)
let change_in_hyp t   = reduct_in_hyp (change_hyp_and_check t)

let change_option t = function
  | Some id -> reduct_in_hyp   (change_hyp_and_check t) id
  | None    -> reduct_in_concl (change_concl_and_check t) 

(* Pour usage interne (le niveau User est pris en compte par dyn_reduce) *)
let red_in_concl        = reduct_in_concl red_product
let red_in_hyp          = reduct_in_hyp   red_product
let red_option          = reduct_option   red_product
let hnf_in_concl        = reduct_in_concl hnf_constr
let hnf_in_hyp          = reduct_in_hyp   hnf_constr
let hnf_option          = reduct_option   hnf_constr
let simpl_in_concl      = reduct_in_concl nf
let simpl_in_hyp        = reduct_in_hyp   nf
let simpl_option        = reduct_option   nf
let normalise_in_concl  = reduct_in_concl compute
let normalise_in_hyp    = reduct_in_hyp   compute
let normalise_option    = reduct_option   compute
let unfold_in_concl loccname   = reduct_in_concl (unfoldn loccname) 
let unfold_in_hyp   loccname   = reduct_in_hyp   (unfoldn loccname) 
let unfold_option   loccname   = reduct_option   (unfoldn loccname) 
let pattern_option l = reduct_option (pattern_occs l)

let dyn_change = function
  | [Constr c; Clause cl] ->
      (fun goal -> 
(*         let c = Astterm.interp_type (project goal) (pf_env goal) com in*)
         in_combinator (change_in_concl c) (change_in_hyp c) cl goal)
  | l -> bad_tactic_args "change" l

(* A function which reduces accordingly to a reduction expression,
   as the command Eval does. *)

let reduce redexp cl goal =
  redin_combinator (reduction_of_redexp redexp) cl goal

let dyn_reduce = function
  | [Redexp redexp; Clause cl] -> (fun goal -> reduce redexp cl goal)
  | l -> bad_tactic_args "reduce" l

(* Unfolding occurrences of a constant *)

let unfold_constr = function 
  | ConstRef sp -> unfold_in_concl [[],Closure.EvalConstRef sp]
  | VarRef id -> unfold_in_concl [[],Closure.EvalVarRef id]
  | _ -> errorlabstrm "unfold_constr" (str "Cannot unfold a non-constant.")

(*******************************************)
(*         Introduction tactics            *)
(*******************************************)

let next_global_ident_from id avoid = 
  let rec next_rec id =
    let id = next_ident_away_from id avoid in
    if not (Declare.is_global id) then
      id
    else  
      next_rec (lift_ident id)
  in 
  next_rec id

let next_global_ident_away id avoid =
  let id  = next_ident_away id avoid in
  if not (Declare.is_global id) then
    id
  else  
    next_global_ident_from (lift_ident id) avoid

let fresh_id avoid id gl =
  next_global_ident_away id (avoid@(pf_ids_of_hyps gl))

let id_of_name_with_default s = function
  | Anonymous -> id_of_string s
  | Name id   -> id

let default_id gl =
  match kind_of_term (strip_outer_cast (pf_concl gl)) with
    | Prod (name,c1,c2) ->
  	(match kind_of_term (pf_whd_betadeltaiota gl (pf_type_of gl c1)) with
	   | Sort (Prop _) -> (id_of_name_with_default "H" name)
	   | Sort (Type _) -> (id_of_name_with_default "X" name)
	   | _                   -> anomaly "Wrong sort")
    | LetIn (name,b,_,_) -> id_of_name_using_hdchar (pf_env gl) b name
    | _ -> raise (RefinerError IntroNeedsProduct)

(* Non primitive introduction tactics are treated by central_intro
   There is possibly renaming, with possibly names to avoid and 
   possibly a move to do after the introduction *)

type intro_name_flag =
  | IntroAvoid of identifier list
  | IntroBasedOn of identifier * identifier list
  | IntroMustBe of identifier

let rec intro_gen name_flag move_flag force_flag gl =
  try
    let id =
      match name_flag with
        | IntroAvoid idl        -> fresh_id idl (default_id gl) gl
        | IntroBasedOn (id,idl) -> fresh_id idl id gl
        | IntroMustBe id        -> 
	    let id' = fresh_id [] id gl in
  	    if id' <> id then error ((string_of_id id)^" is already used");
	    id'
    in
    begin match move_flag with
      | None      -> introduction id gl
      | Some dest -> tclTHEN (introduction id) (move_hyp true id dest) gl
    end
  with RefinerError IntroNeedsProduct as e ->
    if force_flag then
      try
        ((tclTHEN (reduce (Red true) [])
	    (intro_gen name_flag move_flag force_flag)) gl)
      with Redelimination ->
        errorlabstrm "Intro" 
	  (str "No product even after head-reduction")
    else
      raise e

let intro_mustbe_force id = intro_gen (IntroMustBe id) None true
let intro_using id = intro_gen (IntroBasedOn (id,[])) None false
let intro_force force_flag = intro_gen (IntroAvoid []) None force_flag
let intro = intro_force false
let introf = intro_force true

(* For backwards compatibility *)
let central_intro = intro_gen

(**** Multiple introduction tactics ****)

let rec intros_using = function
    []      -> tclIDTAC
  | str::l  -> tclTHEN (intro_using str) (intros_using l)

let intros = tclREPEAT (intro_force false)

let intro_erasing id = tclTHEN (thin [id]) (intro_using id)

let intros_replacing ids gls = 
  let rec introrec = function
    | [] -> tclIDTAC
    | id::tl ->
	(tclTHEN (tclORELSE (intro_replacing id)
		    (tclORELSE (intro_erasing id)   (* ?? *)
                       (intro_using id)))
           (introrec tl))
  in 
  introrec ids gls

(* User-level introduction tactics *)

let dyn_intro = function
  | []              -> intro_gen (IntroAvoid []) None true
  | [Identifier id] -> intro_gen (IntroMustBe id) None true
  |  l -> bad_tactic_args "intro" l

let dyn_intro_move = function
  | [Identifier id2] -> intro_gen (IntroAvoid []) (Some id2) true
  | [Identifier id; Identifier id2] ->
      intro_gen (IntroMustBe id) (Some id2) true
  | l -> bad_tactic_args "intro_move" l

let rec intros_until s g =
  match pf_lookup_name_as_renamed (pf_hyps g) (pf_concl g) s with
    | Some depth -> tclDO depth intro g
    | None -> 
	try
	  ((tclTHEN (reduce (Red true) []) (intros_until s)) g)
	with Redelimination ->
          errorlabstrm "Intros" 
	    (str ("No hypothesis "^(string_of_id s)^" in current goal") ++
	      str " even after head-reduction")

let rec intros_until_n_gen red n g =
  match pf_lookup_index_as_renamed (pf_concl g) n with
    | Some depth -> tclDO depth intro g
    | None ->
      if red then
	try
          ((tclTHEN (reduce (Red true) []) (intros_until_n_gen red n)) g)
	with Redelimination ->
          errorlabstrm "Intros" 
	    (str ("No "^(string_of_int n)) ++
	      str (match n with 1 -> "st" | 2 -> "nd" | _ -> "th") ++
	      str " non dependent hypothesis in current goal" ++
	      str " even after head-reduction")
      else
        errorlabstrm "Intros" (str "No such hypothesis in current goal")

let intros_until_n = intros_until_n_gen true
let intros_until_n_wored = intros_until_n_gen false

let dyn_intros_until = function 
  | [Identifier id] -> intros_until id
  | [Integer n]     -> intros_until_n n
  | l -> bad_tactic_args "Intros until" l

let tactic_try_intros_until tac = function
  | Identifier id ->
      tclTHEN (tclTRY (intros_until id)) (tac id)
  | Integer n ->
      tclTHEN (intros_until_n n)
	(fun gl -> let id,_,_ = pf_last_hyp gl in tac id gl)
  | c -> bad_tactic_args "tactic_try_intros_until" [c]

let hide_ident_or_numarg_tactic s tac =
  let tacfun = function
   | [Identifier id] -> tclTHEN (tclTRY (intros_until id)) (tac id)
   | [Integer n] ->
       tclTHEN (intros_until_n n)
	 (fun gl -> let id,_,_ = pf_last_hyp gl in tac id gl)
   | _ -> assert false in
  add_tactic s tacfun;
  fun id -> vernac_tactic(s,[Identifier id])


(* Obsolete, remplace par intros_unitl_n ?
let intros_do n g = 
  let depth = 
    let rec lookup all nodep c = match kind_of_term c with
      | Prod (name,_,c') -> 
	  (match name with
	     | Name(s')  -> 
		 if dependent (mkRel 1) c' then 
		   lookup (all+1) nodep c'
		 else if nodep = n then 
		   all
                 else 
		   lookup (all+1) (nodep+1) c'
             | Anonymous -> 
		 if nodep=n then all else lookup (all+1) (nodep+1) c')
      | Cast (c,_) -> lookup all nodep c
      | _ -> error "No such hypothesis in current goal"
    in 
    lookup 1 1 (pf_concl g)
  in 
  tclDO depth intro g
*)
let rec intros_move = function
  | [] -> tclIDTAC
  | (hyp,destopt) :: rest ->
      tclTHEN (intro_gen (IntroMustBe hyp) destopt false)
	(intros_move rest)

let dependent_in_decl a (_,c,t) =
  match c with
    | None -> dependent a (body_of_type t)
    | Some body -> dependent a body || dependent a (body_of_type t)

let move_to_rhyp rhyp gl =
  let rec get_lhyp lastfixed depdecls = function
    | [] ->
	(match rhyp with
	   | None -> lastfixed
      	   | Some h -> anomaly ("Hypothesis should occur: "^ (string_of_id h)))
    | (hyp,c,typ) as ht :: rest ->
	if Some hyp = rhyp then 
	  lastfixed
	else if List.exists (occur_var_in_decl (pf_env gl) hyp) depdecls then 
	  get_lhyp lastfixed (ht::depdecls) rest
        else
	  get_lhyp (Some hyp) depdecls rest
  in
  let sign = pf_hyps gl in
  let (hyp,c,typ as decl) = List.hd sign in
  match get_lhyp None [decl] (List.tl sign) with
    | None -> tclIDTAC gl
    | Some hypto -> move_hyp true hyp hypto gl

let rec intros_rmove = function
  | [] -> tclIDTAC
  | (hyp,destopt) :: rest ->
      tclTHENLIST [ introduction hyp;
 		    move_to_rhyp destopt;
		    intros_rmove rest ]

(****************************************************)
(*            Resolution tactics                    *)
(****************************************************)

(*  Refinement tactic: unification with the head of the head normal form
 *  of the type of a term. *)

let apply_type hdcty argl gl =
  refine (applist (mkCast (mkMeta (new_meta()),hdcty),argl)) gl
    
let apply_term hdc argl gl =
  refine (applist (hdc,argl)) gl

let bring_hyps hyps gl = 
  let newcl = List.fold_right mkNamedProd_or_LetIn hyps (pf_concl gl) in
  let f = mkCast (mkMeta (new_meta()),newcl) in
  refine (mkApp (f, instance_from_named_context hyps)) gl

(* Resolution with missing arguments *)


let apply_with_bindings  (c,lbind) gl = 
  let apply = 
    match kind_of_term c with 
      | Lambda _ -> res_pf_cast 
      | _ -> res_pf 
  in 
  let (wc,kONT) = startWalk gl in
  (* The actual type of the theorem. It will be matched against the
  goal. If this fails, then the head constant will be unfolded step by
  step. *)
  let thm_ty0 = (w_type_of wc c) in
  let rec try_apply thm_ty =
    try
      let n = nb_prod thm_ty - nb_prod (pf_concl gl) in
      if n<0 then error "Apply: theorem has not enough premisses.";
      let clause = make_clenv_binding_apply wc n (c,thm_ty) lbind in
      apply kONT clause gl
    with (RefinerError _|UserError _|Failure _) as exn ->
      let red_thm =
        try red_product (w_env wc) (w_Underlying wc) thm_ty
        with (Redelimination | UserError _) -> raise exn in
      try_apply red_thm in
  try try_apply thm_ty0
  with (RefinerError _|UserError _|Failure _) ->
    (* Last chance: if the head is a variable, apply may try
       second order unification *)
    let clause = make_clenv_binding_apply wc (-1) (c,thm_ty0) lbind in 
    apply kONT clause gl


let apply c = apply_with_bindings (c,[])
let apply_com = tactic_com (fun c -> apply_with_bindings (c,[]))

let apply_list = function 
  | c::l -> apply_with_bindings (c,List.map (fun com ->(Com,com)) l)
  | _ -> assert false

(* Resolution with no reduction on the type *)

let apply_without_reduce c gl = 
  let (wc,kONT) = startWalk gl in
  let clause = mk_clenv_type_of wc c in 
  res_pf kONT clause gl

let apply_without_reduce_com = tactic_com  apply_without_reduce

let refinew_scheme kONT clause gl = res_pf kONT clause gl

let dyn_apply l =
  match l with 
    | [Command com; Bindings binds] -> 
        tactic_com_bind_list apply_with_bindings (com,binds)
    | [Constr c; Cbindings binds] -> 
	apply_with_bindings (c,binds)
    | l -> 
	bad_tactic_args "apply" l

(* A useful resolution tactic, equivalent to Cut type_of_c;[Idtac|Apply c] *)

let cut_and_apply c gl =
  let goal_constr = pf_concl gl in 
  match kind_of_term (pf_hnf_constr gl (pf_type_of gl c)) with
    | Prod (_,c1,c2) when not (dependent (mkRel 1) c2) ->
	tclTHENS 
	  (apply_type (mkProd (Anonymous,c2,goal_constr))
	     [mkMeta (new_meta())])
	  [tclIDTAC;apply_term c [mkMeta (new_meta())]] gl
    | _ -> error "Imp_elim needs a non-dependent product"

let dyn_cut_and_apply = function 
  | [Command com] -> tactic_com cut_and_apply com
  | [Constr c]    -> cut_and_apply c
  | l             -> bad_tactic_args "cut_and_apply" l

(**************************)
(*     Cut tactics        *)
(**************************)

let true_cut id c gl =
  match kind_of_term (hnf_type_of gl c) with
    | Sort _ -> internal_cut id c gl
    | _  -> error "Not a proposition or a type"

let true_cut_anon c gl =
  match kind_of_term (hnf_type_of gl c) with
    | Sort s -> 
        let d = match s with Prop _ -> "H" | Type _ -> "X" in
        let id = next_name_away_with_default d Anonymous (pf_ids_of_hyps gl) in
        internal_cut id c gl
    | _  -> error "Not a proposition or a type"

let dyn_true_cut = function
  | [Command com] -> tactic_com_sort true_cut_anon com
  | [Constr  c]   -> true_cut_anon c
  | [Command com; Identifier id] -> tactic_com_sort (true_cut id) com
  | [Constr  c; Identifier id]   -> true_cut id c
  | l             -> bad_tactic_args "true_cut" l

let cut c gl =
  match kind_of_term (hnf_type_of gl c) with
    | Sort _ ->
        let id=next_name_away_with_default "H" Anonymous (pf_ids_of_hyps gl) in
        let t = mkProd (Anonymous, c, pf_concl gl) in
        tclTHENS
          (internal_cut_rev id c)
          [tclTHEN (apply_type t [mkVar id]) (thin [id]);
           tclIDTAC] gl
    | _  -> error "Not a proposition or a type"

let dyn_cut = function
  | [Command com] -> tactic_com_sort cut com
  | [Constr  c]   -> cut c
  | l             -> bad_tactic_args "cut" l

let cut_intro t = (tclTHENS (cut t) [intro;tclIDTAC])
		    
let cut_replacing id t = 
  (tclTHENS (cut t)
     [(tclORELSE (intro_replacing id) 
         (tclORELSE (intro_erasing id) 
            (intro_using id)));
      tclIDTAC])

let cut_in_parallel l = 
  let rec prec = function
    | [] -> tclIDTAC
    | h::t -> (tclTHENS (cut h) ([prec t;tclIDTAC]))
  in 
  prec (List.rev l)

(**************************)
(*   Generalize tactics   *)
(**************************)

let generalize_goal gl c cl =
  let t = pf_type_of gl c in
  match kind_of_term c with
    | Var id -> mkNamedProd id t cl
    | _        -> 
        let cl' = subst_term c cl in 
        if noccurn 1 cl' then 
	  mkProd (Anonymous,t,cl)
          (* On ne se casse pas la tete : on prend pour nom de variable
             la premiere lettre du type, meme si "ci" est une
             constante et qu'on pourrait prendre directement son nom *)
        else 
	  prod_name (Global.env()) (Anonymous, t, cl')

let generalize_dep c gl =
  let env = pf_env gl in
  let sign = pf_hyps gl in
  let init_ids = ids_of_named_context (Global.named_context()) in
  let rec seek toquant d =
    if List.exists (fun (id,_,_) -> occur_var_in_decl env id d) toquant
      or dependent_in_decl c d then 
      d::toquant
    else 
      toquant in
  let toq_rev = Sign.fold_named_context_reverse seek ~init:[] sign in
  let qhyps = List.map (fun (id,_,_) -> id) toq_rev in
  let to_quantify =
    List.fold_left
      (fun sign d -> add_named_decl d sign)
      empty_named_context
      toq_rev in
  let tothin = List.filter (fun id -> not (List.mem id init_ids)) qhyps in
  let tothin' =
    match kind_of_term c with
      | Var id when mem_named_context id sign & not (List.mem id init_ids)
	  -> id::tothin
      | _ -> tothin
  in
  let cl' = it_mkNamedProd_or_LetIn (pf_concl gl) to_quantify in
  let cl'' = generalize_goal gl c cl' in
  let args = List.map mkVar qhyps in
  tclTHEN
    (apply_type cl'' (c::args))
    (thin (List.rev tothin'))
    gl
    
let generalize lconstr gl = 
  let newcl = List.fold_right (generalize_goal gl) lconstr (pf_concl gl) in
  apply_type newcl lconstr gl

let dyn_generalize =
  fun argsl -> generalize (List.map Tacinterp.constr_of_Constr argsl)
      
let dyn_generalize_dep = function
  | [Constr csr] -> generalize_dep csr
  | l -> bad_tactic_args "dyn_generalize_dep" l

(* Faudra-t-il une version avec plusieurs args de generalize_dep ?
Cela peut-être troublant de faire "Generalize Dependent H n" dans
"n:nat; H:n=n |- P(n)" et d'échouer parce que H a disparu après la
généralisation dépendante par n.

let quantify lconstr =
 List.fold_right 
   (fun com tac -> tclTHEN tac (tactic_com generalize_dep c))
   lconstr
   tclIDTAC
*)

(* A dependent cut rule à la sequent calculus
   ------------------------------------------
   Sera simplifiable le jour où il y aura un let in primitif dans constr

   [letin_tac b na c (occ_hyp,occ_ccl) gl] transforms
   [...x1:T1(c),...,x2:T2(c),... |- G(c)] into
   [...x:T;x1:T1(x),...,x2:T2(x),... |- G(x)] if [b] is false or
   [...x:=c:T;x1:T1(x),...,x2:T2(x),... |- G(x)] if [b] is true

   [occ_hyp,occ_ccl] tells which occurrences of [c] have to be substituted;
   if [occ_hyp = []] and [occ_ccl = None] then [c] is substituted
   wherever it occurs, otherwise [c] is substituted only in hyps
   present in [occ_hyps] at the specified occurrences (everywhere if
   the list of occurrences is empty), and in the goal at the specified
   occurrences if [occ_goal] is not [None];

   if name = Anonymous, the name is build from the first letter of the type;

   The tactic first quantify the goal over x1, x2,... then substitute then
   re-intro x1, x2,... at their initial place ([marks] is internally
   used to remember the place of x1, x2, ...: it is the list of hypotheses on
   the left of each x1, ...).
*)

let letin_abstract id c (occ_ccl,occ_hyps) gl =
  let everywhere = (occ_ccl = None) & (occ_hyps = []) in
  let env = pf_env gl in
  let abstract ((depdecls,marks as accu),lhyp) (hyp,_,_ as d) =
    try
      let occ = if everywhere then [] else List.assoc hyp occ_hyps in
      let newdecl = subst_term_occ_decl occ c d in
      if d = newdecl then
	if not everywhere then raise (RefinerError (DoesNotOccurIn (c,hyp)))
	else (accu, Some hyp)
      else 
	let newdecl = subst1_decl (mkVar id) newdecl in
	((newdecl::depdecls,(hyp,lhyp)::marks), lhyp)
    with Not_found -> 
      (accu, Some hyp) 
  in
  let (depdecls,marks),_ =
    fold_named_context_reverse abstract ~init:(([],[]),None) env in
  let occ_ccl = if everywhere then Some [] else occ_ccl in
  let ccl = match occ_ccl with
    | None -> pf_concl gl
    | Some occ -> subst1 (mkVar id) (subst_term_occ occ c (pf_concl gl))
  in
  (depdecls,marks,ccl)

let letin_tac with_eq name c occs gl =
  let x = id_of_name_using_hdchar (Global.env()) (pf_type_of gl c) name in
  let env = pf_env gl in
  let used_ids = ids_of_context env in
  let id =
    if name = Anonymous then next_ident_away x used_ids else
      if not (mem_named_context x (named_context env)) then x else
	error ("The variable "^(string_of_id x)^" is already declared") in
  let (depdecls,marks,ccl)= letin_abstract id c occs gl in 
  let ctxt =
    List.fold_left
      (fun sign d -> add_named_decl d sign)
      empty_named_context
      depdecls in
  let t = pf_type_of gl c in
  let tmpcl = List.fold_right mkNamedProd_or_LetIn depdecls ccl in
  let args = Array.to_list (instance_from_named_context depdecls) in
  let newcl = mkNamedLetIn id c t tmpcl in
  let lastlhyp = if marks=[] then None else snd (List.hd marks) in
  tclTHENLIST
    [ apply_type newcl args;
      thin (List.map (fun (id,_,_) -> id) depdecls);
      intro_gen (IntroMustBe id) lastlhyp false;
      if with_eq then tclIDTAC else thin_body [id];
      intros_move marks ] gl

let check_hypotheses_occurrences_list env occl =
  let rec check acc = function
    | (hyp,_) :: rest -> 
	if List.mem hyp acc then
	  error ("Hypothesis "^(string_of_id hyp)^" occurs twice");
	if not (mem_named_context hyp (named_context env)) then
	  error ("No such hypothesis: " ^ (string_of_id hyp));
	check (hyp::acc) rest
    | [] -> ()
  in check [] occl

let dyn_lettac args gl = match args with
  | [Identifier id; Command com; Letpatterns (o,l)] ->
      check_hypotheses_occurrences_list (pf_env gl) l;
      letin_tac true (Name id) (pf_interp_constr gl com) (o,l) gl
  | [Identifier id; Constr c; Letpatterns (o,l)]    ->
      check_hypotheses_occurrences_list (pf_env gl) l;
      letin_tac true (Name id) c (o,l) gl
  | l -> bad_tactic_args "letin" l

let nowhere = (Some [],[])

let dyn_forward args gl = match args with
  | [Quoted_string s; Command com; Identifier id] ->
      letin_tac (s="KeepBody") (Name id) (pf_interp_constr gl com) nowhere gl
  | [Quoted_string s; Constr c; Identifier id]    ->
      letin_tac (s="KeepBody") (Name id) c nowhere gl
  | [Quoted_string s; Constr c] ->
      letin_tac (s="KeepBody") Anonymous c nowhere gl
  | [Quoted_string s; Command c] ->
      letin_tac (s="KeepBody") Anonymous (pf_interp_constr gl c) nowhere gl
  | l -> bad_tactic_args "forward" l

(********************************************************************)
(*               Exact tactics                                      *)
(********************************************************************)

let exact_check c gl =
  let concl = (pf_concl gl) in
  let ct = pf_type_of gl c in
  if pf_conv_x_leq gl ct concl then  
    refine c gl 
  else 
    error "Not an exact proof"

let exact_no_check = refine

let dyn_exact_no_check cc gl = match cc with
  | [Constr c] -> exact_no_check c gl
  | [Command com] ->
      let evc = (project gl) in
      let concl = (pf_concl gl) in
      let c = Astterm.interp_casted_constr evc (pf_env gl) com concl in
      refine c gl 
  | l -> bad_tactic_args "exact_no_check" l 

let dyn_exact_check cc gl = match cc with
  | [Constr c] -> exact_check c gl
  | [Command com] ->
      let evc = (project gl) in
      let concl = (pf_concl gl) in
      let c = Astterm.interp_casted_constr evc (pf_env gl) com concl in
      refine c gl 
  | l -> bad_tactic_args "exact_check" l 

let (assumption : tactic) = fun gl ->
  let concl =  pf_concl gl in 
  let rec arec = function
    | [] -> error "No such assumption"
    | (id,c,t)::rest -> 
	if pf_conv_x_leq gl (body_of_type t) concl then refine (mkVar id) gl
	else arec rest
  in
  arec (pf_hyps gl)

let dyn_assumption = function
  | [] -> assumption
  | l -> bad_tactic_args "assumption" l
  

(*****************************************************************)
(*          Modification of a local context                      *)
(*****************************************************************)

(* This tactic enables the user to remove hypotheses from the signature.
 * Some care is taken to prevent him from removing variables that are 
 * subsequently used in other hypotheses or in the conclusion of the  
 * goal. *)                                                               

let clear ids gl    = thin ids gl
let clear_one id gl = clear [id] gl
let dyn_clear = function
  | [Clause ids] ->
      let out = function InHyp id -> id | _ -> assert false in
      clear (List.map out ids)
  | l -> bad_tactic_args "clear" l

let clear_body = thin_body
let dyn_clear_body = function
  | [Clause ids] ->
      let out = function InHyp id -> id | _ -> assert false in
      clear_body (List.map out ids)
  | l -> bad_tactic_args "clear_body" l

(* Clears a list of identifiers clauses form the context *)
(*
let clear_clauses clsl =
  clear (List.map 
           (function 
	      | Some id -> id
              | None    -> error "ThinClauses") clsl)
*)
let clear_clauses = clear

(* Clears one identifier clause from the context *)

let clear_clause cls = clear_clauses [cls]


(*   Takes a list of booleans, and introduces all the variables 
 *  quantified in the goal which are associated with a value
 *  true  in the boolean list. *)

let rec intros_clearing = function
  | []          -> tclIDTAC
  | (false::tl) -> tclTHEN intro (intros_clearing tl)
  | (true::tl)  ->
      tclTHENLIST [ intro; onLastHyp clear_clause; intros_clearing tl]

(* Adding new hypotheses  *)

let new_hyp mopt c blist g =
  let (wc,kONT) = startWalk g in
  let clause  = mk_clenv_printable_type_of wc c in
  let clause' = clenv_match_args blist clause in
  let (thd,tstack) = whd_stack (clenv_instance_template clause') in
  let nargs = List.length tstack in
  let cut_pf = 
    applist(thd, 
            match mopt with
	      | Some m -> if m < nargs then list_firstn m tstack else tstack
	      | None   -> tstack)
  in 
  (tclTHENL (tclTHEN (kONT clause.hook)
               (cut (pf_type_of g cut_pf)))
     ((tclORELSE (apply cut_pf) (exact_no_check cut_pf)))) g

let dyn_new_hyp argsl gl =
  match argsl with 
    | [Integer n; Command com; Bindings binds]  ->
	tactic_bind_list 
          (new_hyp (Some n) 
             (pf_interp_constr gl com)) 
          binds gl
    | [Command com; Bindings binds] ->  
	tactic_bind_list 
          (new_hyp None 
             (pf_interp_constr gl com))
          binds gl
    | [Integer n; Constr c; Cbindings binds] ->  
        new_hyp (Some n) c binds gl
    | [Constr c; Cbindings binds] ->  
        new_hyp None c binds gl
    | l -> bad_tactic_args "new_hyp" l 

(* Moving hypotheses *)

let dyn_move = function
  | [Identifier idfrom; Identifier idto] -> move_hyp false idfrom idto
  | l -> bad_tactic_args "move" l 

let dyn_move_dep = function
  | [Identifier idfrom; Identifier idto] -> move_hyp true idfrom idto
  | l -> bad_tactic_args "move_dep" l 

(* Renaming hypotheses *)

let dyn_rename = function
  | [Identifier idfrom; Identifier idto] -> rename_hyp idfrom idto
  | l -> bad_tactic_args "rename" l 

(************************)
(* Introduction tactics *)
(************************)

let constructor_checking_bound  boundopt i lbind gl =
  let cl = pf_concl gl in 
  let (mind,redcl) = pf_reduce_to_quantified_ind gl cl in 
  let nconstr =
    Array.length (snd (Global.lookup_inductive mind)).mind_consnames
  and sigma   = project gl in
  if i=0 then error "The constructors are numbered starting from 1";
  if i > nconstr then error "Not enough constructors";
  begin match boundopt with 
    | Some expctdnum -> 
        if expctdnum <> nconstr then 
	  error "Not the expected number of constructors"
    | None -> ()
  end;
  let cons = mkConstruct (ith_constructor_of_inductive mind i) in
  let apply_tac = apply_with_bindings (cons,lbind) in
  (tclTHENLIST [convert_concl redcl; intros; apply_tac]) gl

let one_constructor i = (constructor_checking_bound None i)

let any_constructor gl = 
  let cl = pf_concl gl in 
  let (mind,redcl) = pf_reduce_to_quantified_ind gl cl in
  let nconstr =
    Array.length (snd (Global.lookup_inductive mind)).mind_consnames
  and sigma   = project gl in
  if nconstr = 0 then error "The type has no constructors";
  tclFIRST (List.map (fun i -> one_constructor i []) 
              (interval 1 nconstr)) gl

(* Try to apply the constructor of the inductive definition followed by 
   a tactic t given as an argument.
   Should be generalize in Constructor (Fun c : I -> tactic)
 *)

let tclConstrThen t gl = 
  let mind = fst (pf_reduce_to_quantified_ind gl (pf_concl gl))
  in let lconstr =
       (snd (Global.lookup_inductive mind)).mind_consnames
  in let nconstr = Array.length lconstr 
  in
  if nconstr = 0 then error "The type has no constructors";
  tclFIRST (List.map (fun i -> (tclTHEN (one_constructor i []) t))
              (interval 1 nconstr)) gl

let dyn_constructor = function 
  | [Integer i; Bindings binds]  -> tactic_bind_list (one_constructor i) binds
  | [Integer i; Cbindings binds] -> (one_constructor i) binds
  | [Tac (tac,_)] -> tclConstrThen tac
  | []                           -> any_constructor 
  | l                            -> bad_tactic_args "constructor" l


let left           = (constructor_checking_bound (Some 2) 1)
let simplest_left  = left  []

let dyn_left = function 
  | [Cbindings binds] -> left binds 
  | [Bindings binds]  -> tactic_bind_list left binds 
  | l                 -> bad_tactic_args "left" l

let right          = (constructor_checking_bound (Some 2) 2)
let simplest_right = right []

let dyn_right  = function 
  | [Cbindings binds]  -> right binds 
  | [Bindings binds]   -> tactic_bind_list right binds 
  | l                  -> bad_tactic_args "right" l


let split          = (constructor_checking_bound (Some 1) 1)
let simplest_split = split []

let dyn_split  = function 
  | [Cbindings binds]  -> split binds 
  | [Bindings binds]   -> tactic_bind_list split binds 
  | l                  -> bad_tactic_args "split" l

(********************************************)
(*       Elimination tactics                *)
(********************************************)


(* kONT : ??
 * wc : ??
 * elimclause : ??
 * inclause : ??
 * gl : the current goal
*)

let last_arg c = match kind_of_term c with
  | App (f,cl) ->  array_last cl
  | _ -> anomaly "last_arg"
	
let elimination_clause_scheme kONT wc elimclause indclause gl = 
  let indmv = 
    (match kind_of_term (last_arg (clenv_template elimclause).rebus) with
       | Meta mv -> mv
       | _  -> errorlabstrm "elimination_clause"
             (str "The type of elimination clause is not well-formed")) 
  in
  let elimclause' = clenv_fchain indmv elimclause indclause in 
  elim_res_pf kONT elimclause' gl

(* cast added otherwise tactics Case (n1,n2) generates (?f x y) and 
 * refine fails *)

let type_clenv_binding wc (c,t) lbind = 
  clenv_instance_template_type (make_clenv_binding wc (c,t) lbind)

(* 
 * Elimination tactic with bindings and using an arbitrary 
 * elimination constant called elimc. This constant should end 
 * with a clause (x:I)(P .. ), where P is a bound variable.
 * The term c is of type t, which is a product ending with a type 
 * matching I, lbindc are the expected terms for c arguments 
 *)

let general_elim (c,lbindc) (elimc,lbindelimc) gl = 
  let (wc,kONT)  = startWalk gl in
  let ct = pf_type_of gl c in
  let t = try snd (pf_reduce_to_quantified_ind gl ct) with UserError _ -> ct in
  let indclause  = make_clenv_binding wc (c,t) lbindc  in
  let elimt      = w_type_of wc elimc in
  let elimclause = make_clenv_binding wc (elimc,elimt) lbindelimc in 
  elimination_clause_scheme kONT wc elimclause indclause gl

(* Elimination tactic with bindings but using the default elimination 
 * constant associated with the type. *)

let default_elim (c,lbindc)  gl = 
  let env = pf_env gl in
  let (ind,t) = reduce_to_quantified_ind env (project gl) (pf_type_of gl c) in
  let s = elimination_sort_of_goal gl in
  let elimc = Indrec.lookup_eliminator ind s in
  general_elim (c,lbindc) (elimc,[]) gl


(* The simplest elimination tactic, with no substitutions at all. *)

let simplest_elim c = default_elim (c,[])

(*
 * A "natural" induction tactic
 * 
  - [H0:T0, ..., Hi:Ti, hyp0:P->I(args), Hi+1:Ti+1, ..., Hn:Tn |-G] is the goal
  - [hyp0] is the induction hypothesis
  - we extract from [args] the variables which are not rigid parameters
    of the inductive type, this is [indvars] (other terms are forgotten);
    [indhyps] are the ones which actually are declared in context
    (done in [find_atomic_param_of_ind])
  - we look for all hyps depending of [hyp0] or one of [indvars]:
    this is [dephyps] of types [deptyps] respectively
  - [statuslist] tells for each hyps in [dephyps] after which other hyp
    fixed in the context they must be moved (when induction is done)
  - [hyp0succ] is the name of the hyp fixed in the context after which to
    move the subterms of [hyp0succ] in the i-th branch where it is supposed
    to be the i-th constructor of the inductive type.

  Strategy: (cf in [induction_from_context])
  - requantify and clear all [dephyps]
  - apply induction on [hyp0]
  - clear [indhyps] and [hyp0]
  - in the i-th subgoal, intro the arguments of the i-th constructor
    of the inductive type after [hyp0succ] (done in
    [induct_discharge]) let the induction hypotheses on top of the
    hyps because they may depend on variables between [hyp0] and the
    top. A counterpart is that the dep hyps programmed to be intro-ed
    on top must now be intro-ed after the induction hypotheses
  - move each of [dephyps] at the right place following the
    [statuslist]

 *)

(* We recompute recargs because we are not sure the elimination lemma
comes from a canonically generated one *)

let rec is_rec_arg env sigma indpath t =
  try
    let (ind_sp,_) = find_mrectype env sigma t in
    path_of_inductive env ind_sp = indpath
  with Induc -> 
    false

let rec recargs indpath env sigma t =
  match kind_of_term (whd_betadeltaiota env sigma t) with
    | Prod (na,t,c2) ->
	(is_rec_arg env sigma indpath t)
	::(recargs indpath (push_rel_assum (na,t) env) sigma c2)
    | _ -> []

let induct_discharge old_style mind statuslists cname destopt avoid ra gl =
  let (lstatus,rstatus) = statuslists in
  let tophyp = ref None in
  let n = List.fold_left (fun n b -> if b then n+1 else n) 0 ra in
  let recvarname, hyprecname, avoid =
    if old_style (* = V6.3 version of Induction on hypotheses *)
    then
      let recvarname =
        if n=1 then 
          cname
        else (* To force renumbering if there is only one *)
          make_ident (string_of_id cname) (Some 1) in
      recvarname, add_prefix "Hrec" recvarname, avoid
    else
      let hyprecname =
        add_prefix "IH"
          (if atompart_of_id cname <> "H" 
           then cname
           else (snd (Global.lookup_inductive mind)).mind_typename) in
      let avoid =
        if n=1 (* Only one recursive argument *)
          or 
          (* Rem: no recursive argument (especially if Destruct) *)
          n=0 (* & atompart_of_id cname <> "H" (* for 7.1 compatibility *)*)
        then avoid
        else
          (* Forbid to use cname, cname0, hyprecname and hyprecname0 *)
          (* in order to get names such as f1, f2, ... *)
          let avoid =
            (make_ident (string_of_id cname) (Some 0)) ::(*here for 7.1 cmpat*)
            (make_ident (string_of_id hyprecname) None) ::
            (make_ident (string_of_id hyprecname) (Some 0)) :: avoid in
          if atompart_of_id cname <> "H" then
            (make_ident (string_of_id cname) None) :: avoid 
          else avoid in
      cname, hyprecname, avoid
  in
  let rec peel_tac = function
    | true :: ra' ->
		 (* For lstatus but _buggy_: if intro_gen renames
		    hyprecname differently (because it already exists
		    in goal, then hypothesis associated to None in
		    lstatus will be moved at a wrong place *)
	if !tophyp=None then
	  tophyp := Some (next_ident_away hyprecname avoid);
        tclTHENLIST
	  [ intro_gen (IntroBasedOn (recvarname,avoid)) destopt false;
	    intro_gen (IntroBasedOn (hyprecname,avoid)) None false;
	    peel_tac ra']
    | false :: ra' ->
	tclTHEN (intro_gen (IntroAvoid avoid) destopt false)
	  (peel_tac ra')
    | [] -> tclIDTAC
  in
  let evaluated_peel_tac = peel_tac ra in (* because side effect on tophyp *)
  let newlstatus = (* if some IH has taken place at the top of hyps *)
    List.map (function (hyp,None) -> (hyp,!tophyp) | x -> x) lstatus
  in 
  tclTHENLIST [ evaluated_peel_tac;
		intros_rmove rstatus;
		intros_move newlstatus ] gl

(* - le recalcul de indtyp à chaque itération de atomize_one est pour ne pas
     s'embêter à regarder si un letin_tac ne fait pas des
     substitutions aussi sur l'argument voisin *)

(* Marche pas... faut prendre en compte l'occurrence précise... *)

let atomize_param_of_ind hyp0 gl =
  let tmptyp0 = pf_get_hyp_typ gl hyp0 in
  let (mind,typ0) = pf_reduce_to_quantified_ind gl tmptyp0 in
  let (mib,mip) = Global.lookup_inductive mind in
  let nparams = mip.mind_nparams in
  let prods, indtyp = decompose_prod typ0 in
  let argl = snd (decompose_app indtyp) in
  let params = list_firstn nparams argl in
  (* le gl est important pour ne pas préévaluer *)
  let rec atomize_one i avoid gl =
    if i<>nparams then
      let tmphyp0 = pf_get_hyp_typ gl hyp0 in
      (* If argl <> [], we expect typ0 not to be quantified, in order to
         avoid bound parameters... then we call pf_reduce_to_atomic_ind *)
      let (_,indtyp) = pf_reduce_to_atomic_ind gl tmptyp0 in
      let argl = snd (decompose_app indtyp) in
      let c = List.nth argl (i-1) in
      match kind_of_term c with
	| Var id when not (List.exists (occur_var (pf_env gl) id) avoid) ->
	    atomize_one (i-1) ((mkVar id)::avoid) gl
	| Var id ->
	    let x = fresh_id [] id gl in
	    tclTHEN
	      (letin_tac true (Name x) (mkVar id) (None,[]))
	      (atomize_one (i-1) ((mkVar x)::avoid)) gl
	| _ ->
	    let id = id_of_name_using_hdchar (Global.env()) (pf_type_of gl c)
		       Anonymous in
	    let x = fresh_id [] id gl in
	    tclTHEN
	      (letin_tac true (Name x) c (None,[]))
	      (atomize_one (i-1) ((mkVar x)::avoid)) gl
    else 
      tclIDTAC gl
  in
  atomize_one (List.length argl) params gl

let find_atomic_param_of_ind mind indtyp =
  let (mib,mip) = Global.lookup_inductive mind in
  let nparams = mip.mind_nparams in
  let argl = snd (decompose_app indtyp) in
  let argv = Array.of_list argl in
  let params = list_firstn nparams argl in
  let indvars = ref Idset.empty in
  for i = nparams to (Array.length argv)-1 do
    match kind_of_term argv.(i) with
      | Var id
          when not (List.exists (occur_var (Global.env()) id) params) -> 
	  indvars := Idset.add id !indvars
      | _ -> ()
  done;
  Idset.elements !indvars

   (* [cook_sign] builds the lists [indhyps] of hyps that must be
   erased, the lists of hyps to be generalize [(hdeps,tdeps)] on the
   goal together with the places [(lstatus,rstatus)] where to re-intro
   them after induction. To know where to re-intro the dep hyp, we
   remember the name of the hypothesis [lhyp] after which (if the dep
   hyp is more recent than [hyp0]) or [rhyp] before which (if older
   than [hyp0]) its equivalent must be moved when the induction has
   been applied. Since computation of dependencies and [rhyp] is from
   more ancient (on the right) to more recent hyp (on the left) but
   the computation of [lhyp] progresses from the other way, [cook_hyp]
   is in two passes (an alternative would have been to write an
   higher-order algorithm). We strongly use references to reduce
   the accumulation of arguments.

   To summarize, the situation looks like this

   Goal(n,x) -| H6:(Q n); x:A; H5:True; H4:(le O n); H3:(P n); H2:True; n:nat
                Left                                                    Right 

   Induction hypothesis is H4 ([hyp0])
   Variable parameters of (le O n) is the singleton list with "n" ([indvars])
   Part of [indvars] really in context is the same ([indhyps])
   The dependent hyps are H3 and H6 ([dephyps])
   For H3 the memorized places are H5 ([lhyp]) and H2 ([rhyp])
    because these names are among the hyp which are fixed through the induction
   For H6 the neighbours are None ([lhyp]) and H5 ([rhyp])
   For H3, because on the right of H4, we remember rhyp (here H2)
   For H6, because on the left of H4, we remember lhyp (here None)
   For H4, we remember lhyp (here H5)

   The right neighbour is then translated into the left neighbour
   because move_hyp tactic needs the name of the hyp _after_ which we
   move the hyp to move.

   But, say in the 2nd subgoal of the hypotheses, the goal will be

   (m:nat)((P m)->(Q m)->(Goal m)) -> (P Sm)->   (Q Sm)->   (Goal Sm)
     ^^^^^^^^^^^^^^^^^^^^^^^^^^^       ^^^^
         both go where H4 was       goes where  goes where
                                      H3 was      H6 was

   We have to intro and move m and the recursive hyp first, but then
   where to move H3 ??? Only the hyp on its right is relevant, but we
   have to translate it into the name of the hyp on the left

   Note: this case where some hyp(s) in [dephyps] has(have) the same
   left neighbour as [hyp0] is the only problematic case with right
   neighbours. For the other cases (e.g. an hyp H1:(R n) between n and H2
   would have posed no problem. But for uniformity, we decided to use
   the right hyp for all hyps on the right of H4.

   Others solutions are welcome *)

(*
type hyp_status = 
let hyps_map
*)

exception Shunt of identifier option

let cook_sign hyp0 indvars env =
  (* First phase from L to R: get [indhyps], [decldep] and [statuslist]
     for the hypotheses before (= more ancient than) hyp0 (see above) *)
  let allindhyps = hyp0::indvars in
  let indhyps = ref [] in
  let decldeps = ref [] in
  let ldeps = ref [] in
  let rstatus = ref [] in
  let lstatus = ref [] in
  let before = ref true in
  let seek_deps env (hyp,_,_ as decl) rhyp =
    if hyp = hyp0 then begin
      before:=false; 
      None (* fake value *)
    end else if List.mem hyp indvars then begin
      indhyps := hyp::!indhyps; 
      rhyp
    end else
      if (List.exists (fun id -> occur_var_in_decl env id decl) allindhyps
	  or List.exists (fun (id,_,_) -> occur_var_in_decl env id decl)
        !decldeps)
      then begin
	decldeps := decl::!decldeps;
	if !before then 
	  rstatus := (hyp,rhyp)::!rstatus
	else 
	  ldeps := hyp::!ldeps; (* status computed in 2nd phase *)
	Some hyp end
      else
	Some hyp
  in
  let _ = fold_named_context seek_deps env ~init:None in
  (* 2nd phase from R to L: get left hyp of [hyp0] and [lhyps] *)
  let compute_lstatus lhyp (hyp,_,_ as d) =
    if hyp = hyp0 then raise (Shunt lhyp);
    if List.mem hyp !ldeps then begin
      lstatus := (hyp,lhyp)::!lstatus;
      lhyp
    end else
      if List.mem hyp !indhyps then lhyp else (Some hyp) 
  in
  try 
    let _ = fold_named_context_reverse compute_lstatus ~init:None env in
    anomaly "hyp0 not found"
  with Shunt lhyp0 ->
    let statuslists = (!lstatus,List.rev !rstatus) in
    (statuslists, lhyp0, !indhyps, !decldeps)


(* Vieille version en une seule passe grace à l'ordre supérieur mais
   trop difficile à comprendre

let cook_sign hyp0 indvars sign =
  let finaldeps = ref ([],[]) in
  let indhyps = ref [] in
  let hyp0succ = ref None in
  let cook_init (hdeps,tdeps) rhyp before =
    finaldeps := (List.rev hdeps, List.rev tdeps);
    (None, []) in
  let cook_hyp compute_rhyp hyp typ ((hdeps,tdeps) as deps) =
    fun rhyp before ->
    match () with
      _ when (List.mem hyp indvars)
 	-> let result = compute_rhyp deps rhyp before in
           indhyps := hyp::!indhyps; result
    | _ when hyp = hyp0
        -> let (lhyp,statl) = compute_rhyp deps rhyp true in
	   hyp0succ := lhyp; (None (* fake value *),statl)
    | _ when (List.exists (fun id -> occur_var id typ) (hyp0::indvars)
           or List.exists (fun id -> occur_var id typ) hdeps)
           -> let deps' = (hyp::hdeps, typ::tdeps) in
              let (lhyp,statl) = compute_rhyp deps' rhyp before in
	      let hyp = if before then lhyp else rhyp in
              (lhyp,(DEPENDENT (before,hyp,hyp))::statl)
    | _ ->
 	let (_,statl) = compute_rhyp deps (Some hyp) before
      	in (Some hyp, statl)
  in let (_,statuslist) = it_sign cook_hyp cook_init sign ([],[]) None false in
     (statuslist, !hyp0succ, !indhyps, !finaldeps)
*)

let induction_tac varname typ (elimc,elimt) gl =
  let c = mkVar varname in
  let (wc,kONT)  = startWalk gl                    in
  let indclause  = make_clenv_binding wc (c,typ) []  in
  let elimclause = make_clenv_binding wc (mkCast (elimc,elimt),elimt) [] in
  elimination_clause_scheme kONT wc elimclause indclause gl

let is_indhyp p n t =
  let c,_ = decompose_app t in 
  match kind_of_term c with
    | Rel k when p < k & k <= p + n -> true
    | _ -> false

(* We check that the eliminator has been build by Coq (usual *)
(* eliminator _ind, _rec or _rect, or eliminator built by Scheme) *)
let compute_elim_signature_and_roughly_check elimt mind =
  let (mib,mip) = Global.lookup_inductive mind in
  let lra = mip.mind_listrec in
  let nconstr = Array.length mip.mind_consnames in
  let _,elimt2 = decompose_prod_n mip.mind_nparams elimt in
  let n = nb_prod elimt2 in
  let npred = n - nconstr - mip.mind_nrealargs - 1 in
  let rec check_branch p c ra = match kind_of_term c, ra with
    | Prod (_,_,c), Declarations.Mrec i :: ra' ->
	(match kind_of_term c with
	   | Prod (_,t,c) when is_indhyp (p+1) npred t ->
	       true::(check_branch (p+2) c ra')
	   | _ -> false::(check_branch (p+1) c ra'))
    | LetIn (_,_,_,c), ra' -> false::(check_branch (p+1) c ra)
    | Prod (_,_,c), _ :: ra -> false::(check_branch (p+1) c ra)
    | _, [] -> []
    | _ ->
	error"Not a recursive eliminator: some constructor argument is lacking"
  in
  let rec check_elim c n =
    if n = nconstr then []
    else match kind_of_term c with
    | Prod (_,t,c) -> (check_branch n t lra.(n)) :: (check_elim c (n+1))
    | _ -> error "Not an eliminator: some constructor case is lacking" in
  let _,elimt3 = decompose_prod_n npred elimt2 in
  check_elim elimt3 0

let induction_from_context isrec style hyp0 gl =
  (*test suivant sans doute inutile car refait par le letin_tac*)
  if List.mem hyp0 (ids_of_named_context (Global.named_context())) then
    errorlabstrm "induction" 
      (str "Cannot generalize a global variable");
  let tmptyp0 =	pf_get_hyp_typ gl hyp0 in
  let env = pf_env gl in
  let (mind,typ0) = pf_reduce_to_quantified_ind gl tmptyp0 in
  let indvars = find_atomic_param_of_ind mind (snd (decompose_prod typ0)) in
  let elimc =
    if isrec then Indrec.lookup_eliminator mind (elimination_sort_of_goal gl)
    else Indrec.make_case_gen env (project gl) mind (elimination_sort_of_goal gl)
  in
  let elimt = pf_type_of gl elimc in
  let (statlists,lhyp0,indhyps,deps) = cook_sign hyp0 indvars env in
  let tmpcl = it_mkNamedProd_or_LetIn (pf_concl gl) deps in
  let lr = compute_elim_signature_and_roughly_check elimt mind in
  let dephyps = List.map (fun (id,_,_) -> id) deps in
  let args =
    List.fold_left
      (fun a (id,b,_) -> if b = None then (mkVar id)::a else a) [] deps in

  (* Magistral effet de bord: si hyp0 a des arguments, ceux d'entre
     eux qui ouvrent de nouveaux buts arrivent en premier dans la
     liste des sous-buts du fait qu'ils sont le plus à gauche dans le
     combinateur engendré par make_case_gen (un "Cases (hyp0 ?) of
     ...")  et on ne peut plus appliquer tclTHENST après; en revanche,
     comme lookup_eliminator renvoie un combinateur de la forme
     "ind_rec ... (hyp0 ?)", les buts correspondant à des arguments de
     hyp0 sont maintenant à la fin et tclTHENS marche !!! *)
  if not isrec && nb_prod typ0 <> 0 && lr <> [] (* passe-droit *) then
    error "Cases analysis on a functional term not implemented";

  tclTHENLIST
    [ apply_type tmpcl args;
      thin dephyps;
      tclTHENST
       	(tclTHEN
	   (induction_tac hyp0 typ0 (elimc,elimt))
	   (thin (hyp0::indhyps)))
       	(List.map
	   (induct_discharge style mind statlists hyp0 lhyp0
              (List.rev dephyps)) lr)
	tclIDTAC ]
    gl

let induction_with_atomization_of_ind_arg isrec hyp0 =
  tclTHEN
    (atomize_param_of_ind hyp0)
    (induction_from_context isrec false hyp0)

let new_induct isrec c gl =
  match kind_of_term c with
    | Var id when not (mem_named_context id (Global.named_context())) ->
	induction_with_atomization_of_ind_arg isrec id gl
    | _        ->
	let x = id_of_name_using_hdchar (Global.env()) (pf_type_of gl c) 
		  Anonymous in
	let id = fresh_id [] x gl in
	tclTHEN
	  (letin_tac true (Name id) c (None,[]))
	  (induction_with_atomization_of_ind_arg isrec id) gl

(*
let new_induct_nodep isrec n =
  tclTHEN (intros_until_n n) (induction_with_atomization_of_ind_arg isrec None)
*)

(* The registered tactic, which calls the default elimination
 * if no elimination constant is provided. *)
	  
let dyn_elim = function
  | [Constr mp; Cbindings mpbinds]  -> 
      default_elim (mp,mpbinds)
  | [Command mp; Bindings mpbinds]  -> 
       tactic_com_bind_list default_elim (mp,mpbinds)
  | [Command mp; Bindings mpbinds; Command elimc; Bindings elimcbinds] ->
      let funpair2funlist f = (function [x;y] -> f x y | _ -> assert false) in
      tactic_com_bind_list_list 
        (funpair2funlist general_elim) 
        [(mp,mpbinds);(elimc,elimcbinds)]
  | [Constr mp; Cbindings mpbinds; Constr elimc; Cbindings elimcbinds] ->
      general_elim (mp,mpbinds) (elimc,elimcbinds)
  | l -> bad_tactic_args "elim" l
	
(* Induction tactics *)

(* This was Induction before 6.3 (induction only in quantified premisses) *)
let raw_induct s = tclTHEN (intros_until s) (tclLAST_HYP simplest_elim)
let raw_induct_nodep n = tclTHEN (intros_until_n n) (tclLAST_HYP simplest_elim)

(* This was Induction in 6.3 (hybrid form) *)
let old_induct s =tclORELSE (raw_induct s) (induction_from_context true true s)
let old_induct_nodep = raw_induct_nodep

(* This is Induction since V7 ("natural" induction both in quantified
   premisses and introduced ones) *)
let dyn_new_induct = function
  | [(Command c)] -> tactic_com (new_induct true) c
  | [(Constr x)]  -> new_induct true x
  (* Identifier apart because id can be quantified in goal and not typable *)
  | [Integer _ | Identifier _ as arg] ->
      tactic_try_intros_until (fun id -> new_induct true (mkVar id)) arg
  | l             -> bad_tactic_args "induct" l

(* This was Induction before 6.3 (induction only in quantified premisses)
let dyn_raw_induct = function 
  | [Identifier x] -> raw_induct x
  | [Integer n]    -> raw_induct_nodep n
  | l              -> bad_tactic_args "raw_induct" l
*)

(* This was Induction in 6.3 (hybrid form) *)
let dyn_old_induct = function
  | [(Identifier n)]  -> old_induct n
  | [Integer n]    -> raw_induct_nodep n
  | l              -> bad_tactic_args "raw_induct" l

(* Case analysis tactics *)

let general_case_analysis (c,lbindc) gl =
  let env = pf_env gl in
  let (mind,_) = pf_reduce_to_quantified_ind gl (pf_type_of gl c) in
  let sigma    = project gl in 
  let sort     = elimination_sort_of_goal gl in
  let elim     = Indrec.make_case_gen env sigma mind sort in 
  general_elim (c,lbindc) (elim,[]) gl
    
let simplest_case c = general_case_analysis (c,[])
			
let dyn_case =function 
  | [Constr mp; Cbindings mpbinds] ->
      general_case_analysis (mp,mpbinds)
  | [Command mp; Bindings mpbinds] ->
      tactic_com_bind_list general_case_analysis (mp,mpbinds)
  | l -> bad_tactic_args "case" l
	

(* Destruction tactics *)

let destruct s       = (tclTHEN (intros_until s) (tclLAST_HYP simplest_case))
let destruct_nodep n = (tclTHEN (intros_until_n n)    (tclLAST_HYP simplest_case))

let dyn_new_destruct = function
  | [(Command c)] -> tactic_com (new_induct false) c
  | [(Constr x)]  -> new_induct false x
  (* Identifier apart because id can be quantified in goal and not typable *)
  | [Integer _ | Identifier _ as arg] ->
      tactic_try_intros_until (fun id -> new_induct false (mkVar id)) arg
  | l             -> bad_tactic_args "induct" l

let dyn_old_destruct = function  
  | [Identifier x] -> destruct x
  | [Integer    n] -> destruct_nodep n 
  | l                -> bad_tactic_args "destruct" l

let dyn_destruct = dyn_old_destruct

(*
 *  Eliminations giving the type instead of the proof.
 * These tactics use the default elimination constant and
 * no substitutions at all. 
 * May be they should be integrated into Elim ...
 *)

let elim_scheme_type elim t gl =
  let (wc,kONT) = startWalk gl in
  let clause = mk_clenv_type_of wc elim in 
  match kind_of_term (last_arg (clenv_template clause).rebus) with
    | Meta mv ->
        let clause' =
	  (* t is inductive, then CUMUL or CONV is irrelevant *)
	  clenv_unify CUMUL t (clenv_instance_type clause mv) clause in
	elim_res_pf kONT clause' gl
    | _ -> anomaly "elim_scheme_type"

let elim_type t gl =
  let (ind,t) = pf_reduce_to_atomic_ind gl t in
  let elimc = Indrec.lookup_eliminator ind (elimination_sort_of_goal gl) in
  elim_scheme_type elimc t gl

let dyn_elim_type = function
  | [Constr c]    -> elim_type c
  | [Command com] -> tactic_com_sort elim_type com
  | l             -> bad_tactic_args "elim_type" l

let case_type t gl =
  let (ind,t) = pf_reduce_to_atomic_ind gl t in
  let env = pf_env gl in
  let elimc = Indrec.make_case_gen env (project gl) ind (elimination_sort_of_goal gl) in 
  elim_scheme_type elimc t gl

let dyn_case_type = function
  | [Constr c]    -> case_type c
  | [Command com] -> tactic_com case_type com
  | l             -> bad_tactic_args "case_type" l


(* Some eliminations frequently used *)

(* These elimination tactics are particularly adapted for sequent
   calculus.  They take a clause as argument, and yield the
   elimination rule if the clause is of the form (Some id) and a
   suitable introduction rule otherwise. They do not depend on 
   the name of the eliminated constant, so they can be also 
   used on ad-hoc disjunctions and conjunctions introduced by
   the user. 
   -- Eduardo Gimenez (11/8/97)

   HH (29/5/99) replaces failures by specific error messages
 *)

let andE id gl =
  let t = pf_get_hyp_typ gl id in
  if is_conjunction (pf_hnf_constr gl t) then 
    (tclTHEN (simplest_elim (mkVar id)) (tclDO 2 intro)) gl
  else 
    errorlabstrm "andE" 
      (str("Tactic andE expects "^(string_of_id id)^" is a conjunction."))

let dAnd cls gl =
  match cls with
    | None    -> simplest_split gl
    | Some id -> andE id  gl

let orE id gl =
  let t = pf_get_hyp_typ gl id in
  if is_disjunction (pf_hnf_constr gl t) then 
    (tclTHEN (simplest_elim (mkVar id)) intro) gl
  else 
    errorlabstrm "orE" 
      (str("Tactic orE expects "^(string_of_id id)^" is a disjunction."))

let dorE b cls gl =
  match cls with 
    | (Some id) -> orE id gl 
    |  None     -> (if b then right else left) [] gl

let impE id gl =
  let t = pf_get_hyp_typ gl id in
  if is_imp_term (pf_hnf_constr gl t) then 
    let (dom, _, rng) = destProd (pf_hnf_constr gl t) in 
    (tclTHENS (cut_intro rng) 
       [tclIDTAC;apply_term (mkVar id) [mkMeta (new_meta())]]) gl
  else 
    errorlabstrm "impE"
      (str("Tactic impE expects "^(string_of_id id)^
	      " is a an implication."))
                        
let dImp cls gl =
  match cls with
    | None    -> intro gl
    | Some id -> impE id gl

(************************************************)
(*  Tactics related with logic connectives      *)
(************************************************)

(* Contradiction *)

let contradiction_on_hyp id gl =
  let hyp = pf_get_hyp_typ gl id in
  if is_empty_type hyp then
    simplest_elim (mkVar id) gl
  else 
    error "Not a contradiction"

(* Absurd *)
let absurd c gls =
  (tclTHENS
     (tclTHEN (elim_type (build_coq_False ())) (cut c)) 
     ([(tclTHENS
          (cut (applist(build_coq_not (),[c]))) 
	  ([(tclTHEN intros
	       ((fun gl ->
		   let ida = pf_nth_hyp_id gl 1
                   and idna = pf_nth_hyp_id gl 2 in
                   exact_no_check (applist(mkVar idna,[mkVar ida])) gl)));
            tclIDTAC]));
       tclIDTAC])) gls

let dyn_absurd = function
  | [Constr c]    -> absurd c
  | [Command com] -> tactic_com_sort absurd com
  | l             -> bad_tactic_args "absurd" l

let contradiction gls = 
  tclTHENLIST [ intros; elim_type (build_coq_False ()); assumption ] gls

let dyn_contradiction = function
  | []  -> contradiction
  | l  -> bad_tactic_args "contradiction" l

(* Relfexivity tactics *)

let reflexivity gl =
  match match_with_equation (pf_concl gl) with
    | None -> error "The conclusion is not a substitutive equation" 
    | Some (hdcncl,args) ->  one_constructor 1 [] gl

let intros_reflexivity  = (tclTHEN intros reflexivity)

let dyn_reflexivity = function
  | []  -> intros_reflexivity
  | _ -> errorlabstrm "Tactics.reflexivity" 
                           (str "Tactic applied to bad arguments!")

(* Symmetry tactics *)

(* This tactic first tries to apply a constant named sym_eq, where eq
   is the name of the equality predicate. If this constant is not
   defined and the conclusion is a=b, it solves the goal doing (Cut
   b=a;Intro H;Case H;Constructor 1) *)

let symmetry gl =
  match match_with_equation (pf_concl gl) with
    | None -> error "The conclusion is not a substitutive equation" 
    | Some (hdcncl,args) ->
        let hdcncls = string_of_inductive hdcncl in
        begin 
	  try 
	    (apply (pf_parse_const gl ("sym_"^hdcncls)) gl)
          with  _ ->
            let symc = match args with 
              | [typ;c1;c2] -> mkApp (hdcncl, [| typ; c2; c1 |])
              | [c1;c2]     -> mkApp (hdcncl, [| c2; c1 |])
	      | _ -> assert false 
	    in 
	    (tclTHENS (cut symc)
               [ tclTHENLIST [ intro;
			       tclLAST_HYP simplest_case;
			       one_constructor 1 [] ];
                 tclIDTAC ]) gl
	end

let intros_symmetry  = (tclTHEN intros symmetry)

let dyn_symmetry = function
  | []  -> intros_symmetry
  | l   -> bad_tactic_args "symmetry" l

(* Transitivity tactics *)

(* This tactic first tries to apply a constant named trans_eq, where eq
   is the name of the equality predicate. If this constant is not
   defined and the conclusion is a=b, it solves the goal doing 
   Cut x1=x2; 
       [Cut x2=x3; [Intros e1 e2; Case e2;Assumption 
                    | Idtac]
       | Idtac]
   --Eduardo (19/8/97)
*)

let transitivity t gl =
  match match_with_equation (pf_concl gl) with
    | None -> error "The conclusion is not a substitutive equation" 
    | Some (hdcncl,args) -> 
        let hdcncls = string_of_inductive hdcncl in
        begin
	  try 
	    apply_list [(pf_parse_const gl ("trans_"^hdcncls));t] gl 
          with  _ -> 
            let eq1 = match args with 
              | [typ;c1;c2] -> mkApp (hdcncl, [| typ; c1; t |])
	      | [c1;c2]     -> mkApp (hdcncl, [| c1; t|])
	      | _ -> assert false 
	    in
            let eq2 = match args with 
              | [typ;c1;c2] -> mkApp (hdcncl, [| typ; t; c2 |])
	      | [c1;c2]     -> mkApp (hdcncl, [| t; c2 |])
	      |  _ -> assert false 
	    in
            (tclTHENS (cut eq2)
	       [tclTHENS (cut eq1)
                  [ tclTHENLIST [ tclDO 2 intro;
				  tclLAST_HYP simplest_case;
				  assumption ];
                    tclIDTAC];
                tclIDTAC])gl
        end 
	
let intros_transitivity  n  = tclTHEN intros (transitivity n)

let dyn_transitivity = function
  | [Constr n]  -> intros_transitivity n
  | [Command n] -> tactic_com intros_transitivity n
  | l           -> bad_tactic_args "transitivity" l

(* tactical to save as name a subproof such that the generalisation of 
   the current goal, abstracted with respect to the local signature, 
   is solved by tac *)

let abstract_subproof name tac gls = 
  let env = Global.env() in
  let current_sign = Global.named_context()
  and global_sign = pf_hyps gls in
  let sign = 
    List.fold_right
      (fun (id,_,_ as d) s -> 
	 if mem_named_context id current_sign then s else add_named_decl d s) 
      global_sign empty_named_context
  in
  let na = next_global_ident_away name (ids_of_named_context global_sign) in
  let concl = 
    List.fold_left (fun t d -> mkNamedProd_or_LetIn d t) (pf_concl gls) sign 
  in
  if occur_existential concl then error "Abstract cannot handle existentials";
  let lemme =
    start_proof na NeverDischarge current_sign concl;
    let _,(const,strength) =
      try
	by (tclCOMPLETE (tclTHEN (tclDO (List.length sign) intro) tac)); 
	let r = cook_proof () in 
	delete_current_proof (); r
      with e when catchable_exception e -> 
	(delete_current_proof(); raise e)
    in   (* Faudrait un peu fonctionnaliser cela *)
    let cd = Safe_typing.ConstantEntry const in
    let sp = Declare.declare_constant na (cd,strength) in
    let newenv = Global.env() in
    Declare.constr_of_reference (ConstRef sp)
  in
  exact_no_check 
    (applist (lemme,
	      List.map mkVar (List.rev (ids_of_named_context sign))))
    gls

let tclABSTRACT name_op tac gls = 
  let s = match name_op with 
    | Some s -> s 
    | None   -> add_suffix (get_current_proof_name ()) "_subproof" 
  in  
  abstract_subproof s tac gls

let dyn_tclABSTRACT = 
  hide_tactic "ABSTRACT"
   (function 
       | [Tac (tac,_)] ->
	   tclABSTRACT None tac
       | [Identifier s; Tac (tac,_)] ->
	   tclABSTRACT (Some s) tac
       | _ -> invalid_arg "tclABSTRACT") 



