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
open Libnames
open Declare
open Evd
open Pfedit
open Tacred
open Rawterm
open Tacmach
open Proof_trees
open Proof_type
open Logic
open Evar_refiner
open Clenv
open Refiner
open Tacticals
open Hipattern
open Coqlib
open Nametab
open Tacexpr

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

(*
let get_pairs_from_bindings = 
  let pair_from_binding = function  
    | [(Bindings binds)] -> binds
    | _                  -> error "not a binding list!"
  in 
  List.map pair_from_binding
*)

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

(*
let bad_tactic_args s l =
  raise (RefinerError (BadTacticArgs (s,l)))
*)

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

(* Moving hypotheses *)
let move_hyp        = Tacmach.move_hyp 

(* Renaming hypotheses *)
let rename_hyp      = Tacmach.rename_hyp

(* Refine as a fixpoint *)
let mutual_fix = Tacmach.mutual_fix

let fix ido n = match ido with
  | None -> mutual_fix (Pfedit.get_current_proof_name ()) n []
  | Some id -> mutual_fix id n []

(* Refine as a cofixpoint *)
let mutual_cofix = Tacmach.mutual_cofix

let cofix = function
  | None -> mutual_cofix (Pfedit.get_current_proof_name ()) []
  | Some id -> mutual_cofix id []

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
    | None -> convert_hyp (id,None,redfun' ty) gl
    | Some b ->
	if inhyp then (* Default for defs: reduce in body *)
	  convert_hyp (id,Some (redfun' b),ty) gl
	else
	  convert_hyp (id,Some b,redfun' ty) gl

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

(* Pour usage interne (le niveau User est pris en compte par reduce) *)
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

let change c = in_combinator (change_in_concl c) (change_in_hyp c)

(* A function which reduces accordingly to a reduction expression,
   as the command Eval does. *)

let reduce redexp cl goal =
  redin_combinator (reduction_of_redexp redexp) cl goal

(* Unfolding occurrences of a constant *)

let unfold_constr = function 
  | ConstRef sp -> unfold_in_concl [[],Closure.EvalConstRef sp]
  | VarRef id -> unfold_in_concl [[],Closure.EvalVarRef id]
  | _ -> errorlabstrm "unfold_constr" (str "Cannot unfold a non-constant.")

(*******************************************)
(*         Introduction tactics            *)
(*******************************************)

let is_section_variable id =
  try let _ = Declare.find_section_variable id in true with Not_found -> false

let next_global_ident_from id avoid = 
  let rec next_rec id =
    let id = next_ident_away_from id avoid in
    if is_section_variable id || not (Declare.is_global id) then
      id
    else  
      next_rec (lift_ident id)
  in 
  next_rec id

let next_global_ident_away id avoid =
  let id  = next_ident_away id avoid in
  if is_section_variable id || not (Declare.is_global id) then
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

let intro_move idopt idopt' = match idopt with
  | None -> intro_gen (IntroAvoid []) idopt' true
  | Some id -> intro_gen (IntroMustBe id) idopt' true

let pf_lookup_hypothesis_as_renamed env ccl = function
  | AnonHyp n -> pf_lookup_index_as_renamed env ccl n
  | NamedHyp id -> pf_lookup_name_as_renamed env ccl id

let pf_lookup_hypothesis_as_renamed_gen red h gl =
  let env = pf_env gl in
  let rec aux ccl =
    match pf_lookup_hypothesis_as_renamed env ccl h with
      | None when red -> aux (reduction_of_redexp (Red true) env Evd.empty ccl)
      | x -> x
  in
  try aux (pf_concl gl)
  with Redelimination -> None

let is_quantified_hypothesis id g =
  match pf_lookup_hypothesis_as_renamed_gen true (NamedHyp id) g with
    | Some _ -> true
    | None -> false

let msg_quantified_hypothesis = function
  | NamedHyp id -> 
      str "hypothesis " ++ pr_id id
  | AnonHyp n ->
      int n ++ str (match n with 1 -> "st" | 2 -> "nd" | _ -> "th") ++
      str " non dependent hypothesis"

let depth_of_quantified_hypothesis red h gl =
  match pf_lookup_hypothesis_as_renamed_gen red h gl with
    | Some depth -> depth
    | None ->
        errorlabstrm "lookup_quantified_hypothesis" 
          (str "No " ++ msg_quantified_hypothesis h ++
	  str " in current goal" ++
	  if red then str " even after head-reduction" else mt ())

let intros_until_gen red h g =
  tclDO (depth_of_quantified_hypothesis red h g) intro g

let intros_until_id id = intros_until_gen true (NamedHyp id)
let intros_until_n_gen red n = intros_until_gen red (AnonHyp n)

let intros_until = intros_until_gen true
let intros_until_n = intros_until_n_gen true
let intros_until_n_wored = intros_until_n_gen false

let try_intros_until tac = function
  | NamedHyp id -> tclTHEN (tclTRY (intros_until_id id)) (tac id)
  | AnonHyp n -> tclTHEN (intros_until_n n) (onLastHyp tac)

let rec intros_move = function
  | [] -> tclIDTAC
  | (hyp,destopt) :: rest ->
      tclTHEN (intro_gen (IntroMustBe hyp) destopt false)
	(intros_move rest)

let dependent_in_decl a (_,c,t) =
  match c with
    | None -> dependent a t
    | Some body -> dependent a body || dependent a t

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

let bring_hyps hyps = 
  if hyps = [] then Refiner.tclIDTAC
  else
    (fun gl ->
      let newcl = List.fold_right mkNamedProd_or_LetIn hyps (pf_concl gl) in
      let f = mkCast (mkMeta (new_meta()),newcl) in
      refine (mkApp (f, instance_from_named_context hyps)) gl)

(* Resolution with missing arguments *)

let apply_with_bindings (c,lbind) gl = 
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


let apply c = apply_with_bindings (c,NoBindings)
let apply_com = tactic_com (fun c -> apply_with_bindings (c,NoBindings))

let apply_list = function 
  | c::l -> apply_with_bindings (c,ImplicitBindings l)
  | _ -> assert false

(* Resolution with no reduction on the type *)

let apply_without_reduce c gl = 
  let (wc,kONT) = startWalk gl in
  let clause = mk_clenv_type_of wc c in 
  res_pf kONT clause gl

let apply_without_reduce_com = tactic_com  apply_without_reduce

let refinew_scheme kONT clause gl = res_pf kONT clause gl

(* A useful resolution tactic which, if c:A->B, transforms |- C into
   |- B -> C and |- A (which is realized by Cut B;[Idtac|Apply c]

   -------------------
   Gamma |- c : A -> B      Gamma |- ?2 : A
   ----------------------------------------
           Gamma |- B                        Gamma |- ?1 : B -> C
           -----------------------------------------------------
                             Gamma |- ? : C
 *)

let cut_and_apply c gl =
  let goal_constr = pf_concl gl in 
  match kind_of_term (pf_hnf_constr gl (pf_type_of gl c)) with
    | Prod (_,c1,c2) when not (dependent (mkRel 1) c2) ->
	tclTHENLAST
	  (apply_type (mkProd (Anonymous,c2,goal_constr)) [mkMeta(new_meta())])
	  (apply_term c [mkMeta (new_meta())]) gl
    | _ -> error "Imp_elim needs a non-dependent product"

(**************************)
(*     Cut tactics        *)
(**************************)

let true_cut idopt c gl =
  match kind_of_term (hnf_type_of gl c) with
    | Sort s -> 
	let id =
	  match idopt with
	  | None -> 
              let d = match s with Prop _ -> "H" | Type _ -> "X" in
              fresh_id [] (id_of_string d) gl
	  | Some id -> id
	in
	internal_cut id c gl
    | _  -> error "Not a proposition or a type"

let cut c gl =
  match kind_of_term (hnf_type_of gl c) with
    | Sort _ ->
        let id=next_name_away_with_default "H" Anonymous (pf_ids_of_hyps gl) in
        let t = mkProd (Anonymous, c, pf_concl gl) in
        tclTHENFIRST
          (internal_cut_rev id c)
          (tclTHEN (apply_type t [mkVar id]) (thin [id]))
          gl
    | _  -> error "Not a proposition or a type"

let cut_intro t = tclTHENFIRST (cut t) intro
		    
let cut_replacing id t = 
  tclTHENFIRST
    (cut t)
    (tclORELSE
      (intro_replacing id) 
      (tclORELSE (intro_erasing id) 
        (intro_using id)))

let cut_in_parallel l = 
  let rec prec = function
    | [] -> tclIDTAC
    | h::t -> tclTHENFIRST (cut h) (prec t)
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

let occurrences_of_hyp id = function
  | None, [] -> (* Everywhere *) Some []
  | _, occ_hyps -> try Some (List.assoc id occ_hyps) with Not_found -> None

let occurrences_of_goal = function
  | None, [] -> (* Everywhere *) Some []
  | Some gocc as x, _ -> x
  | None, _ -> None

let everywhere (occ_ccl,occ_hyps) = (occ_ccl = None) & (occ_hyps = [])

let letin_abstract id c occs gl =
  let env = pf_env gl in
  let compute_dependency _ (hyp,_,_ as d) ctxt =
    let d' =
      try
	match occurrences_of_hyp hyp occs with
	  | None -> raise Not_found
	  | Some occ ->
              let newdecl = subst_term_occ_decl occ c d in
              if d = newdecl then
		if not (everywhere occs)
		then raise (RefinerError (DoesNotOccurIn (c,hyp)))
		else raise Not_found
              else 
		(subst1_decl (mkVar id) newdecl, true)
	with Not_found -> 
	  (d,List.exists
	      (fun ((id,_,_),dep) -> dep && occur_var_in_decl env id d) ctxt)
    in d'::ctxt
  in 
  let ctxt' = fold_named_context compute_dependency env ~init:[] in
  let compute_marks ((depdecls,marks as accu),lhyp) ((hyp,_,_) as d,b) =
    if b then ((d::depdecls,(hyp,lhyp)::marks), lhyp)
    else (accu, Some hyp) in
  let (depdecls,marks),_ = List.fold_left compute_marks (([],[]),None) ctxt' in
  let ccl = match occurrences_of_goal occs with
    | None -> pf_concl gl
    | Some occ -> subst1 (mkVar id) (subst_term_occ occ c (pf_concl gl))
  in
  (depdecls,marks,ccl)

let letin_tac with_eq name c occs gl =
  let x = id_of_name_using_hdchar (Global.env()) (pf_type_of gl c) name in
  let id =
    if name = Anonymous then fresh_id [] x gl else
      if not (mem_named_context x (pf_hyps gl)) then x else
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

let check_hypotheses_occurrences_list env (_,occl) =
  let rec check acc = function
    | (hyp,_) :: rest -> 
	if List.mem hyp acc then
	  error ("Hypothesis "^(string_of_id hyp)^" occurs twice");
	if not (mem_named_context hyp (named_context env)) then
	  error ("No such hypothesis: " ^ (string_of_id hyp));
	check (hyp::acc) rest
    | [] -> ()
  in check [] occl

let nowhere = (Some [],[])

let forward b na c = letin_tac b na c nowhere

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

let exact_proof c gl =
  (* on experimente la synthese d'ise dans exact *)
  let c = Astterm.interp_casted_constr (project gl) (pf_env gl) c (pf_concl gl)
  in refine c gl 

let (assumption : tactic) = fun gl ->
  let concl =  pf_concl gl in 
  let rec arec = function
    | [] -> error "No such assumption"
    | (id,c,t)::rest -> 
	if pf_conv_x_leq gl t concl then refine (mkVar id) gl
	else arec rest
  in
  arec (pf_hyps gl)

(*****************************************************************)
(*          Modification of a local context                      *)
(*****************************************************************)

(* This tactic enables the user to remove hypotheses from the signature.
 * Some care is taken to prevent him from removing variables that are 
 * subsequently used in other hypotheses or in the conclusion of the  
 * goal. *)                                                               

let clear ids gl = (* avant seul dyn_clear n'echouait pas en [] *)
  if ids=[] then tclIDTAC gl else thin ids gl

let clear_body = thin_body

(*   Takes a list of booleans, and introduces all the variables 
 *  quantified in the goal which are associated with a value
 *  true  in the boolean list. *)

let rec intros_clearing = function
  | []          -> tclIDTAC
  | (false::tl) -> tclTHEN intro (intros_clearing tl)
  | (true::tl)  ->
      tclTHENLIST
        [ intro; onLastHyp (fun id -> clear [id]); intros_clearing tl]

(* Adding new hypotheses  *)

let new_hyp mopt c lbind g =
  let (wc,kONT) = startWalk g in
  let clause  = make_clenv_binding wc (c,w_type_of wc c) lbind in
  let (thd,tstack) = whd_stack (clenv_instance_template clause) in
  let nargs = List.length tstack in
  let cut_pf = 
    applist(thd, 
            match mopt with
	      | Some m -> if m < nargs then list_firstn m tstack else tstack
	      | None   -> tstack)
  in 
  (tclTHENLAST (tclTHEN (kONT clause.hook)
               (cut (pf_type_of g cut_pf)))
     ((tclORELSE (apply cut_pf) (exact_no_check cut_pf)))) g

(************************)
(* Introduction tactics *)
(************************)

let constructor_tac boundopt i lbind gl =
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

let one_constructor i = constructor_tac None i

(* Try to apply the constructor of the inductive definition followed by 
   a tactic t given as an argument.
   Should be generalize in Constructor (Fun c : I -> tactic)
 *)

let any_constructor tacopt gl =
  let t = match tacopt with None -> tclIDTAC | Some t -> t in
  let mind = fst (pf_reduce_to_quantified_ind gl (pf_concl gl)) in
  let nconstr =
    Array.length (snd (Global.lookup_inductive mind)).mind_consnames in
  if nconstr = 0 then error "The type has no constructors";
  tclFIRST (List.map (fun i -> tclTHEN (one_constructor i NoBindings) t) 
              (interval 1 nconstr)) gl

let left           = constructor_tac (Some 2) 1
let simplest_left  = left NoBindings

let right          = constructor_tac (Some 2) 2
let simplest_right = right NoBindings

let split          = constructor_tac (Some 1) 1
let simplest_split = split NoBindings

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
	
let elimination_clause_scheme kONT elimclause indclause gl = 
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
  elimination_clause_scheme kONT elimclause indclause gl

(* Elimination tactic with bindings but using the default elimination 
 * constant associated with the type. *)

let find_eliminator c gl =
  let env = pf_env gl in
  let (ind,t) = reduce_to_quantified_ind env (project gl) (pf_type_of gl c) in
  let s = elimination_sort_of_goal gl in
    Indrec.lookup_eliminator ind s 
(*  with Not_found -> 
    let dir, base = repr_path (path_of_inductive env ind) in
    let id = Indrec.make_elimination_ident base s in
    errorlabstrm "default_elim"
      (str "Cannot find the elimination combinator :" ++
         pr_id id ++ spc () ++
	 str "The elimination of the inductive definition :" ++
         pr_id base ++ spc () ++ str "on sort " ++
         spc () ++ print_sort (new_sort_in_family s) ++
	 str " is probably not allowed")
(* lookup_eliminator prints the message *) *)
let default_elim (c,lbindc) gl = 
  general_elim (c,lbindc) (find_eliminator c gl,NoBindings) gl

let elim (c,lbindc) elim gl =
  match elim with
  | Some (elimc,lbindelimc) -> general_elim (c,lbindc) (elimc,lbindelimc) gl
  | None -> general_elim (c,lbindc) (find_eliminator c gl,NoBindings) gl 


(* The simplest elimination tactic, with no substitutions at all. *)

let simplest_elim c = default_elim (c,NoBindings)

(* Elimination in hypothesis *)

let elimination_in_clause_scheme kONT id elimclause indclause =
  let (hypmv,indmv) = 
    match clenv_independent elimclause with
        [k1;k2] -> (k1,k2)
      | _  -> errorlabstrm "elimination_clause"
          (str "The type of elimination clause is not well-formed") in
  let elimclause'  = clenv_fchain indmv elimclause indclause in 
  let hyp = mkVar id in
  let hyp_typ = clenv_type_of elimclause' hyp in
  let hypclause =
    mk_clenv_from_n elimclause'.hook (Some 0) (hyp, hyp_typ) in
  let elimclause'' = clenv_fchain hypmv elimclause' hypclause in  
  let new_hyp_prf  = clenv_instance_template elimclause'' in
  let new_hyp_typ  = clenv_instance_template_type elimclause'' in
  if eq_constr hyp_typ new_hyp_typ then
    errorlabstrm "general_rewrite_in" 
      (str "Nothing to rewrite in " ++ pr_id id);
  tclTHEN
    (kONT elimclause''.hook)
    (tclTHENS
      (cut new_hyp_typ)
      [ (* Try to insert the new hyp at the same place *)
        tclORELSE (intro_replacing id)
          (tclTHEN (clear [id]) (introduction id));
        refine new_hyp_prf])

let general_elim_in id (c,lbindc) (elimc,lbindelimc) gl = 
  let (wc,kONT)  = startWalk gl in
  let ct = pf_type_of gl c in
  let t = try snd (pf_reduce_to_quantified_ind gl ct) with UserError _ -> ct in
  let indclause  = make_clenv_binding wc (c,t) lbindc  in
  let elimt      = w_type_of wc elimc in
  let elimclause = make_clenv_binding wc (elimc,elimt) lbindelimc in 
  elimination_in_clause_scheme kONT id elimclause indclause gl

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

let check_unused_names names =
  if names <> [] & Options.is_verbose () then
    let s,are = if List.tl names = [] then " "," is" else "s "," are" in
    let names = String.concat " " (List.map string_of_id names) in
    warning ("Name"^s^names^are^" unused")

(* We recompute recargs because we are not sure the elimination lemma
comes from a canonically generated one *)
(* dead code ?
let rec is_rec_arg env sigma indpath t =
  try
    let (ind_sp,_) = find_mrectype env sigma t in
    path_of_inductive env ind_sp = indpath
  with Not_found -> false

let rec recargs indpath env sigma t =
  match kind_of_term (whd_betadeltaiota env sigma t) with
    | Prod (na,t,c2) ->
	(is_rec_arg env sigma indpath t)
	::(recargs indpath (push_rel_assum (na,t) env) sigma c2)
    | _ -> []
*)
let induct_discharge old_style mind statuslists cname destopt avoid ra names gl
  =
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
  let rec peel_tac ra names gl = match ra with
    | true :: ra' ->
		 (* For lstatus but _buggy_: if intro_gen renames
		    hyprecname differently (because it already exists
		    in goal, then hypothesis associated to None in
		    lstatus will be moved at a wrong place *)
        let recvar,hyprec,names = match names with
          | [] ->
              next_ident_away recvarname avoid,
              next_ident_away hyprecname avoid,
              []
          | [id] ->
              id, next_ident_away (add_prefix "IH" id) avoid, []
          | id1::id2::names -> (id1,id2,names) in
	if !tophyp=None then tophyp := Some hyprec;
        tclTHENLIST
	  [ intro_gen (IntroMustBe (recvar)) destopt false;
	    intro_gen (IntroMustBe (hyprec)) None false;
	    peel_tac ra' names ] gl
    | false :: ra' ->
        let introstyle,names = match names with
          | [] -> IntroAvoid avoid, []
          | id::names -> IntroMustBe id,names in
	tclTHEN (intro_gen introstyle destopt false)
	  (peel_tac ra' names) gl
    | [] ->
        check_unused_names names;
        tclIDTAC gl
  in
  let intros_move lstatus =
    let newlstatus = (* if some IH has taken place at the top of hyps *)
      List.map (function (hyp,None) -> (hyp,!tophyp) | x -> x) lstatus in
    intros_move newlstatus
  in 
  tclTHENLIST [ peel_tac ra names;
		intros_rmove rstatus;
		intros_move lstatus ] gl

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

let induction_tac varname typ (elimc,elimt,lbindelimc) gl =
  let c = mkVar varname in
  let (wc,kONT)  = startWalk gl                    in
  let indclause  = make_clenv_binding wc (c,typ) NoBindings  in
  let elimclause =
    make_clenv_binding wc (mkCast (elimc,elimt),elimt) lbindelimc in
  elimination_clause_scheme kONT elimclause indclause gl

let compute_induction_names n names =
  let names = if names = [] then Array.make n [] else Array.of_list names in
  if Array.length names <> n then
    errorlabstrm "induction_from_context"
      (str "Expect " ++ int n ++ str " lists of names");
  names

let is_indhyp p n t =
  let c,_ = decompose_app t in 
  match kind_of_term c with
    | Rel k when p < k & k <= p + n -> true
    | _ -> false

(* We check that the eliminator has been build by Coq (usual *)
(* eliminator _ind, _rec or _rect, or eliminator built by Scheme) *)
let compute_elim_signature_and_roughly_check elimt mind =
  let (mib,mip) = Global.lookup_inductive mind in
  let lra = dest_subterms mip.mind_recargs in
  let nconstr = Array.length mip.mind_consnames in
  let _,elimt2 = decompose_prod_n mip.mind_nparams elimt in
  let n = nb_prod elimt2 in
  let npred = n - nconstr - mip.mind_nrealargs - 1 in
  let rec check_branch p c ra = match kind_of_term c, ra with
    | Prod (_,_,c), r :: ra' ->
	(match dest_recarg r, kind_of_term c with
	   | Mrec i, Prod (_,t,c) when is_indhyp (p+1) npred t ->
	       true::(check_branch (p+2) c ra')
	   | _ -> false::(check_branch (p+1) c ra'))
    | LetIn (_,_,_,c), ra' -> false::(check_branch (p+1) c ra)
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
  Array.of_list (check_elim elimt3 0)

let induction_from_context isrec style elim hyp0 names gl =
  (*test suivant sans doute inutile car refait par le letin_tac*)
  if List.mem hyp0 (ids_of_named_context (Global.named_context())) then
    errorlabstrm "induction" 
      (str "Cannot generalize a global variable");
  let tmptyp0 =	pf_get_hyp_typ gl hyp0 in
  let env = pf_env gl in
  let (mind,typ0) = pf_reduce_to_quantified_ind gl tmptyp0 in
  let elimc,lbindelimc = match elim with
    | None ->
	let s = elimination_sort_of_goal gl in
	(if isrec then Indrec.lookup_eliminator mind s
	else Indrec.make_case_gen env (project gl) mind s),
	NoBindings
    | Some elim ->
	(* Not really robust: no control on the form of the combinator *)
	elim in
  let elimt = pf_type_of gl elimc in
  let indvars = find_atomic_param_of_ind mind (snd (decompose_prod typ0)) in
  let (statlists,lhyp0,indhyps,deps) = cook_sign hyp0 indvars env in
  let tmpcl = it_mkNamedProd_or_LetIn (pf_concl gl) deps in
  let lr = compute_elim_signature_and_roughly_check elimt mind in
  let names = compute_induction_names (Array.length lr) names in
  let dephyps = List.map (fun (id,_,_) -> id) deps in
  let args =
    List.fold_left
      (fun a (id,b,_) -> if b = None then (mkVar id)::a else a) [] deps in

  (* Magistral effet de bord: si hyp0 a des arguments, ceux d'entre
     eux qui ouvrent de nouveaux buts arrivent en premier dans la
     liste des sous-buts du fait qu'ils sont le plus à gauche dans le
     combinateur engendré par make_case_gen (un "Cases (hyp0 ?) of
     ...")  et on ne peut plus appliquer tclTHENSI après; en revanche,
     comme lookup_eliminator renvoie un combinateur de la forme
     "ind_rec ... (hyp0 ?)", les buts correspondant à des arguments de
     hyp0 sont maintenant à la fin et tclTHENSI marche !!! *)
(*
  if not isrec && nb_prod typ0 <> 0 && lr <> [] (* passe-droit *) then
    error "Cases analysis on a functional term not implemented";
*)
  tclTHENLIST
    [ apply_type tmpcl args;
      thin dephyps;
      (if isrec then tclTHENFIRSTn else tclTHENLASTn)
       	(tclTHEN
	   (induction_tac hyp0 typ0 (elimc,elimt,lbindelimc))
	   (thin (hyp0::indhyps)))
       	(array_map2
	   (induct_discharge style mind statlists hyp0 lhyp0
              (List.rev dephyps)) lr names)
    ]
    gl

let induction_with_atomization_of_ind_arg isrec elim names hyp0 =
  tclTHEN
    (atomize_param_of_ind hyp0)
    (induction_from_context isrec false elim hyp0 names)

(* This is Induction since V7 ("natural" induction both in quantified
   premisses and introduced ones) *)
let new_induct_gen isrec elim names c gl =
  match kind_of_term c with
    | Var id when not (mem_named_context id (Global.named_context())) ->
	induction_with_atomization_of_ind_arg isrec elim names id gl
    | _        ->
	let x = id_of_name_using_hdchar (Global.env()) (pf_type_of gl c) 
		  Anonymous in
	let id = fresh_id [] x gl in
	tclTHEN
	  (letin_tac true (Name id) c (None,[]))
	  (induction_with_atomization_of_ind_arg isrec elim names id) gl

let new_induct_destruct isrec c elim names = match c with
  | ElimOnConstr c -> new_induct_gen isrec elim names c
  | ElimOnAnonHyp n ->
      tclTHEN (intros_until_n n)
        (tclLAST_HYP (new_induct_gen isrec elim names))
  (* Identifier apart because id can be quantified in goal and not typable *)
  | ElimOnIdent (_,id) ->
      tclTHEN (tclTRY (intros_until_id id))
        (new_induct_gen isrec elim names (mkVar id))

let new_induct = new_induct_destruct true
let new_destruct = new_induct_destruct false

(* The registered tactic, which calls the default elimination
 * if no elimination constant is provided. *)
	
(* Induction tactics *)

(* This was Induction before 6.3 (induction only in quantified premisses) *)
let raw_induct s = tclTHEN (intros_until_id s) (tclLAST_HYP simplest_elim)
let raw_induct_nodep n = tclTHEN (intros_until_n n) (tclLAST_HYP simplest_elim)

(* This was Induction in 6.3 (hybrid form) *)
let old_induct_id s =
  tclORELSE (raw_induct s) (induction_from_context true true None s [])
let old_induct_nodep = raw_induct_nodep

let old_induct = function
  | NamedHyp id -> old_induct_id id
  | AnonHyp n -> old_induct_nodep n

(* Case analysis tactics *)

let general_case_analysis (c,lbindc) gl =
  let env = pf_env gl in
  let (mind,_) = pf_reduce_to_quantified_ind gl (pf_type_of gl c) in
  let sigma    = project gl in 
  let sort     = elimination_sort_of_goal gl in
  let case = if occur_term c (pf_concl gl) then Indrec.make_case_dep
  else Indrec.make_case_gen in
  let elim     = case env sigma mind sort in 
  general_elim (c,lbindc) (elim,NoBindings) gl
    
let simplest_case c = general_case_analysis (c,NoBindings)

(* Destruction tactics *)

let old_destruct_id s    =
  (tclTHEN (intros_until_id s) (tclLAST_HYP simplest_case))
let old_destruct_nodep n =
  (tclTHEN (intros_until_n n)    (tclLAST_HYP simplest_case))

let old_destruct = function
  | NamedHyp id -> old_destruct_id id
  | AnonHyp n -> old_destruct_nodep n

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
	  clenv_unify true CUMUL t (clenv_instance_type clause mv) clause in
	elim_res_pf kONT clause' gl
    | _ -> anomaly "elim_scheme_type"

let elim_type t gl =
  let (ind,t) = pf_reduce_to_atomic_ind gl t in
  let elimc = Indrec.lookup_eliminator ind (elimination_sort_of_goal gl) in
  elim_scheme_type elimc t gl

let case_type t gl =
  let (ind,t) = pf_reduce_to_atomic_ind gl t in
  let env = pf_env gl in
  let elimc = Indrec.make_case_gen env (project gl) ind (elimination_sort_of_goal gl) in 
  elim_scheme_type elimc t gl


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
    |  None     -> (if b then right else left) NoBindings gl

let impE id gl =
  let t = pf_get_hyp_typ gl id in
  if is_imp_term (pf_hnf_constr gl t) then 
    let (dom, _, rng) = destProd (pf_hnf_constr gl t) in 
    tclTHENLAST
      (cut_intro rng) 
      (apply_term (mkVar id) [mkMeta (new_meta())]) gl
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

(* Reflexivity tactics *)

let reflexivity gl =
  match match_with_equation (pf_concl gl) with
    | None -> error "The conclusion is not a substitutive equation" 
    | Some (hdcncl,args) ->  one_constructor 1 NoBindings gl

let intros_reflexivity  = (tclTHEN intros reflexivity)

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
	    tclTHENLAST (cut symc)
              (tclTHENLIST 
		[ intro;
		  tclLAST_HYP simplest_case;
		  one_constructor 1 NoBindings ])
	      gl
	end

let intros_symmetry  = (tclTHEN intros symmetry)

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
            tclTHENFIRST (cut eq2)
	      (tclTHENFIRST (cut eq1)
                (tclTHENLIST
		  [ tclDO 2 intro;
		    tclLAST_HYP simplest_case;
		    assumption ])) gl
        end 
	
let intros_transitivity  n  = tclTHEN intros (transitivity n)

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
    start_proof na (false,NeverDischarge) current_sign concl (fun _ _ -> ());
    let _,(const,(_,strength),_) =
      try
	by (tclCOMPLETE (tclTHEN (tclDO (List.length sign) intro) tac)); 
	let r = cook_proof () in 
	delete_current_proof (); r
      with e when catchable_exception e -> 
	(delete_current_proof(); raise e)
    in   (* Faudrait un peu fonctionnaliser cela *)
    let cd = Entries.DefinitionEntry const in
    let sp = Declare.declare_constant na (cd,strength) in
    let newenv = Global.env() in
    Declare.constr_of_reference (ConstRef (snd sp))
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
