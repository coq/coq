
open Util
open Names
open Generic
open Term
open Declarations
open Inductive
open Environ
open Sign
open Reduction
open Typeops
open Type_errors

open Rawterm
open Retyping
open Pretype_errors
open Evarutil
open Evarconv

(*********************************************************************)
(* A) Typing old cases                                               *)
(* This was previously in Indrec but creates existential holes       *)

let mkExistential isevars env =
  new_isevar isevars env (mkCast dummy_sort dummy_sort) CCI

let norec_branch_scheme env isevars cstr =
  prod_it (mkExistential isevars env) cstr.cs_args 

let lift_args l = list_map_i (fun i (name,c) -> (name,liftn 1 i c)) 1 l

let rec_branch_scheme env isevars ((sp,j),_) recargs cstr = 
  let rec crec (args,recargs) = 
    match args, recargs with 
      | (name,c)::rea,(ra::reca) -> 
          DOP2(Prod,c,DLAM(name,
	       match ra with 
		 | Mrec k when k=j -> 
		     mkArrow (mkExistential isevars env)
		       (crec (lift_args rea,reca))
                 | _ -> crec (rea,reca)))
      | [],[] -> mkExistential isevars env
      | _ -> anomaly "rec_branch_scheme"
  in 
  crec (List.rev cstr.cs_args,recargs) 
    
let branch_scheme env isevars isrec (IndFamily (mis,params) as indf) =
  let cstrs = get_constructors indf in 
  if isrec then
    array_map2
      (rec_branch_scheme env isevars (mis_inductive mis))
      (mis_recarg mis) cstrs
  else 
    Array.map (norec_branch_scheme env isevars) cstrs

(***************************************************)
(* Building ML like case expressions without types *)

let concl_n env sigma = 
  let rec decrec m c = if m = 0 then c else 
    match whd_betadeltaiota env sigma c with
      | DOP2(Prod,_,DLAM(n,c_0)) -> decrec (m-1) c_0
      | _                        -> failwith "Typing.concl_n"
  in 
  decrec

let count_rec_arg j = 
  let rec crec i = function 
    | [] -> i 
    | (Mrec k::l) -> crec (if k=j then (i+1) else i) l
    | (_::l) -> crec i l
  in 
  crec 0

(* Used in Program only *)      
let make_case_ml isrec pred c ci lf = 
  if isrec then 
    DOPN(XTRA("REC"),Array.append [|pred;c|] lf)
  else 
    mkMutCaseA ci pred c lf

(* if arity of mispec is (p_bar:P_bar)(a_bar:A_bar)s where p_bar are the
 * K parameters. Then then build_notdep builds the predicate
 * [a_bar:A'_bar](lift k pred) 
 * where A'_bar = A_bar[p_bar <- globargs] *)

let build_notdep_pred env sigma indf pred =
  let arsign,_ = get_arity env sigma indf in
  let nar = List.length arsign in
  it_lambda_name env (lift nar pred) arsign

let pred_case_ml_fail env sigma isrec (IndType (indf,realargs)) (i,ft) =
  let pred =
    let mispec,_ = dest_ind_family indf in
    let recargs = mis_recarg mispec in
    assert (Array.length recargs <> 0);
    let recargi = recargs.(i) in
    let j = mis_index mispec in
    let nbrec = if isrec then count_rec_arg j recargi else 0 in
    let nb_arg = List.length (recargs.(i)) + nbrec in
    let pred = concl_n env sigma nb_arg ft in
    if noccur_between 1 nb_arg pred then 
      lift (-nb_arg) pred
    else 
      failwith "Dependent"
  in
  if realargs = [] then 
    pred
  else (* we try with [_:T1]..[_:Tn](lift n pred) *)
    build_notdep_pred env sigma indf pred  

let pred_case_ml env sigma isrec indt lf (i,ft) = 
    pred_case_ml_fail env sigma isrec indt (i,ft)

(* similar to pred_case_ml but does not expect the list lf of braches *)
let pred_case_ml_onebranch env sigma isrec indt (i,f,ft) = 
    pred_case_ml_fail env sigma isrec indt (i,ft)

(************************************************************************)
(*            Pattern-matching compilation (Cases)                      *)
(************************************************************************)

(************************************************************************)
(* Configuration, errors and warnings *)

let substitute_alias = ref false

open Pp

let error_bad_pattern_loc a = failwith "TODO1"

let mssg_may_need_inversion () =
  [< 'sTR "This pattern-matching is not exhaustive.">]

let mssg_this_case_cannot_occur () =
  "This pattern-matching is not exhaustive."

(* Utils *)

let ctxt_of_ids ids =
  Array.of_list (List.map (function id -> VAR id) ids)
let constructor_of_rawconstructor (cstr_sp,ids) = (cstr_sp,ctxt_of_ids ids)
let inductive_of_rawconstructor c =
  inductive_of_constructor (constructor_of_rawconstructor c)

(* Environment management *)
let push_rel_type sigma (na,t) env =
  push_rel (na,make_typed t (get_sort_of env sigma t)) env

let push_rels vars env =
  List.fold_left (fun env nvar -> push_rel_type Evd.empty nvar env) env vars

(**********************************************************************)
(* Structures used in compiling pattern-matching *)
type 'a lifted = int * 'a

let insert_lifted a = (0,a);;

(* INVARIANT:

   The pattern variables of it are the disjoint union of [user_ids]
   and the domain of [subst]. Non global VAR in the codomain of [subst] are
   in private_ids.
   The non pattern variables of it + the global VAR in the codomain of
   [subst] are in others_ids

*)

type rhs =
    { rhs_env    : env;
      other_ids  : identifier list;
      private_ids: identifier list;
      user_ids   : identifier list;
      subst      : (identifier * constr) list;
      rhs_lift   : int;
      it         : rawconstr }

type equation =
    { dependencies : constr lifted list;
      patterns     : cases_pattern list; 
      rhs          : rhs;
      tag          : pattern_source }

type matrix = equation list

(* 1st argument of IsInd is the original ind before extracting the summary *)
type tomatch_type =
  | IsInd of constr * inductive_type
  | NotInd of constr

type dependency_in_rhs = DepInRhs | NotDepInRhs
type dependency_on_previous = DepOnPrevious | NotDepOnPrevious
type dependency_status = dependency_on_previous * dependency_in_rhs

type pushed_attributes = (constr * tomatch_type) * dependency_in_rhs
type topush_attributes = (name * tomatch_type) * dependency_status

type tomatch_status =
  | Pushed of pushed_attributes lifted
  | ToPush of topush_attributes

type tomatch_stack = tomatch_status list

type predicate_signature =
  | PrLetIn of (constr list * constr option) * predicate_signature
  | PrProd of (bool * name * tomatch_type) * predicate_signature
  | PrCcl of constr

(* A pattern-matching problem has the following form:

   env, isevars |- <pred> Cases tomatch of mat end

  where tomatch is some sequence (t1  ... tn)

  and mat is some matrix 
   (p11 ... p1n -> rhs1)
   (    ...            )
   (pm1 ... pmn -> rhsm)

  Terms to match: there are 3 kinds of terms to match

  - initials terms are arbitrary terms given by user and typed in [env]
  - to-push inherited terms are subterms, actually variables, obtained
    from the top-down analysis of pattern, they are typed in [env]
    enriched by the previous inherited terms to match and are still to be
    pushed in env
  - pushed inherited terms are variables refering to a variable in [env]

  A variable inherited from a subpattern is not immediately pushed in
  [env] because of possible dependencies from previous variables to match

  Right-hand-sides:

  They consist of a raw term to type in an environment specific to the
  clause they belong to: the names of declarations are those of the
  variables present in the patterns. Therefore, they come with their
  own [rhs_env] (actually it is the same as [env] except for the names
  of variables).

*)
type 'a pattern_matching_problem =
    { env      : env;
      isevars  : 'a evar_defs;
      pred     : predicate_signature option;
      tomatch  : tomatch_stack;
      mat      : matrix;
      typing_function: trad_constraint -> env -> rawconstr -> unsafe_judgment }

(************************************************************************)
(* Utils *)

let to_mutind env sigma t =
  try IsInd (t,find_inductive env sigma t)
  with Induc -> NotInd t

let type_of_tomatch_type = function
    IsInd (t,ind) -> t
  | NotInd t -> t

let current_pattern eqn =
  match eqn.patterns with
    | pat::_ -> pat
    | [] -> anomaly "Empty list of patterns"

let alias_of_pat = function
  | PatVar (_,name) -> name
  | PatCstr(_,_,_,name) -> name

let remove_current_pattern eqn =
  match eqn.patterns with
    | _::pats -> { eqn with patterns = pats }
    | [] -> anomaly "Empty list of patterns"

let liftn_tomatch_type n depth = function
  | IsInd (t,ind) -> IsInd (liftn n depth t,liftn_inductive_type n depth ind)
  | NotInd t -> NotInd (liftn n depth t)

let lift_tomatch_type n = liftn_tomatch_type n 1

let lift_tomatch n ((current,typ),info) =
  ((lift n current,lift_tomatch_type n typ),info)

let substnl_tomatch v depth = function
  | IsInd (t,indt) -> IsInd (substnl v depth t,substnl_ind_type v depth indt)
  | NotInd t -> NotInd (substnl v depth t)

let subst_tomatch (depth,c) = substnl_tomatch [c] depth


(**********************************************************************)
(* Dealing with regular and default patterns *)
let is_regular eqn = eqn.tag = RegularPat

let lower_pattern_status = function
  | RegularPat -> DefaultPat 0
  | DefaultPat n -> DefaultPat (n+1)

let pattern_status defaults eqns =
  if eqns <> [] then RegularPat
  else
    let min =
      List.fold_right
	(fun (_,eqn) n -> match eqn with
	   | {tag = DefaultPat i} when i<n -> i
	   | _ -> n)
	defaults 0 in
    DefaultPat min

(**********************************************************************)
(* Well-formedness tests *)
(* Partial check on patterns *)

let check_constructor loc ((_,j as cstr_sp,ids),args) mind cstrs =
  (* Check it is constructor of the right type *)
  if inductive_path_of_constructor_path cstr_sp <> fst mind
  then error_bad_constructor_loc loc CCI (cstr_sp,ctxt_of_ids ids) mind;
  (* Check the constructor has the right number of args *)
  let nb_args_constr = cstrs.(j-1).cs_nargs in 
  if List.length args <> nb_args_constr
  then error_wrong_numarg_constructor_loc loc CCI cstr_sp nb_args_constr

let check_all_variables typ mat =
  List.iter
    (fun eqn -> match current_pattern eqn with
       | PatVar (_,id) -> ()
       | PatCstr (loc,_,_,_) -> error_bad_pattern_loc loc CCI typ)
    mat

let check_number_of_regular_eqns eqns =
  let n =
    List.fold_left(fun i eqn ->if is_regular eqn then i+1 else i) 0 eqns in
  match n with
    | 0 -> warning "Found several default clauses, kept the first one"
    | 1 -> ()
    | n -> errorlabstrm "build_leaf" [<'sTR "Some clauses are redondant" >]

(**********************************************************************)
(* Functions to deal with matrix factorization *)
let occur_rawconstr id =
  let rec occur = function
    | RRef (loc,RVar id) -> true
    | RApp (loc,f,args) -> (occur f) or (List.exists occur args)
    | RBinder (loc,bk,na,ty,c) -> (occur ty) or ((na <> Name id) & (occur c))
    | RCases (loc,prinfo,tyopt,tml,pl) ->
	(occur_option tyopt) or (List.exists occur tml)
	or (List.exists occur_pattern pl)
    | ROldCase (loc,b,tyopt,tm,bv) -> 
	(occur_option tyopt) or (occur tm) or (array_exists occur bv)
    | RRec (loc,fk,idl,tyl,bv) ->
	(array_exists occur tyl) or
	(not (array_exists (fun id2 -> id=id2) idl) & array_exists occur bv)
    | RCast (loc,c,t) -> (occur c) or (occur t)
    | (RSort _ | RHole _ | RRef _ | RMeta _) -> false

  and occur_pattern (idl,p,c) = not (List.mem id idl) & (occur c)

  and occur_option = function None -> false | Some p -> occur p

  in occur

let occur_in_rhs na rhs =
  match na with
    | Anonymous -> false
    | Name id -> occur_rawconstr id rhs.it

let is_dep_patt eqn pat = occur_in_rhs (alias_of_pat pat) eqn.rhs

let dependencies_in_rhs nargs eqns =
  if eqns = [] then list_tabulate (fun _ -> false) nargs (* Only "_" patts *)
  else
  let deps = List.map (fun (tms,eqn) -> List.map (is_dep_patt eqn) tms) eqns in
  let columns = matrix_transpose deps in
  List.map (List.for_all ((=) true)) columns

(* Introduction of an argument of the current constructor must be
   delayed (flag DepOnPrevious) if it depends in the rhs and depends
   on a previous variable of inductive type, or on a previous variable
   already dependent *)

let rec is_dep_on_previous n t = function
  | ((_,IsInd _),_)::_ when dependent (Rel n) t -> DepOnPrevious
  | ((_,NotInd _),(DepOnPrevious,DepInRhs))::_ 
      when dependent (Rel n) t -> DepOnPrevious
  | _::rest -> is_dep_on_previous (n+1) t rest
  | [] -> NotDepOnPrevious

let find_dependencies t prevlist is_dep_in_rhs =
  if is_dep_in_rhs then (is_dep_on_previous 1 t prevlist,DepInRhs)
  else (NotDepOnPrevious,NotDepInRhs)

(******)

(* A Pushed term to match has just been substituted by some
   constructor t = (ci x1...xn) and the terms x1 ... xn have been added to
   match 

   - all terms to match and to push (dependent on t by definition)
     must have (Rel depth) substituted by t and Rel's>depth lifted by n
   - all pushed terms to match (non dependent on t by definition) must
     be lifted by n

  We start with depth=1

  We delay lift for Pushed but not for ToPush (trop complexe !)
*)

let rec lift_subst_tomatch n (depth,ci as binder) = function
  | [] -> []

  (* By definition ToPush terms depend on the previous substituted tm *)
  (* and they contribute to the environment (hence [depth+1]) *)
  | ToPush ((na,t),info)::rest ->
      let t' = liftn_tomatch_type n (depth+1) t in
      let t'' = subst_tomatch binder t' in
      ToPush ((na,t''), info)::(lift_subst_tomatch n (depth+1,ci) rest)

  (* By definition Pushed terms do not depend on previous terms to match *)
  (* and are already pushed in the environment; *)
  (* if all is correct, [c] has no variables < depth *)
  | Pushed (lift,tm)::rest ->
      Pushed (n+lift, tm)::(lift_subst_tomatch n binder rest)

let subst_in_subst id t (id2,c) = (id2,replace_vars [(id,t)] c)

let replace_id_in_rhs id t rhs =
  if List.mem id rhs.private_ids then
    {rhs with
	 subst = List.map (subst_in_subst id t) rhs.subst;
         private_ids = list_except id rhs.private_ids}
  else if List.mem id rhs.user_ids & not (List.mem_assoc id rhs.subst) then
  {rhs with subst = (id,t)::List.map (subst_in_subst id t) rhs.subst}
  else anomaly ("Found a pattern variables neither private nor user supplied: "
		^(string_of_id id))

let replace_name_in_rhs name c rhs =
  match name with
    | Anonymous -> rhs
    | Name id -> replace_id_in_rhs id c rhs

(* if [current] has type [I(p1...pn u1...um)] and we consider the case
   of constructor [ci] of type [I(p1...pn u'1...u'm)], then the
   default variable [name] is expected to have which type?
   Rem: [current] is [(Rel i)] except perhaps for initial terms to match *)

let rec pop_next_tomatchs acc = function
  | ToPush((na,t),(NotDepOnPrevious,_ as deps))::l ->
      pop_next_tomatchs (((na,t),deps)::acc) l
  | ((ToPush(_,(DepOnPrevious,_)) | Pushed _)::_ | []) as l -> (acc,l)

let expand_defaults pats current (name,eqn) =
  { eqn with
      patterns = pats @ eqn.patterns;
      rhs = replace_name_in_rhs name current eqn.rhs;
      tag = lower_pattern_status eqn.tag }

(************************************************************************)
(* Some heuristics to get names for variables pushed in pb environment *)

let merge_names get_name =
  List.map2 (fun obj na -> match na with
	       | Anonymous -> get_name obj
	       | _ -> na)

let get_names env sign eqns =
  let names1 = list_tabulate (fun _ -> Anonymous) (List.length sign) in
  (* If any, we prefer names used in pats, from top to bottom *)
  let names2 = 
    List.fold_right
      (fun (pats,eqn) names -> merge_names alias_of_pat pats names)
      eqns names1 in
  (* Otherwise, we take names from the parameters of the constructor *)
  let names3 = merge_names (fun (na,t) -> named_hd env t na) sign names2 in
  (* Then we rename the base names to avoid conflicts *)
  let allvars =
    List.fold_left (fun l (_,eqn) -> list_union l eqn.rhs.other_ids) [] eqns in
  let names4,_ =
    List.fold_left
      (fun (l,avoid) na ->
	 let id = next_name_away na avoid in
      ((Name id)::l,id::avoid)) ([],allvars) names3 in
  List.rev names4

(************************************************************************)
(* Recovering names for variables pushed to the rhs' environment *)

let rec recover_pat_names = function
  | (_,t)::sign,p::pats -> (alias_of_pat p,t)::(recover_pat_names (sign,pats))
  | [],_ -> []
  | _,[] -> anomaly "Cases.recover_pat_names: Not enough patterns"

let push_rels_eqn sign eqn =
  let sign' = recover_pat_names (sign, eqn.patterns) in
  {eqn with
     rhs = {eqn.rhs with
	      rhs_env = push_rels sign' eqn.rhs.rhs_env} }

let prepend_pattern tms eqn = {eqn with patterns = tms@eqn.patterns }

(*
let substitute_rhs current pb =
  if !substitute_alias then { pb with subst = current::pb.subst } else pb
*)
let pop_pattern eqn = { eqn with patterns = List.tl eqn.patterns }

(**********************************************************************)
(* Functions to deal with elimination predicate *)

(* Infering the predicate *)
let prepare_unif_pb typ cs =
  let n = cs.cs_nargs in
  let (sign,p) = decompose_prod_n n typ in

  (* We may need to invert ci if its parameters occur in p *)
  let p' =
    if noccur_between 1 n p then lift (-n) p
    else 
      (* Il faudrait que noccur_between ne regarde pas la subst des Evar *)
      if match p with DOPN(Evar _,_) -> true | _ -> false then lift (-n) p
      else
	 failwith "TODO4-1" in
  let ci = applist
	     (mkMutConstruct cs.cs_cstr, cs.cs_params@(rel_list (-n) n)) in

  (* This is the problem: finding P s.t. cs_args |- (P realargs ci) = p' *)
  (Array.map (lift (-n)) cs.cs_concl_realargs, ci, p')

let abstract_conclusion typ cs =
  let n = cs.cs_nargs in
  let (sign,p) = decompose_prod_n n typ in
  lam_it p sign

let infer_predicate env isevars typs cstrs (IndFamily (mis,_) as indf) =
  (* Il faudra substituer les isevars a un certain moment *)
  let eqns = array_map2 prepare_unif_pb typs cstrs in

  (* First strategy: no dependencies at all *)
  let (cclargs,_,typn) = eqns.(mis_nconstr mis -1) in
  let (sign,_) = get_arity env !isevars indf in
  if array_for_all (fun (_,_,typ) -> the_conv_x env isevars typn typ) eqns
  then
    let pred = lam_it (lift (List.length sign) typn) sign in
    (false,pred) (* true = dependent -- par défaut *)
  else
    if Array.length typs = 0 then
      failwith "TODO4-3"
    else
      let s = get_sort_of env !isevars typs.(0) in
      let predpred = lam_it (mkSort s) sign in
      let caseinfo = make_default_case_info mis in
      let brs = array_map2 abstract_conclusion typs cstrs in
      let predbody = mkMutCaseA caseinfo predpred (Rel 1) brs in
      let pred = lam_it (lift (List.length sign) typn) sign in
      failwith "TODO4-2"; (true,pred)

(* Propagation of user-provided predicate through compilation steps *)

let lift_predicate n pred =
  let rec liftrec k = function
  | PrCcl ccl -> PrCcl (liftn n k ccl)
  | PrProd ((dep,na,t),pred) ->
	PrProd ((dep,na,liftn_tomatch_type n k t), liftrec (k+1) pred)
    | PrLetIn ((args,copt),pred) ->
	let args' = List.map (liftn n k) args in
	let copt' = option_app (liftn n k) copt in
	PrLetIn ((args',copt'), liftrec (k+1) pred) in
  liftrec 1 pred

let subst_predicate (args,copt) pred =
  let sigma = match copt with
    | None -> args
    | Some c -> args@[c] in
  let rec substrec k = function
    | PrCcl ccl -> PrCcl (substnl sigma k ccl)
    | PrProd ((dep,na,t),pred) ->
	PrProd ((dep,na,substnl_tomatch sigma k t), substrec (k+1) pred)
    | PrLetIn ((args,copt),pred) ->
	let args' = List.map (substnl sigma k) args in
	let copt' = option_app (substnl sigma k) copt in
	PrLetIn ((args',copt'), substrec (k+1) pred) in
  substrec 0 pred

let specialize_predicate_var = function
  | PrProd _ | PrCcl _ ->
     anomaly "specialize_predicate_var: a pattern-variable must be pushed"
  | PrLetIn (tm,pred) -> subst_predicate tm pred

let rec weaken_predicate n pred =
  if n=0 then pred else match pred with
    | PrLetIn _ | PrCcl _ ->
		    anomaly "weaken_predicate: only product can be weakened"
    | PrProd ((dep,_,IsInd (_,IndType(indf,realargs))),pred) ->
	(* To make it more uniform, we apply realargs but they not occur! *)
	let copt = if dep then Some (Rel n) else None in
	PrLetIn ((realargs,copt), weaken_predicate (n-1)
		   (lift_predicate (List.length realargs) pred))
    | PrProd ((dep,_,NotInd t),pred) ->
	let copt = if dep then Some (Rel n) else None in
	PrLetIn (([],copt), weaken_predicate (n-1) pred)

let rec extract_predicate = function
  | PrProd ((_,na,t),pred) ->
      mkProd na (type_of_tomatch_type t) (extract_predicate pred)
  | PrLetIn ((args,Some c),pred) -> substl (args@[c]) (extract_predicate pred)
  | PrLetIn ((args,None),pred) -> substl args (extract_predicate pred)
  | PrCcl ccl -> ccl

let abstract_predicate env sigma indf = function
  | PrProd _ | PrCcl _ -> anomaly "abstract_predicate: must be some LetIn"
  | PrLetIn ((_,copt),pred) ->
      let asign,_ = get_arity env sigma indf in
      let sign =
	List.map (fun (na,t) -> (named_hd (Global.env()) t na,t)) asign in
      let dep = copt<> None in
      let sign' =
	if dep then
	  let ind = build_dependent_inductive indf in
	  let na = named_hd (Global.env()) ind Anonymous in
	  (na,ind)::sign
	else sign in
      (dep, lam_it (extract_predicate pred) sign')

let specialize_predicate_match tomatchs cs = function
  | PrProd _ | PrCcl _ ->
     anomaly "specialize_predicate_match: a matched pattern must be pushed"
  | PrLetIn ((args,copt),pred) ->
      let argsi = Array.to_list cs.cs_concl_realargs in
      let copti = option_app (fun _ -> build_dependent_constructor cs) copt in
      let pred' = subst_predicate (argsi, copti) pred in
      let pred'' = lift_predicate cs.cs_nargs pred' in
      let dep = (copt <> None) in
      List.fold_right
	(* Ne perd-on pas des cas en ne posant pas true à la place de dep ? *)
	(fun ((na,t),_) p -> PrProd ((dep,na,t),p)) tomatchs pred''

let find_predicate env isevars p typs cstrs current (IndType (indf,realargs)) =
  let (dep,pred) =
    match p with
      | Some p -> abstract_predicate env !isevars indf p
      | None -> infer_predicate env isevars typs cstrs indf in
  let typ = applist (pred, realargs) in
  if dep then (pred, applist (typ, [current]), Type Univ.dummy_univ)
  else (pred, typ, Type Univ.dummy_univ)

(************************************************************************)
(* Sorting equation by constructor *)

type inversion_problem =
  (* the discriminating arg in some Ind and its order in Ind *)
  | Incompatible of int * (int * int)
  | Constraints of (int * constr) list

let solve_constraints constr_info indt =
  (* TODO *)
  Constraints []

let group_equations mind cstrs mat =
  let brs = Array.create (Array.length cstrs) [] in
  let dflt = ref [] in
  let _ =
    List.fold_left (* To be sure it's from bottom to top *)
      (fun () eqn ->
	 let rest = remove_current_pattern eqn in
	 match current_pattern eqn with
	   | PatVar (_,name) -> dflt := (name,rest) :: !dflt
	   | PatCstr(loc,((ind_sp,i),ids as cstr),largs,alias) ->
	       check_constructor loc (cstr,largs) mind cstrs;
	       brs.(i-1) <- (largs,rest) :: brs.(i-1)) () mat in
  (brs,!dflt)

(************************************************************************)
(* Here start the pattern-matching compiling algorithm *)

(* No more patterns: typing the right-hand-side of equations *)
let build_leaf pb =
  let rhs =
    match pb.mat with 
      | [] -> errorlabstrm "build_leaf" (mssg_may_need_inversion())
      | (eqn::_::_ as eqns) ->
	  check_number_of_regular_eqns eqns;
	  assert (eqn.tag = RegularPat); eqn.rhs
      | [eqn] -> eqn.rhs in
(*
      if List.length rhs.user_ids <> List.length rhs.subst then 
	anomaly "Some user pattern variable has not been substituted";
*)
  if rhs.private_ids <> [] then
    anomaly "Some private pattern variable has not been substituted";
  let tycon = match pb.pred with
    | None -> empty_tycon
    | Some (PrCcl typ) -> mk_tycon typ
    | Some _ -> anomaly "not all parameters of pred have been consumed" in
  let j = pb.typing_function tycon rhs.rhs_env rhs.it in
  let subst = (*List.map (fun id -> (id,make_substituend (List.assoc id rhs.subst))) rhs.user_ids *)[] in
  {uj_val = replace_vars subst j.uj_val;
   uj_type = typed_app (replace_vars subst) j.uj_type }

(* Building the sub-problem when all patterns are variables *)
let shift_problem pb =
  (* rhs have alr. the right env: we just have to pop a pattern & cook pred *)
  {pb with
     pred = option_app specialize_predicate_var pb.pred;
     mat = List.map pop_pattern pb.mat }

(* Building the sub-pattern-matching problem for a given branch *)
let build_branch pb defaults current eqns const_info =
  let names = get_names pb.env const_info.cs_args eqns in
  let newpats =
  if !substitute_alias then
    List.map (fun na -> PatVar (dummy_loc,na)) names
  else
    List.map (fun _ -> PatVar (dummy_loc,Anonymous)) names in
  let submatdef = List.map (expand_defaults newpats current) defaults in
  let submat = List.map (fun (tms,eqn) -> prepend_pattern tms eqn) eqns in
  if submat = [] & submatdef = [] then error "Non exhaustive";
  let typs = List.map2 (fun (_,t) na -> (na,t)) const_info.cs_args names in
  let tomatchs =
    List.fold_left2
      (fun l (na,t) dep_in_rhs ->
	 ((na,to_mutind pb.env !(pb.isevars) t),
	  (find_dependencies t l dep_in_rhs))::l)
      [] typs (dependencies_in_rhs const_info.cs_nargs eqns) in
  let topushs = List.map (fun x -> ToPush x) tomatchs in
  (* The dependent term to subst in the types of the remaining UnPushed 
     terms is relative to the current context enriched by topushs *)
  let ci =
    applist
      (mkMutConstruct const_info.cs_cstr, 
       (List.map (lift const_info.cs_nargs) const_info.cs_params)
       @(rel_list 0 const_info.cs_nargs)) in

  (* We replace [(Rel 1)] by its expansion [ci] *)
  let updated_old_tomatch =
    lift_subst_tomatch const_info.cs_nargs (1,ci) pb.tomatch in
  { pb with
      tomatch = topushs@updated_old_tomatch;
      mat = submat@submatdef;
      pred = option_app (specialize_predicate_match tomatchs const_info) pb.pred }

(**********************************************************************
 INVARIANT:

  pb = { env, subst, tomatch, mat, ...}
  tomatch = list of Pushed (c:T) or ToPush (na:T) or Initial (c:T)

  "Pushed" terms and types are relative to env
  "ToPush" types are relative to env enriched by the previous terms to match

  Concretely, each term "c" or type "T" comes with a delayed lift
  index, but it works as if the lifting were effective.

*)

(**********************************************************************)
(* Main compiling descent *)
let rec compile pb =
  match pb.tomatch with
    | (Pushed cur)::rest -> match_current { pb with tomatch = rest } cur
    | (ToPush next)::rest -> compile_further pb next rest
    | [] -> build_leaf pb

and match_current pb (n,tm) =
  let ((current,typ),info) = lift_tomatch n tm in
  match typ with
    | NotInd typ ->
	check_all_variables typ pb.mat;
	compile (shift_problem pb)
    | IsInd (_,(IndType(indf,realargs) as indt)) ->
	let mis,_ = dest_ind_family indf in
	let cstrs = get_constructors indf in
	let eqns,defaults = group_equations (mis_inductive mis) cstrs pb.mat in
	if array_for_all ((=) []) eqns
	then compile (shift_problem pb)
	else
          let constraints = Array.map (solve_constraints indt) cstrs in
	  let pbs =
	    array_map2 (build_branch pb defaults current) eqns cstrs in
	  let tags = Array.map (pattern_status defaults) eqns in
	  let brs = Array.map compile pbs in
	  let brvals = Array.map (fun j -> j.uj_val) brs in
	  let brtyps = Array.map (fun j -> body_of_type j.uj_type) brs in
	  let (pred,typ,s) =
	    find_predicate pb.env pb.isevars 
	      pb.pred brtyps cstrs current indt in
	  let ci = make_case_info mis None tags in
	  { uj_val = mkMutCaseA ci (*eta_reduce_if_rel*) pred current brvals;
	    uj_type = make_typed typ s }

and compile_further pb firstnext rest =
  (* We pop as much as possible tomatch not dependent one of the other *)
  let nexts,future = pop_next_tomatchs [firstnext] rest in
  (* the next pattern to match is at the end of [nexts], it has ref (Rel n)
     where n is the length of nexts *)
  let sign = List.map (fun ((na,t),_) -> (na,type_of_tomatch_type t)) nexts in
  let revsign = List.rev sign in
  let currents =
    list_map_i
      (fun i ((na,t),(_,rhsdep)) ->
	 Pushed (insert_lifted ((Rel i, lift_tomatch_type i t), rhsdep)))
      1 nexts in
  let pb' = { pb with
		env = push_rels revsign pb.env;
		tomatch = List.rev_append currents future;
                pred= option_app (weaken_predicate (List.length sign)) pb.pred;
		mat = List.map (push_rels_eqn revsign) pb.mat } in
  let j = compile pb' in
  { uj_val = lam_it j.uj_val sign;
    uj_type =  (* Pas d'univers ici: imprédicatif si Prop/Set, dummy si Type *)
      typed_app (fun t -> prod_it t sign) j.uj_type }


(* pour les alias des initiaux, enrichir les env de ce qu'il faut et
substituer après par les initiaux *)

(**************************************************************************)
(* Preparation of the pattern-matching problem                            *)

(* builds the matrix of equations testing that each eqn has n patterns
 * and linearizing the _ patterns.
 * Syntactic correctness has already been done in astterm *)
let matx_of_eqns env eqns =
  let build_eqn (ids,lpatt,rhs) =
    let rhs =
      { rhs_env = env;
	other_ids = ids@(ids_of_sign (get_globals (context env)));
	private_ids = [];
	user_ids = ids;
	subst = [];
	rhs_lift = 0;
	it = rhs }
    in { dependencies = [];
	 patterns = lpatt;
	 tag = RegularPat;
	 rhs = rhs }
  in List.map build_eqn eqns

(*--------------------------------------------------------------------------*
 * A few functions to infer the inductive type from the patterns instead of *
 * checking that the patterns correspond to the ind. type of the            *
 * destructurated object. Allows type inference of examples like            *
 *  [n]Cases n of O => true | _ => false end                                *
 *--------------------------------------------------------------------------*)

(* Computing the inductive type from the matrix of patterns *)

let rec find_row_ind = function
    [] -> None
  | PatVar _ :: l -> find_row_ind l
  | PatCstr(loc,c,_,_) :: _ -> Some (loc,c)

(* We do the unification for all the rows that contain
 * constructor patterns. This is what we do at the higher level of patterns.
 * For nested patterns, we do this unif when we ``expand'' the matrix, and we
 * use the function above.
 *)

exception NotCoercible

let inh_coerce_to_ind isevars env ty tyi =
  let (ntys,_) = splay_prod env !isevars (mis_arity (Global.lookup_mind_specif tyi)) in
  let (_,evarl) =
    List.fold_right
      (fun (na,ty) (env,evl) ->
	 let s = get_sort_of env Evd.empty ty in
	   (push_rel (na,(make_typed ty s)) env,
	    (new_isevar isevars env (mkCast ty (mkSort s)) CCI)::evl))
      ntys (env,[]) in
  let expected_typ = applist (mkMutInd tyi,evarl) in
     (* devrait être indifférent d'exiger leq ou pas puisque pour 
        un inductif cela doit être égal *)
  if the_conv_x_leq env isevars expected_typ ty then ty
  else raise NotCoercible


let coerce_row typing_fun isevars env row tomatch =
  let j = typing_fun empty_tycon env tomatch in
  let typ = body_of_type j.uj_type in
  let t =
    match find_row_ind row with
	Some (cloc,(cstr,_ as c)) ->
	  (let tyi = inductive_of_rawconstructor c in
	   try 
	     let indtyp = inh_coerce_to_ind isevars env typ tyi in
	     IsInd (typ,find_inductive env !isevars typ)
	   with NotCoercible ->
	     (* 2 cas : pas le bon inductive ou pas un inductif du tout *)
	     try
	       let mind,_ = find_minductype env !isevars typ in
	       error_bad_constructor_loc cloc CCI
		 (constructor_of_rawconstructor c) mind
	     with Induc ->
	       error_case_not_inductive_loc
		 (loc_of_rawconstr tomatch) CCI env j.uj_val typ)
      | None -> 
	  try IsInd (typ,find_inductive env !isevars typ)
	  with Induc -> NotInd typ
  in (j.uj_val,t)

let coerce_to_indtype typing_fun isevars env matx tomatchl =
  let pats = List.map (fun r ->  r.patterns) matx in
  List.map2
    (coerce_row typing_fun isevars env)
    (matrix_transpose pats) tomatchl

(***********************************************************************)
(* preparing the elimination predicate if any                          *)

let build_expected_arity env sigma isdep tomatchl sort =
  let cook n = function
    | _,IsInd (_,IndType(indf,_)) ->
	let indf' = lift_inductive_family n indf in
	(build_dependent_inductive indf', fst (get_arity env sigma indf'))
    | _,NotInd _ -> anomaly "Should have been catched in case_dependent"
  in
  let rec buildrec n = function
    | [] -> sort
    | tm::ltm ->
	let (ty1,aritysign) = cook n tm in
	let rec follow n = function
	  | (na,ty2)::sign -> DOP2(Prod,ty2,DLAM(na,follow (n+1) sign))
	  | _ ->
	      if isdep then DOP2(Prod,ty1,DLAM(Anonymous,buildrec (n+1) ltm))
	      else buildrec n ltm
	in follow n (List.rev aritysign)
  in buildrec 0 tomatchl

let build_initial_predicate isdep pred tomatchl =
  let cook n = function
    | _,IsInd (_,IndType(ind_data,realargs)) ->
	let args = List.map (lift n) realargs in
	if isdep then
	  let ty = lift n (build_dependent_inductive ind_data) in
	  (List.length realargs + 1, (args,Some ty))
	else
	  (List.length realargs, (args,None))
    | _,NotInd _ -> anomaly "Should have been catched in case_dependent"
  in
  let rec buildrec n pred = function
    | [] -> PrCcl pred
    | tm::ltm ->
	let (nargs,args) = cook n tm in
	PrLetIn (args,buildrec (n+nargs) (snd(decompose_lam_n nargs pred)) ltm)
  in buildrec 0 pred tomatchl

let rec eta_expand0 env sigma n c t =
  match whd_betadeltaiota env sigma t with
      DOP2(Prod,a,DLAM(na,b)) ->
	DOP2(Lambda,a,DLAM(na,eta_expand0 env sigma (n+1) c b))
   | _ -> applist (lift n c, rel_list 0 n)


let rec eta_expand env sigma c t =
  match whd_betadeltaiota env sigma c, whd_betadeltaiota env sigma t with
   | (DOP2(Lambda,ta,DLAM(na,cb)), DOP2(Prod,_,DLAM(_,tb))) ->
       DOP2(Lambda,ta,DLAM(na,eta_expand env sigma cb tb))
   | (c, t) -> eta_expand0 env sigma 0 c t

(* determines wether the multiple case is dependent or not. For that
 * the predicate given by the user is eta-expanded. If the result
 * of expansion is pred, then :
 * if pred=[x1:T1]...[xn:Tn]P and tomatchj=[|[e1:S1]...[ej:Sj]] then
 * if n= SUM {i=1 to j} nb_prod (arity Sj)
 *  then case_dependent= false
 *  else if n= j+(SUM (i=1 to j) nb_prod(arity Sj))
 *        then case_dependent=true
 *        else error! (can not treat mixed dependent and non dependent case
 *)
let case_dependent env sigma loc predj tomatchs =
  let nb_dep_ity = function
      (_,IsInd (_,IndType(_,realargs))) -> List.length realargs
    | (c,NotInd t) ->
	errorlabstrm "case_dependent" (error_case_not_inductive CCI env c t)
  in
  let etapred = eta_expand env sigma predj.uj_val (body_of_type predj.uj_type) in
  let n = nb_lam etapred in
  let _,sort = splay_prod env sigma (body_of_type predj.uj_type) in
  let ndepv = List.map nb_dep_ity tomatchs in
  let sum = List.fold_right (fun i j -> i+j)  ndepv 0 in
  let depsum = sum + List.length tomatchs in
  if n = sum then (false,build_expected_arity env sigma false tomatchs sort)
  else if n = depsum
  then (true,build_expected_arity env sigma true tomatchs sort)
  else error_wrong_predicate_arity_loc loc CCI env etapred sum depsum

let prepare_predicate typing_fun isevars env tomatchs = function
  | None -> None
  | Some pred ->
      let loc = loc_of_rawconstr pred in
      (* First typing to know if it is dependent *)
      let predj1 = typing_fun empty_tycon env pred in
      let cdep,arity = case_dependent env !isevars loc predj1 tomatchs in
      (* We got the expected arity of pred and relaunch pretype with it *)
      let predj = typing_fun (mk_tycon arity) env pred in
      let etapred = eta_expand env !isevars predj.uj_val (body_of_type predj.uj_type) in
      Some (build_initial_predicate cdep etapred tomatchs)

(**************************************************************************)
(* Main entry of the matching compilation                                 *)

let compile_cases loc (typing_fun,isevars) vtcon env (predopt, tomatchl, eqns)=

  (* We build the matrix of patterns and right-hand-side *)
  let matx = matx_of_eqns env eqns in

  (* We build the vector of terms to match consistently with the *)
  (* constructors found in patterns *)
  let tomatchs = coerce_to_indtype typing_fun isevars env matx tomatchl in

  (* We build the elimination predicate if any and check its consistency *)
  (* with the type of arguments to match *)
  let pred = prepare_predicate typing_fun isevars env tomatchs predopt in

  let initial_pushed =
    List.map (fun tm -> Pushed (insert_lifted (tm,NotDepInRhs))) tomatchs in

  let pb =
    { env      = env;
      isevars  = isevars;
      pred     = pred;
      tomatch  = initial_pushed;
      mat      = matx;
      typing_function = typing_fun } in
  
  let j = compile pb in
  
  match vtcon with
    | (_,(_,Some p)) ->
	let p = make_typed p (get_sort_of env !isevars p) in
	Coercion.inh_conv_coerce_to loc env isevars j p
    | _ -> j
