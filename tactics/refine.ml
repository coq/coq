
(* $Id$ *)

(* JCF -- 6 janvier 1998  EXPERIMENTAL *)

(*
 *  L'idée est, en quelque sorte, d'avoir de "vraies" métavariables
 *  dans Coq, c'est-à-dire de donner des preuves incomplètes -- mais
 *  où les trous sont typés -- et que les sous-buts correspondants
 *  soient engendrés pour finir la preuve.
 *
 *  Exemple : 
 *    J'ai le but
 *        (x:nat) { y:nat | (minus y x) = x }
 *    et je donne la preuve incomplète
 *        [x:nat](exist nat [y:nat]((minus y x)=x) (plus x x) ?)
 *    ce qui engendre le but
 *        (minus (plus x x) x)=x
 *)

(*  Pour cela, on procède de la manière suivante :
 *
 *  1. Un terme de preuve incomplet est un terme contenant des variables
 *     existentielles Evar i.e. "?" en syntaxe concrète.
 *     La résolution de ces variables n'est plus nécessairement totale
 *     (ise_resolve called with fail_evar=false) et les variables
 *     existentielles restantes sont remplacées par des méta-variables
 *     castées par leur types (celui est connu : soit donné, soit trouvé
 *     pendant la phase de résolution).
 *
 *  2. On met ensuite le terme "à plat" i.e. on n'autorise des MV qu'au
 *     permier niveau et pour chacune d'elles, si nécessaire, on donne
 *     à son tour un terme de preuve incomplet pour la résoudre.
 *     Exemple: le terme (f a ? [x:nat](e ?)) donne
 *         (f a ?1 ?2) avec ?2 => [x:nat]?3 et ?3 => (e ?4)
 *         ?1 et ?4 donneront des buts
 *
 *  3. On écrit ensuite une tactique tcc qui engendre les sous-buts
 *     à partir d'une preuve incomplète.
 *)

open Pp
open Util
open Names
open Generic
open Term
open Tacmach
open Sign
open Environ
open Reduction
open Typing
open Tactics
open Tacticals
open Printer

type metamap = (int * constr) list

type term_with_holes = TH of constr * metamap * sg_proofs
and  sg_proofs       = (term_with_holes option) list

(* pour debugger *)

let rec pp_th (TH(c,mm,sg)) =
  [< 'sTR"TH=[ "; hOV 0 [< prterm c; 'fNL;
			      (* pp_mm mm; 'fNL; *)
			   pp_sg sg >] ; 'sTR "]" >]
and pp_mm l =
  hOV 0 (prlist_with_sep (fun _ -> [< 'fNL >]) 
	   (fun (n,c) -> [< 'iNT n; 'sTR" --> "; prterm c >]) l)
and pp_sg sg =
  hOV 0 (prlist_with_sep (fun _ -> [< 'fNL >])
	   (function None -> [< 'sTR"None" >] | Some th -> [< pp_th th >]) sg)
     
(*  compute_metamap : constr -> term_with_holes
 *  réalise le 2. ci-dessus
 *
 *  Pour cela, on renvoie une metamap qui indique pour chaque meta-variable
 *  si elle correspond à un but (None) ou si elle réduite à son tour
 *  par un terme de preuve incomplet (Some c).
 *
 *  On a donc l'INVARIANT suivant : le terme c rendu est "de niveau 1"
 *  -- i.e. à plat -- et la metamap contient autant d'éléments qu'il y 
 *  a de meta-variables dans c. On suppose de plus que l'ordre dans la
 *  metamap correspond à celui des buts qui seront engendrés par le refine.
 *)

let replace_by_meta env = function
  | TH (DOP0(Meta _) | DOP2(Cast,DOP0(Meta _),_) as m, mm, sgp) -> m,mm,sgp
  | (TH (c,mm,_)) as th ->
      let n = new_meta() in
      let m = DOP0(Meta n) in
      (* quand on introduit une mv on calcule son type *)
      let ty = match c with
	| DOP2(Lambda,c1,DLAM(Name id,DOP2(Cast,_,ty))) ->
	    mkNamedProd id c1 ty
	| DOP2(Lambda,c1,DLAM(Anonymous,DOP2(Cast,_,ty))) ->
	    mkArrow c1 ty
	| DOPN((AppL|MutCase _),_) ->
	    (** let j = ise_resolve true empty_evd mm (gLOB sign) c in **)
	    Retyping.get_type_of_with_meta env Evd.empty mm c
	| DOPN(Fix (_,j),v) ->
	    v.(j) (* en pleine confiance ! *)
	| _ -> invalid_arg "Tcc.replace_by_meta (TO DO)" 
      in
      DOP2(Cast,m,ty),[n,ty],[Some th]

exception NoMeta

let replace_in_array env a =
  if array_for_all (function (TH (_,_,[])) -> true | _ -> false) a then
    raise NoMeta;
  let a' = Array.map (function
			| (TH (c,mm,[])) -> c,mm,[]
			| th -> replace_by_meta env th) a 
  in
  let v' = Array.map (fun (x,_,_) -> x) a' in
  let mm = Array.fold_left (@) [] (Array.map (fun (_,x,_) -> x) a') in
  let sgp = Array.fold_left (@) [] (Array.map (fun (_,_,x) -> x) a') in
  v',mm,sgp
    
let fresh env n =
  let id = match n with Name x -> x | _ -> id_of_string "_" in
  next_global_ident_away id (ids_of_var_context (var_context env))

let rec compute_metamap env = function
  (* le terme est directement une preuve *)
  | DOP0(Sort _)
  | DOPN((Const _ | Abst _ | MutInd _ | MutConstruct _),_)
  | VAR _ | Rel _ as c -> TH (c,[],[])

  (* le terme est une mv => un but *)
  | DOP0(Meta n) as c ->
      Pp.warning (Printf.sprintf ("compute_metamap: MV(%d) sans type !\n") n);
      TH (c,[],[None])
  | DOP2(Cast,DOP0(Meta n),ty) as c -> TH (c,[n,ty],[None])

  (* abstraction => il faut décomposer si le terme dessous n'est pas pur
   *    attention : dans ce cas il faut remplacer (Rel 1) par (VAR x)
   *    où x est une variable FRAICHE *)
  | DOP2(Lambda,c1,DLAM(name,c2)) as c ->
      let v = fresh env name in
      (** let tj = ise_resolve_type true empty_evd [] (gLOB sign) c1 in **)
      let tj = Retyping.get_assumption_of env Evd.empty c1 in
      let env' = push_var_decl (v,tj) env in
      begin match compute_metamap env' (subst1 (VAR v) c2) with
	(* terme de preuve complet *)
	| TH (_,_,[]) -> TH (c,[],[])
	(* terme de preuve incomplet *)    
	| th ->
	    let m,mm,sgp = replace_by_meta env' th in
	    TH (DOP2(Lambda,c1,DLAM(Name v,m)), mm, sgp)
      end

  (* 4. Application *)
  | DOPN((AppL|MutCase _) as op,v) as c ->
      let a = Array.map (compute_metamap env) v in
      begin
	try
	  let v',mm,sgp = replace_in_array env a in TH (DOPN(op,v'),mm,sgp)
	with NoMeta ->
	  TH (c,[],[])
      end

  (* 5. Fix. *)
  | DOPN(Fix _,_) as c ->
      let ((ni,i),(ai,fi,v)) = destFix c in
      let vi = List.rev (List.map (fresh env) fi) in
      let env' =
	List.fold_left
	  (fun env (v,ar) -> push_var_decl (v,Retyping.get_assumption_of env Evd.empty ar) env)
	  env
	  (List.combine vi (Array.to_list ai)) 
      in
      let a = Array.map
		(compute_metamap env')
		(Array.map (substl (List.map (fun x -> VAR x) vi)) v) 
      in
      begin
	try
	  let v',mm,sgp = replace_in_array env' a in
	  let fi' = List.rev (List.map (fun id -> Name id) vi) in
	  let fix = mkFix ((ni,i),(ai,fi',v')) in
	  TH (fix,mm,sgp)
	with NoMeta ->
	  TH (c,[],[])
      end
	      
  (* Cast. Est-ce bien exact ? *)
  | DOP2(Cast,c,t) -> compute_metamap env c
      (*let TH (c',mm,sgp) = compute_metamap sign c in
	TH (DOP2(Cast,c',t),mm,sgp) *)
      
  (* Produit. Est-ce bien exact ? *)
  | DOP2(Prod,_,_) as c ->
      if occur_meta c then
	error "Refine: proof term contains metas in a product"
      else
      	TH (c,[],[])
 
  (* Autres cas. *)
  | _ ->
      invalid_arg "Tcc.compute_metamap"


(*  tcc_aux : term_with_holes -> tactic
 * 
 *  Réalise le 3. ci-dessus
 *)

let rec tcc_aux (TH (c,mm,sgp) as th) gl =
  match (c,sgp) with
    (* mv => sous-but : on ne fait rien *)
    | (DOP0(Meta _) | DOP2(Cast,DOP0(Meta _),_)) , _ ->
	tclIDTAC gl
	  
    (* terme pur => refine *)
    | _,[] ->
	refine c gl
	
    (* abstraction => intro *)
    | DOP2(Lambda,_,
	   DLAM(Name id,(DOP0(Meta _)|DOP2(Cast,DOP0(Meta _),_) as m))) ,_ ->
	begin match sgp with
	  | [None] -> introduction id gl
	  | [Some th] ->
	      tclTHEN (introduction id) (tcc_aux th) gl
	  | _ -> invalid_arg "Tcc.tcc_aux (bad length)"
	end
	
    | DOP2(Lambda,_,_),_ ->
	error "invalid abstraction passed to function tcc_aux !"
      
    (* fix => tactique Fix *)
    | DOPN(Fix _,_) , _ ->
      	let ((ni,_),(ai,fi,_)) = destFix c in
	let ids =
	  List.map (function Name id -> id | _ ->
		      error "recursive functions must have names !") fi 
	in
	tclTHENS
	  (mutual_fix ids (List.map succ (Array.to_list ni))
             (List.tl (Array.to_list ai)))
	  (List.map (function
		       | None -> tclIDTAC 
		       | Some th -> tcc_aux th) sgp)
	  gl

    (* sinon on fait refine du terme puis appels rec. sur les sous-buts.
     * c'est le cas pour AppL et MutCase. *)
    | _ ->
	tclTHENS
	  (refine c)
	  (List.map (function None -> tclIDTAC | Some th -> tcc_aux th) sgp)
	  gl

(* Et finalement la tactique refine elle-même : *)

let refine c gl =
  let env = pf_env gl in
  let th = compute_metamap env c in
  tcc_aux th gl

let refine_tac = Tacmach.hide_constr_tactic "Refine" refine

let my_constr_of_com_casted sigma env com typ = 
  let rawc = Astterm.interp_rawconstr sigma env com in
  Printf.printf "ICI\n"; flush stdout;
  let c = Pretyping.ise_resolve_casted_gen false sigma env [] [] typ rawc in
  Printf.printf "LA\n"; flush stdout;
  c
  (**
  let cc = mkCast (nf_ise1 sigma c) (nf_ise1 sigma typ) in
  try (unsafe_machine env sigma cc).uj_val
  with e -> Stdpp.raise_with_loc (Ast.loc com) e
  **)

open Proof_type

let dyn_tcc args gl = match args with 
  | [Command com]  ->
      let env = pf_env gl in
      refine
	(my_constr_of_com_casted (project gl) env com (pf_concl gl)) gl
  | [Constr c] -> 
      refine c gl
  | _ -> assert false

let tcc_tac = hide_tactic "Tcc" dyn_tcc


