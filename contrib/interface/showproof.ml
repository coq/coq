(*
#use "/cygdrive/D/Tools/coq-7avril/dev/base_include";;
open Coqast;;
*)
open Environ
open Evd
open Names
open Nameops
open Libnames
open Term
open Termops
open Util
open Proof_type
open Pfedit
open Translate
open Term
open Reductionops
open Clenv
open Typing
open Inductive
open Inductiveops
open Vernacinterp
open Declarations
open Showproof_ct
open Proof_trees
open Sign
open Pp
open Printer
open Rawterm
open Tacexpr
open Genarg
(*****************************************************************************)
(*
   Arbre de preuve maison:
   
*)

(* hypotheses *)

type nhyp = {hyp_name : identifier;
             hyp_type : Term.constr;
             hyp_full_type: Term.constr}
;;

type ntactic = tactic_expr
;;

type nproof =
    Notproved
  | Proof of ntactic * (ntree list)

and ngoal=
     {newhyp : nhyp list;
      t_concl : Term.constr;
      t_full_concl: Term.constr;
      t_full_env: Environ.named_context_val}
and ntree=
      {t_info:string;
	t_goal:ngoal;
       	t_proof : nproof}
;;


let hyps {t_info=info;
	 t_goal={newhyp=lh;t_concl=g;t_full_concl=gf;t_full_env=ge};
	 t_proof=p} = lh
;;

let concl {t_info=info;
	 t_goal={newhyp=lh;t_concl=g;t_full_concl=gf;t_full_env=ge};
	 t_proof=p} = g
;;

let proof {t_info=info;
	 t_goal={newhyp=lh;t_concl=g;t_full_concl=gf;t_full_env=ge};
	 t_proof=p} = p
;;
let g_env {t_info=info;
	 t_goal={newhyp=lh;t_concl=g;t_full_concl=gf;t_full_env=ge};
	 t_proof=p} = ge
;;
let sub_ntrees t =
  match (proof t) with
    Notproved -> []
  | Proof (_,l) -> l
;;

let tactic t =
  match (proof t) with
    Notproved -> failwith "no tactic applied"
  | Proof (t,_) -> t
;;


(* 
un arbre est clos s'il ne contient pas de sous-but non prouves,
ou bien s'il a un cousin gauche qui n'est pas clos 
ce qui fait qu'on a au plus un sous-but non clos, le premier sous-but.
*)
let update_closed nt =
  let found_not_closed=ref false in
  let rec update {t_info=b; t_goal=g; t_proof =p} =
    if !found_not_closed
    then  {t_info="to_prove"; t_goal=g; t_proof =p}
    else
      match p with
      	Notproved -> found_not_closed:=true;
	  {t_info="not_proved"; t_goal=g; t_proof =p}
      | Proof(tac,lt) ->
	  let lt1=List.map update lt in
	  let b=ref "proved" in
	  (List.iter
	     (fun x ->
	       if x.t_info ="not_proved" then b:="not_proved") lt1;
	   {t_info=(!b);
	     t_goal=g;
             t_proof=Proof(tac,lt1)})
  in update nt
    ;;
    
      
(*
    type complet avec les hypotheses.
*)

let long_type_hyp lh t=
   let t=ref t in
   List.iter (fun (n,th) ->
         let ni = match n with Name ni -> ni | _ -> assert false in
         t:= mkProd(n,th,subst_term (mkVar ni) !t))
       (List.rev lh);
   !t
;;

(* let long_type_hyp x y = y;; *)

(* Expansion des tactikelles *)

let seq_to_lnhyp sign sign' cl =
      let lh= ref (List.map (fun (x,c,t) -> (Name x, t)) sign) in
      let nh=List.map (fun (id,c,ty) -> 
             {hyp_name=id;
              hyp_type=ty;
              hyp_full_type=
                let res= long_type_hyp !lh ty in
                lh:=(!lh)@[(Name id,ty)];
                res})
              sign'
      in
      {newhyp=nh;
       t_concl=cl;
       t_full_concl=long_type_hyp !lh cl;
       t_full_env = Environ.val_of_named_context (sign@sign')}
;;


let rule_is_complex r =
   match r with
       Nested (Tactic 
		 ((TacArg (Tacexp _)
		 |TacAtom (_,(TacAuto _|TacSymmetry _))),_),_) -> true
   |_ -> false
;;

let rule_to_ntactic r =
   let rt =
     (match r with
       Nested(Tactic (t,_),_) -> t
     | Prim (Refine h) -> TacAtom (dummy_loc,TacExact (Tactics.inj_open h))
     | _ -> TacAtom (dummy_loc, TacIntroPattern [])) in
   if rule_is_complex r
   then (match rt with
           TacArg (Tacexp _) as t -> t
          | _ -> assert false)

   else rt
;;

(* Attribue les preuves de la liste l aux sous-buts non-prouvés de nt  *)


let fill_unproved nt l =
  let lnt = ref l in
  let rec fill nt =
    let {t_goal=g;t_proof=p}=nt in
       match p with
        Notproved -> let p=List.hd (!lnt) in
                     lnt:=List.tl (!lnt);
                     {t_info="to_prove";t_goal=g;t_proof=p}
       |Proof(tac,lt) ->
          {t_info="to_prove";t_goal=g;
           t_proof=Proof(tac,List.map fill lt)}
  in fill nt
;;
(* Differences entre signatures *)

let new_sign osign sign =
    let res=ref [] in
    List.iter (fun (id,c,ty) ->
		   try (let  (_,_,_ty1)= (lookup_named id osign) in
			())
		   with Not_found -> res:=(id,c,ty)::(!res))
              sign;
    !res
;;

let old_sign osign sign =
    let res=ref [] in
    List.iter (fun (id,c,ty) ->
		   try (let (_,_,ty1) = (lookup_named id osign) in
			if ty1 = ty then res:=(id,c,ty)::(!res))
		   with Not_found -> ())
              sign;
    !res
;;

(* convertit l'arbre de preuve courant en ntree *)
let  to_nproof sigma osign pf =
  let rec to_nproof_rec sigma osign pf =
    let {evar_hyps=sign;evar_concl=cl} = pf.goal in
    let sign = Environ.named_context_of_val sign in
    let nsign = new_sign osign sign in 
    let oldsign = old_sign osign sign in 
    match pf.ref with
      
      None -> {t_info="to_prove";
	      	t_goal=(seq_to_lnhyp oldsign nsign cl);
              	t_proof=Notproved}
    | Some(r,spfl) ->
      	if rule_is_complex r
      	then (
	  let p1= to_nproof_rec sigma sign (subproof_of_proof pf) in
          let ntree= fill_unproved p1 
              (List.map (fun x -> (to_nproof_rec sigma sign x).t_proof)
		 spfl) in
	  (match r with
	       Nested(Tactic (TacAtom (_, TacAuto _),_),_) ->
		 if spfl=[]
		 then
	      	   {t_info="to_prove";
	    	    t_goal= {newhyp=[];
			     t_concl=concl ntree;
			     t_full_concl=ntree.t_goal.t_full_concl;
			     t_full_env=ntree.t_goal.t_full_env};
		    t_proof= Proof (TacAtom (dummy_loc,TacExtend (dummy_loc,"InfoAuto",[])), [ntree])}
		 else ntree
	     | _ -> ntree))
      	else
	  {t_info="to_prove";
	    t_goal=(seq_to_lnhyp oldsign nsign cl);
       	    t_proof=(Proof (rule_to_ntactic r,
			      List.map (fun x -> to_nproof_rec sigma sign x) spfl))}
  in update_closed (to_nproof_rec sigma osign pf)
    ;;

(* 
  recupere l'arbre de preuve courant.
*)

let get_nproof () =
  to_nproof (Global.env()) []
            (Tacmach.proof_of_pftreestate (get_pftreestate()))
;;

    
(*****************************************************************************)
(*
   Pprinter
*)

let pr_void () = sphs "";;

let list_rem l = match l with [] -> [] |x::l1->l1;;

(* liste de chaines *)
let prls l = 
   let res = ref (sps (List.hd l)) in
   List.iter (fun s -> 
     res:= sphv [ !res; spb; sps s]) (list_rem l);
   !res
;;

let prphrases f l = 
   spv (List.map (fun s -> sphv [f s; sps ","]) l)
;;

(* indentation *)
let spi = spnb 3;;

(* en colonne *)
let prl f l = 
   if l=[] then spe else spv (List.map f l);;
(*en colonne,  avec indentation *)
let prli f l =  
   if l=[] then spe else sph [spi; spv (List.map f l)];;

(* 
  Langues.
*)

let rand l =
  List.nth l (Random.int (List.length l))
;;

type natural_languages = French | English;;
let natural_language = ref French;;

(*****************************************************************************)
(*
   Les liens html pour proof-by-pointing
*)

(* le path du but en cours. *)

let path=ref[1];;

let ftag_apply =ref (fun (n:string) t -> spt t);;

let ftag_case =ref (fun n -> sps n);;

let ftag_elim =ref (fun n ->  sps n);;

let ftag_hypt =ref (fun h t -> sphypt (translate_path !path) h t);;

let ftag_hyp =ref (fun h t -> sphyp (translate_path !path) h t);;

let ftag_uselemma =ref (fun h t ->
  let intro = match !natural_language with
    French -> "par"
  | English -> "by"
  in
  spuselemma intro h t);;

let ftag_toprove =ref (fun t -> sptoprove (translate_path !path) t);;

let tag_apply = !ftag_apply;;

let tag_case = !ftag_case;;

let tag_elim = !ftag_elim;;

let tag_uselemma = !ftag_uselemma;;

let tag_hyp = !ftag_hyp;;

let tag_hypt = !ftag_hypt;;

let tag_toprove = !ftag_toprove;;

(*****************************************************************************)

(* pluriel *)
let txtn n s =
  if n=1 then s
  else match s with
    |"un" -> "des"
    |"a" -> ""
    |"an" -> ""
    |"une" -> "des"
    |"Soit" -> "Soient"
    |"Let" -> "Let"
    | s -> s^"s"
;;

let _et () =  match !natural_language with
    French -> sps "et"
| English -> sps "and"
;;

let name_count = ref 0;;
let new_name () =
  name_count:=(!name_count)+1;
  string_of_int !name_count
;;

let enumerate f ln =
  match ln with
    [] -> []
  | [x] -> [f x]
  |ln -> 
  let rec enum_rec f ln = 
     (match ln with 
       [x;y] -> [f x; spb; sph [_et ();spb;f y]]
      |x::l -> [sph [(f x);sps ","];spb]@(enum_rec f l)
      | _ -> assert false)
  in enum_rec f ln
;;


let constr_of_ast = Constrintern.interp_constr Evd.empty (Global.env());;

let sp_tac tac = failwith "TODO"

let soit_A_une_proposition nh ln t=  match !natural_language with
    French ->
      sphv ([sps (txtn nh "Soit");spb]@(enumerate (fun x -> tag_hyp x t) ln)
            @[spb; prls [txtn nh "une";txtn nh "proposition"]])
| English ->
      sphv ([sps "Let";spb]@(enumerate (fun x -> tag_hyp x t) ln)
            @[spb; prls ["be"; txtn nh "a";txtn nh "proposition"]])
;;

let on_a ()=  match !natural_language with
  French -> rand ["on a "]
| English ->rand ["we have "]
;;

let bon_a ()=  match !natural_language with
  French -> rand ["On a "]
| English ->rand ["We have "]
;;

let soit_X_un_element_de_T nh ln t =  match !natural_language with
  French ->
    sphv ([sps (txtn nh "Soit");spb]@(enumerate (fun x -> tag_hyp x t) ln)
          @[spb; prls [txtn nh "un";txtn nh "élément";"de"]]
          @[spb; spt t])
| English ->
    sphv ([sps (txtn nh "Let");spb]@(enumerate (fun x -> tag_hyp x t) ln)
          @[spb; prls ["be";txtn nh "an";txtn nh "element";"of"]]
          @[spb; spt t])
;;

let soit_F_une_fonction_de_type_T nh ln t =  match !natural_language with
  French ->
    sphv ([sps (txtn nh "Soit");spb]@(enumerate (fun x -> tag_hyp x t) ln)
          @[spb; prls [txtn nh "une";txtn nh "fonction";"de";"type"]]
          @[spb; spt t])
| English ->
    sphv ([sps (txtn nh "Let");spb]@(enumerate (fun x -> tag_hyp x t) ln)
          @[spb; prls ["be";txtn nh "a";txtn nh "function";"of";"type"]]
          @[spb; spt t])
;;


let telle_que nh =  match !natural_language with
    French -> [prls [" ";txtn nh "telle";"que";" "]]
| English -> [prls [" "; "such";"that";" "]]
;;

let tel_que nh =  match !natural_language with
    French -> [prls [" ";txtn nh "tel";"que";" "]]
| English -> [prls [" ";"such";"that";" "]]
;;

let supposons () =  match !natural_language with
    French -> "Supposons "
|  English -> "Suppose "
;;

let cas () =  match !natural_language with
    French -> "Cas"
|  English -> "Case"
;;

let donnons_une_proposition () =  match !natural_language with
    French -> sph[ (prls ["Donnons";"une";"proposition"])]
|  English -> sph[ (prls ["Let us give";"a";"proposition"])]
;;

let montrons g =  match !natural_language with
    French -> sph[ sps (rand ["Prouvons";"Montrons";"Démontrons"]);
		   spb; spt g; sps ". "]
|  English -> sph[ sps (rand ["Let us";"Now"]);spb;
		   sps (rand ["prove";"show"]);
		   spb; spt g; sps ". "]
;;

let calculons_un_element_de g =  match !natural_language with
    French -> sph[ (prls ["Calculons";"un";"élément";"de"]);
		   spb; spt g; sps ". "]
|  English -> sph[ (prls ["Let us";"compute";"an";"element";"of"]);
		   spb; spt g; sps ". "]
;;

let calculons_une_fonction_de_type g =  match !natural_language with
    French -> sphv [ (prls ["Calculons";"une";"fonction";"de";"type"]);
                spb; spt g; sps ". "]
|  English -> sphv [ (prls ["Let";"us";"compute";"a";"function";"of";"type"]);
                spb; spt g; sps ". "];;

let en_simplifiant_on_obtient g =  match !natural_language with
    French ->
      sphv [ (prls [rand ["Après simplification,"; "En simplifiant,"];
		     rand ["on doit";"il reste à"];
		     rand ["prouver";"montrer";"démontrer"]]);
		     spb; spt g; sps ". "]
|  English ->
      sphv [ (prls [rand ["After simplification,"; "Simplifying,"];
		     rand ["we must";"it remains to"];
		     rand ["prove";"show"]]);
		     spb; spt g; sps ". "] ;;

let on_obtient g =  match !natural_language with
  French -> sph[ (prls [rand ["on doit";"il reste à"];
			 rand ["prouver";"montrer";"démontrer"]]);
                 spb; spt g; sps ". "]
|  English ->sph[ (prls [rand ["we must";"it remains to"];
		     rand ["prove";"show"]]);
                  spb; spt g; sps ". "]
;;

let reste_a_montrer g =  match !natural_language with
    French -> sph[ (prls ["Reste";"à";
			   rand ["prouver";"montrer";"démontrer"]]);
                spb; spt g; sps ". "]
|  English -> sph[ (prls ["It remains";"to";
			   rand ["prove";"show"]]);
                spb; spt g; sps ". "] 
;;

let discutons_avec_A type_arg  =  match !natural_language with
    French -> sphv [sps "Discutons"; spb; sps "avec"; spb;
				   spt type_arg; sps ":"] 
|  English -> sphv [sps "Let us discuss"; spb; sps "with"; spb;
				   spt type_arg; sps ":"] 
;;

let utilisons_A arg1  =  match !natural_language with
    French -> sphv [sps (rand ["Utilisons";"Avec";"A l'aide de"]);
		     spb; spt arg1; sps ":"] 
|  English -> sphv [sps (rand ["Let us use";"With";"With the help of"]);
		     spb; spt arg1; sps ":"] 
;;

let selon_les_valeurs_de_A arg1  =  match !natural_language with
    French -> sphv [  (prls ["Selon";"les";"valeurs";"de"]);
                      spb; spt arg1; sps ":"] 
|  English -> sphv [  (prls ["According";"values";"of"]);
                      spb; spt arg1; sps ":"] 
;;

let de_A_on_a arg1  =  match !natural_language with
    French -> sphv [  sps (rand ["De";"Avec";"Grâce à"]); spb; spt arg1; spb;
		      sps (rand ["on a:";"on déduit:";"on obtient:"])]
|  English -> sphv [  sps (rand ["From";"With";"Thanks to"]); spb;
		     spt arg1; spb;
		      sps (rand ["we have:";"we deduce:";"we obtain:"])]
;;


let procedons_par_recurrence_sur_A arg1  =  match !natural_language with
    French ->  sphv [  (prls ["Procédons";"par";"récurrence";"sur"]);
			  spb; spt arg1; sps ":"]
|  English -> sphv [  (prls ["By";"induction";"on"]);
			  spb; spt arg1; sps ":"]
;;


let calculons_la_fonction_F_de_type_T_par_recurrence_sur_son_argument_A 
  nfun tfun narg =  match !natural_language with
    French ->  sphv [  
                    sphv [ prls ["Calculons";"la";"fonction"];
                     spb; sps (string_of_id nfun);spb;
                     prls ["de";"type"];
                     spb; spt tfun;spb;
                     prls ["par";"récurrence";"sur";"son";"argument"];
                     spb; sps (string_of_int narg); sps ":"]
                 ]
|  English ->  sphv [  
                    sphv [ prls ["Let us compute";"the";"function"];
                     spb; sps (string_of_id nfun);spb;
                     prls ["of";"type"];
                     spb; spt tfun;spb;
                     prls ["by";"induction";"on";"its";"argument"];
                     spb; sps (string_of_int narg); sps ":"]
                 ]

;;
let pour_montrer_G_la_valeur_recherchee_est_A g arg1  =
  match !natural_language with
    French ->  sph [sps "Pour";spb;sps "montrer"; spt g; spb;
		     sps ","; spb; sps "choisissons";spb;
		     spt arg1;sps ". " ]
|  English ->  sph [sps "In order to";spb;sps "show"; spt g; spb;
		     sps ","; spb; sps "let us choose";spb;
		     spt arg1;sps ". " ]
;;

let on_se_sert_de_A   arg1  =  match !natural_language with
    French ->  sph [sps "On se sert de";spb ;spt arg1;sps ":" ]
|  English ->  sph [sps "We use";spb ;spt arg1;sps ":" ]
;;


let d_ou_A g  =  match !natural_language with
    French ->  sph [spi; sps "d'où";spb ;spt g;sps ". " ]
|  English -> sph [spi; sps "then";spb ;spt g;sps ". " ]
;;


let coq_le_demontre_seul ()  =  match !natural_language with
    French ->   rand [prls ["Coq";"le";"démontre"; "seul."];
		       sps "Fastoche.";
		     sps "Trop cool"]
|  English -> 	rand [prls ["Coq";"shows";"it"; "alone."];
		       sps "Fingers in the nose."]	      
;;

let de_A_on_deduit_donc_B arg g  =  match !natural_language with
    French -> sph
             [  sps "De"; spb; spt arg; spb; sps "on";spb;
                sps "déduit";spb; sps "donc";spb;  spt g ]
|  English -> sph
             [  sps "From"; spb; spt arg; spb; sps "we";spb;
                sps "deduce";spb; sps "then";spb;  spt g ]
;;

let _A_est_immediat_par_B g arg  =  match !natural_language with
    French -> sph [  spt g;  spb; (prls ["est";"immédiat";"par"]);
                     spb;  spt arg ] 
|  English -> sph [  spt g;  spb; (prls ["is";"immediate";"from"]);
                     spb;  spt arg ] 
;;

let le_resultat_est arg  =  match !natural_language with
    French -> sph [  (prls ["le";"résultat";"est"]);
                    spb; spt arg ] 
|  English -> sph [  (prls ["the";"result";"is"]);
                    spb; spt arg ];;

let on_applique_la_tactique tactic tac =  match !natural_language with
  French -> sphv 
      [ sps "on applique";spb;sps "la tactique"; spb;tactic;spb;tac]
|  English -> sphv 
      [ sps "we apply";spb;sps "the tactic"; spb;tactic;spb;tac]
;;

let de_A_il_vient_B arg g  =  match !natural_language with
    French -> sph
             [  sps "De"; spb; spt arg; spb; 
               sps "il";spb; sps "vient";spb; spt g; sps ". " ] 
|  English -> sph
             [  sps "From"; spb; spt arg; spb; 
               sps "it";spb; sps "comes";spb; spt g; sps ". " ] 
;;

let ce_qui_est_trivial ()  =  match !natural_language with
    French -> sps "Trivial."
|  English -> sps "Trivial."
;;

let en_utilisant_l_egalite_A arg  =  match !natural_language with
    French -> sphv [  sps "En"; spb;sps "utilisant"; spb;
                   sps "l'egalite"; spb; spt arg; sps ","
                  ]
|  English -> sphv [  sps "Using"; spb;
                   sps "the equality"; spb; spt arg; sps ","
                  ]
;;

let simplifions_H_T hyp thyp =  match !natural_language with
    French -> sphv [sps"En simplifiant";spb;sps hyp;spb;sps "on obtient:";
		     spb;spt thyp;sps "."]
|  English ->  sphv [sps"Simplifying";spb;sps hyp;spb;sps "we get:";
		     spb;spt thyp;sps "."]
;;

let grace_a_A_il_suffit_de_montrer_LA arg lg=
  match !natural_language with
    French -> sphv ([sps (rand ["Grâce à";"Avec";"A l'aide de"]);spb;
		      spt arg;sps ",";spb;
		     sps "il suffit";spb; sps "de"; spb;
		      sps (rand["prouver";"montrer";"démontrer"]); spb]
		     @[spv (enumerate (fun x->x) lg)])
|  English -> sphv ([sps (rand ["Thanks to";"With"]);spb;
		      spt arg;sps ",";spb;
		     sps "it suffices";spb; sps "to"; spb;
		      sps (rand["prove";"show"]); spb]
		     @[spv (enumerate (fun x->x) lg)])
;;
let reste_a_montrer_LA lg=
  match !natural_language with
    French -> sphv ([ sps "Il reste";spb; sps "à"; spb;
		      sps (rand["prouver";"montrer";"démontrer"]); spb]
		     @[spv (enumerate (fun x->x) lg)])
|  English -> sphv ([ sps "It remains";spb; sps "to"; spb;
		      sps (rand["prove";"show"]); spb]
		     @[spv (enumerate (fun x->x) lg)])
;;
(*****************************************************************************)
(*
  Traduction des hypothèses.
*)

type n_sort=
      Nprop
    | Nformula
    | Ntype
    | Nfunction
;;

   
let sort_of_type t ts =
   let t=(strip_outer_cast t) in
   if is_Prop t
   then Nprop
   else 
       match ts with
         Prop(Null) -> Nformula
        |_ -> (match (kind_of_term t) with
                Prod(_,_,_) -> Nfunction
               |_ -> Ntype)
;;

let adrel (x,t) e =
    match x with 
      Name(xid) -> Environ.push_rel (x,None,t) e
    | Anonymous -> Environ.push_rel (x,None,t) e

let rec nsortrec vl x = 
     match (kind_of_term x) with
     Prod(n,t,c)->
        let vl = (adrel (n,t) vl) in nsortrec vl c
   | Lambda(n,t,c) ->
        let vl = (adrel (n,t) vl) in nsortrec vl c
   | App(f,args) -> nsortrec vl f
   | Sort(Prop(Null)) -> Prop(Null)
   | Sort(c) -> c
   | Ind(ind) ->
          let (mib,mip) = lookup_mind_specif vl ind in
	  new_sort_in_family (inductive_sort_family mip)
   | Construct(c) ->
          nsortrec vl (mkInd (inductive_of_constructor c))
   | Case(_,x,t,a) 
        -> nsortrec vl x
   | Cast(x,_, t)-> nsortrec vl t
   | Const c  -> nsortrec vl (Typeops.type_of_constant vl c)
   | _ -> nsortrec vl (type_of vl Evd.empty x)
;;
let nsort x =
    nsortrec  (Global.env()) (strip_outer_cast x)
;;

let sort_of_hyp h = 
  (sort_of_type h.hyp_type (nsort h.hyp_full_type))
;;

(* grouper les hypotheses successives de meme type, ou logiques.
   donne une liste de liste *)
let rec group_lhyp lh =
    match lh with
     [] -> []
    |[h] -> [[h]]
    |h::lh ->
      match group_lhyp lh with
       (h1::lh1)::lh2 -> 
        if h.hyp_type=h1.hyp_type
          || ((sort_of_hyp h)=(sort_of_hyp h1) && (sort_of_hyp h1)=Nformula)
        then (h::(h1::lh1))::lh2
        else [h]::((h1::lh1)::lh2)
     |_-> assert false
;;
	
(* ln noms des hypotheses, lt leurs types *)
let natural_ghyp (sort,ln,lt) intro =
  let t=List.hd lt in
  let nh=List.length ln in
  let _ns=List.hd ln in
  match sort with
    Nprop -> soit_A_une_proposition nh ln t
  | Ntype -> soit_X_un_element_de_T nh ln t
  | Nfunction -> soit_F_une_fonction_de_type_T nh ln t
  | Nformula -> 
      sphv ((sps intro)::(enumerate (fun (n,t) -> tag_hypt n t)
			    (List.combine ln lt)))
;;

(* Cas d'une hypothese *)
let natural_hyp h = 
   let ns= string_of_id h.hyp_name in
   let t=h.hyp_type in
   let ts= (nsort h.hyp_full_type) in
   natural_ghyp ((sort_of_type t ts),[ns],[t]) (supposons ())
;;

let rec pr_ghyp lh intro=
     match lh with
       [] -> []
     | [(sort,ln,t)]->
         (match sort with
           Nformula -> [natural_ghyp(sort,ln,t) intro; sps ". "]
         | _ -> [natural_ghyp(sort,ln,t) ""; sps ". "])
     | (sort,ln,t)::lh  ->
       let hp= 
        ([natural_ghyp(sort,ln,t) intro]
         @(match lh with
           [] -> [sps ". "]
          |(sort1,ln1,t1)::lh1  ->
             match sort1 with
               Nformula -> 
                 (let nh=List.length ln in
                     match sort with
                   Nprop -> telle_que nh 
                  |Nfunction -> telle_que nh 
                  |Ntype -> tel_que nh 
                  |Nformula -> [sps ". "])
             | _ -> [sps ". "])) in
        (sphv hp)::(pr_ghyp lh "")
;;

(* traduction d'une liste d'hypotheses groupees. *)
let prnatural_ghyp llh intro=
  if llh=[]
  then spe
  else
    sphv (pr_ghyp (List.map
		     (fun lh ->
		       let h=(List.hd lh) in
		       let sh = sort_of_hyp h in
		       let lhname = (List.map (fun h ->
			 string_of_id h.hyp_name) lh) in
		       let lhtype = (List.map (fun h -> h.hyp_type) lh) in
		       (sh,lhname,lhtype))
		     llh) intro)
;;


(*****************************************************************************)
(*
    Liste des hypotheses.
*)
type type_info_subgoals_hyp=
    All_subgoals_hyp
  | Reduce_hyp
  | No_subgoals_hyp
  | Case_subgoals_hyp of string (* word for introduction *)
	* Term.constr (* variable *)
        * string (* constructor *)
        * int (* arity *)
        * int (* number of constructors *)
  | Case_prop_subgoals_hyp of string (* word for introduction *)
	* Term.constr (* variable *)
        * int (* index of constructor *)
        * int (* arity *)
        * int (* number of constructors *)
  | Elim_subgoals_hyp of Term.constr (* variable *)
        * string (* constructor *)
        * int (* arity *)
        * (string list) (* rec hyp *)
        * int (* number of constructors *)
  | Elim_prop_subgoals_hyp of Term.constr (* variable *)
        * int (* index of constructor *)
        * int (* arity *)
        * (string list) (* rec hyp *)
        * int (* number of constructors *)
;;
let rec nrem l n =
  if n<=0 then l else nrem (list_rem l) (n-1)
;;

let rec nhd l n =
  if n<=0 then [] else (List.hd l)::(nhd (list_rem l) (n-1))
;;

let par_hypothese_de_recurrence () =  match !natural_language with
    French -> sphv [(prls ["par";"hypothèse";"de";"récurrence";","])]
| English -> sphv [(prls ["by";"induction";"hypothesis";","])]
;;

let  natural_lhyp lh hi =
  match hi with
    All_subgoals_hyp -> 
        ( match lh with
          [] -> spe
        |_-> prnatural_ghyp (group_lhyp lh) (supposons ()))
  | Reduce_hyp ->
      (match lh with
	[h] -> simplifions_H_T (string_of_id h.hyp_name) h.hyp_type
      |	_-> spe)
  | No_subgoals_hyp -> spe
  |Case_subgoals_hyp (sintro,var,c,a,ncase) -> (* sintro pas encore utilisee *)
      let s=ref c in
      for i=1 to a do
        let nh=(List.nth lh (i-1)) in
        s:=(!s)^" "^(string_of_id nh.hyp_name);
      done;
      if a>0 then s:="("^(!s)^")";
      sphv [  (if ncase>1
                     then sph[ sps ("-"^(cas ()));spb]
                     else spe);
                    (* spt var;sps "="; *) sps !s; sps ":";
           (prphrases (natural_hyp) (nrem lh a))]
  |Case_prop_subgoals_hyp (sintro,var,c,a,ncase) ->
      prnatural_ghyp (group_lhyp lh) sintro
  |Elim_subgoals_hyp (var,c,a,lhci,ncase) ->
      let nlh = List.length lh in
      let nlhci = List.length lhci in
      let lh0 = ref [] in
      for i=1 to (nlh-nlhci) do
         lh0:=(!lh0)@[List.nth lh (i-1)];
      done;
      let lh=nrem lh (nlh-nlhci) in
      let s=ref c in
      let lh1=ref [] in
      for i=1 to nlhci do
        let targ=(List.nth lhci (i-1))in
        let nh=(List.nth lh (i-1)) in
        if targ="arg" || targ="argrec" 
        then
            (s:=(!s)^" "^(string_of_id nh.hyp_name);
	     lh0:=(!lh0)@[nh])
        else lh1:=(!lh1)@[nh];
      done;
      let introhyprec=
          (if (!lh1)=[] then spe 
           else   par_hypothese_de_recurrence () )
      in          
      if a>0 then s:="("^(!s)^")";
      spv [sphv [(if ncase>1
                     then sph[ sps ("-"^(cas ()));spb]
                     else spe);
                     sps !s; sps ":"]; 
           prnatural_ghyp (group_lhyp !lh0) (supposons ());
           introhyprec;
           prl (natural_hyp) !lh1]
  |Elim_prop_subgoals_hyp (var,c,a,lhci,ncase) ->
      sphv [  (if ncase>1
                     then sph[ sps ("-"^(cas ()));spb;sps (string_of_int c);
                             sps ":";spb]
                     else spe);
           (prphrases (natural_hyp) lh )]

;;

(*****************************************************************************)
(*
    Analyse des tactiques.
*)

let name_tactic = function
  | TacIntroPattern _ -> "Intro"
  | TacAssumption -> "Assumption"
  | _ -> failwith "TODO"
;;

(*
let arg1_tactic tac =
  match tac with
    (Node(_,"Interp",
		(Node(_,_,
		      (Node(_,_,x::_))::_))::_))::_ ->x
  | (Node(_,_,x::_))::_ -> x
  | x::_ -> x
  | _ -> assert false
;;
*)

let arg1_tactic tac = failwith "TODO";;

type type_info_subgoals =
    {ihsg: type_info_subgoals_hyp;
     isgintro : string}
;;

let rec show_goal lh ig g gs =
  match ig with
    "intros" ->
      if lh = []
      then spe
      else show_goal lh "standard" g gs 
  |"standard" ->
      (match (sort_of_type g gs) with
        Nprop -> donnons_une_proposition ()
      | Nformula -> montrons g
      | Ntype -> calculons_un_element_de g
      | Nfunction ->calculons_une_fonction_de_type g)
  | "apply" -> show_goal lh "" g gs
  | "simpl" ->en_simplifiant_on_obtient g
  | "rewrite" -> on_obtient g 
  | "equality" -> reste_a_montrer g
  | "trivial_equality" -> reste_a_montrer g
  | "" -> spe
  |_ -> sph[ sps "A faire ..."; spb; spt g; sps ". " ]
;;

let show_goal2 lh {ihsg=hi;isgintro=ig} g gs s =
  if ig="" && lh = []
  then spe
  else sphv [  show_goal lh ig g gs; sps s]
;;

let imaginez_une_preuve_de () =  match !natural_language with
    French -> "Imaginez une preuve de"
| English -> "Imagine a proof of"
;;

let donnez_un_element_de () =  match !natural_language with
    French -> "Donnez un element de"
| English -> "Give an element of";;

let intro_not_proved_goal gs =
   match gs with
     Prop(Null) -> imaginez_une_preuve_de ()
    |_ -> donnez_un_element_de ()
;;

let first_name_hyp_of_ntree {t_goal={newhyp=lh}}=
  match lh with
   {hyp_name=n}::_ -> n
  | _ -> assert false
;;

let rec find_type x t=
    match (kind_of_term (strip_outer_cast t)) with 
      Prod(y,ty,t) ->
	(match y with
	  Name y -> 
            if x=(string_of_id y) then ty
            else find_type x t
	| _ -> find_type x t)
     |_-> assert false 
;;

(***********************************************************************
Traitement des égalités
*)
(*
let is_equality e =
   match  (kind_of_term e) with
     AppL args ->
       (match (kind_of_term args.(0)) with
	 Const (c,_) ->
	   (match (string_of_sp c) with
	     "Equal" -> true
           | "eq" -> true
	   | "eqT" -> true
	   | "identityT" -> true
	   | _ -> false)
       | _ -> false)
   | _ -> false
;;
*)

let is_equality e =
  let e= (strip_outer_cast e) in
   match  (kind_of_term e) with
     App (f,args) -> (Array.length args) >= 3
   | _ -> false
;;

let terms_of_equality e =
  let e= (strip_outer_cast e) in
  match  (kind_of_term e) with
     App (f,args) -> (args.(1) , args.(2))
    | _ -> assert false
;;

let eq_term = eq_constr;;

let is_equality_tac = function
  | TacAtom (_,
      (TacExtend
	(_,("ERewriteLR"|"ERewriteRL"|"ERewriteLRocc"|"ERewriteRLocc"
	 |"ERewriteParallel"|"ERewriteNormal"
	 |"RewriteLR"|"RewriteRL"|"Replace"),_)
      | TacReduce _
      | TacSymmetry _ | TacReflexivity
      | TacExact _ | TacIntroPattern _ | TacIntroMove _ | TacAuto _)) -> true
  | _ -> false

let equalities_ntree ig ntree =
  let rec equalities_ntree ig ntree =
  if not (is_equality (concl ntree)) 
  then []
  else
    match (proof ntree) with
      Notproved ->  [(ig,ntree)]
    | Proof (tac,ltree) ->
	if is_equality_tac tac
      	then (match ltree with
          [] ->  [(ig,ntree)]
	| t::_ -> let res=(equalities_ntree ig t) in
	          if eq_term (concl ntree) (concl t)
		  then res
		  else (ig,ntree)::res)
	else  [(ig,ntree)]
  in 
  equalities_ntree ig ntree 
;;

let remove_seq_of_terms l =
  let rec remove_seq_of_terms l =    match l with
    a::b::l -> if (eq_term (fst a) (fst b))
    then remove_seq_of_terms (b::l)
    else a::(remove_seq_of_terms (b::l))
  | _ -> l
  in remove_seq_of_terms l
;;

let  list_to_eq l o=
  let switch = fun h h' -> (if o then h else h') in
   match l with
      [a] -> spt (fst a) 
   |  (a,h)::(b,h')::l ->
       let rec list_to_eq h l =
	 match l with
	   [] -> []
	 |  (b,h')::l ->
	     (sph [sps "="; spb; spt b; spb;tag_uselemma (switch h h') spe])
             :: (list_to_eq (switch h' h) l)
       in sph [spt a;  spb;
		 spv ((sph [sps "="; spb; spt b; spb; 
			     tag_uselemma (switch h h') spe])
		      ::(list_to_eq (switch h' h) l))]
  | _ -> assert false
;;

let stde = Global.env;;

let dbize env = Constrintern.interp_constr Evd.empty env;;

(**********************************************************************)
let rec natural_ntree ig ntree =
  let  {t_info=info;
	 t_goal={newhyp=lh;t_concl=g;t_full_concl=gf;t_full_env=ge};
	 t_proof=p} = ntree in
    let leq = List.rev (equalities_ntree ig ntree)  in
    if List.length leq > 1
    then (* Several equalities to treate ... *)
      (
       print_string("Several equalities to treate ...\n");
      let l1 = ref [] in
      let l2 = ref [] in
      List.iter
	(fun (_,ntree) ->
	 let lemma =  match (proof ntree) with
	   Proof (tac,ltree) ->
	     (try (sph [spt (dbize (gLOB ge) (arg1_tactic tac));(* TODO *)
			  (match ltree with
			    [] ->spe
			  | [_] -> spe
			  | _::l -> sphv[sps ": ";
					  prli (natural_ntree 
					    {ihsg=All_subgoals_hyp;
					      isgintro="standard"})
                            		    l])])
	      with _ -> sps "simplification"  )
	 | Notproved -> spe
	 in
 	  let (t1,t2)= terms_of_equality (concl ntree) in
	  l2:=(t2,lemma)::(!l2);
	  l1:=(t1,lemma)::(!l1))
	leq;
      l1:=remove_seq_of_terms !l1;
      l2:=remove_seq_of_terms !l2;
      l2:=List.rev !l2;
      let ltext=ref [] in
      if List.length !l1 > 1
      then (ltext:=(!ltext)@[list_to_eq !l1 true];
	    if List.length !l2 > 1 then
	      (ltext:=(!ltext)@[_et()];
	       ltext:=(!ltext)@[list_to_eq !l2 false]))
      else if List.length !l2 > 1 then ltext:=(!ltext)@[list_to_eq !l2 false];
      if !ltext<>[] then ltext:=[sps (bon_a ()); spv !ltext];
      let (ig,ntree)=(List.hd leq) in
      spv [(natural_lhyp lh ig.ihsg);
	    (show_goal2 lh ig g (nsort gf) "");
	    sph !ltext;
	    
	    natural_ntree {ihsg=All_subgoals_hyp;
                            isgintro=
			    let  (t1,t2)= terms_of_equality (concl ntree) in
			    if eq_term t1 t2
			    then "trivial_equality"
			    else "equality"}
	      ntree]
      	)
    else
    let ntext =
      let gs=nsort gf in
      match p with
   	Notproved ->  spv [ (natural_lhyp lh ig.ihsg);
                            sph [spi; sps (intro_not_proved_goal gs); spb; 
                                  tag_toprove g  ]
			  ]

      | Proof (TacId _,ltree) -> natural_ntree ig (List.hd ltree)
      | Proof (TacAtom (_,tac),ltree) -> 
	 (let ntext = 
	  match tac with
(* Pas besoin de l'argument éventuel de la tactique *)
	    TacIntroPattern _ -> natural_intros ig lh g gs ltree
	  | TacIntroMove _ -> natural_intros ig lh g gs ltree
	  | TacFix (_,n) -> natural_fix ig lh g gs n ltree
	  | TacSplit (_,_,NoBindings) -> natural_split ig lh g gs ge [] ltree
	  | TacSplit(_,_,ImplicitBindings l) -> natural_split ig lh g gs ge (List.map snd l) ltree
	  | TacGeneralize l -> natural_generalize ig lh g gs ge l ltree
	  | TacRight _ -> natural_right ig lh g gs ltree
	  | TacLeft _ -> natural_left ig lh g gs ltree
	  | (* "Simpl" *)TacReduce (r,cl)  ->
	      natural_reduce ig lh g gs ge r cl ltree
	  | TacExtend (_,"InfoAuto",[]) -> natural_infoauto ig lh g gs ltree
	  | TacAuto _ -> natural_auto ig lh g gs ltree
	  | TacExtend (_,"EAuto",_) -> natural_auto ig lh g gs ltree
	  | TacTrivial _ -> natural_trivial ig lh g gs ltree
	  | TacAssumption -> natural_trivial ig lh g gs ltree
	  | TacClear _ -> natural_clear ig lh g gs ltree
(* Besoin de l'argument de la tactique *)
	  | TacSimpleInductionDestruct (true,NamedHyp id) -> 
              natural_induction ig lh g gs ge id ltree false
	  | TacExtend (_,"InductionIntro",[a]) -> 
              let id=(out_gen wit_ident a) in
              natural_induction ig lh g gs ge id ltree true
	  | TacApply (_,false,[c,_],None) ->
              natural_apply ig lh g gs (snd c) ltree
	  | TacExact c -> natural_exact ig lh g gs (snd c) ltree
	  | TacCut c -> natural_cut ig lh g gs (snd c) ltree
	  | TacExtend (_,"CutIntro",[a]) ->
	      let _c = out_gen wit_constr a in
	      natural_cutintro ig lh g gs a ltree
	  | TacCase (_,(c,_)) -> natural_case ig lh g gs ge (snd c) ltree false
	  | TacExtend (_,"CaseIntro",[a]) ->
	      let c = out_gen wit_constr a in
	      natural_case ig lh g gs ge c ltree true
	  | TacElim (_,(c,_),_) ->
	      natural_elim ig lh g gs ge (snd c) ltree false
	  | TacExtend (_,"ElimIntro",[a]) ->
	      let c = out_gen wit_constr a in
	      natural_elim ig lh g gs ge c ltree true
	  | TacExtend (_,"Rewrite",[_;a]) ->
	      let (c,_) = out_gen wit_constr_with_bindings a in
	      natural_rewrite ig lh g gs c ltree
	  | TacExtend (_,"ERewriteRL",[a]) ->
	      let c = out_gen wit_constr a in (* TODO *)
	      natural_rewrite ig lh g gs c ltree
	  | TacExtend (_,"ERewriteLR",[a]) ->
	      let c = out_gen wit_constr a in (* TODO *)
	      natural_rewrite ig lh g gs c ltree
	  |_ -> natural_generic ig lh g gs (sps (name_tactic tac)) (prl sp_tac [tac]) ltree
         in
          ntext (* spwithtac ntext tactic*)
          )
      | Proof _ -> failwith "Don't know what to do with that"
    in   
         if info<>"not_proved"
         then spshrink info ntext
         else ntext
and  natural_generic  ig lh g gs tactic tac ltree =
  spv
    [ (natural_lhyp lh ig.ihsg);
      (show_goal2 lh ig g gs "");
      on_applique_la_tactique tactic tac ;
      (prli(natural_ntree  
	      {ihsg=All_subgoals_hyp;
		isgintro="standard"})
         ltree)
    ]
and natural_clear ig lh g gs ltree = natural_ntree ig (List.hd ltree)
(*
    spv
    [ (natural_lhyp lh ig.ihsg);
      (show_goal2 lh ig g gs "");
      (prl (natural_ntree ig) ltree)
    ]
*)
and natural_intros ig lh g gs ltree =
  spv
         [  (natural_lhyp lh ig.ihsg);
            (show_goal2 lh ig g gs "");
            (prl (natural_ntree  
                {ihsg=All_subgoals_hyp;
                 isgintro="intros"})
                            ltree)
        ]
and natural_apply ig lh g gs arg ltree =
  let lg = List.map concl ltree in
  match lg with
    [] ->
      spv
        [ (natural_lhyp lh ig.ihsg);
	  de_A_il_vient_B arg g  
        ]
  | [sg]->
      spv
        [ (natural_lhyp lh ig.ihsg);
          (show_goal2 lh
	     {ihsg=ig.ihsg; isgintro= if ig.isgintro<>"apply"
	                              then "standard"
	                              else ""}
	     g gs "");
          grace_a_A_il_suffit_de_montrer_LA arg [spt sg];
	  sph [spi ; natural_ntree 
		  {ihsg=All_subgoals_hyp;
		    isgintro="apply"} (List.hd ltree)]
	]       
  | _ ->
      let ln = List.map (fun _ -> new_name()) lg in
      spv
        [ (natural_lhyp lh ig.ihsg);
          (show_goal2 lh
	     {ihsg=ig.ihsg; isgintro= if ig.isgintro<>"apply"
	                              then "standard"
			              else ""}
	     g gs "");
          grace_a_A_il_suffit_de_montrer_LA arg
	    (List.map2 (fun g n -> sph [sps ("("^n^")"); spb; spt g])
	       lg ln);
	  sph [spi; spv (List.map2
			   (fun x n -> sph [sps ("("^n^"):"); spb;
					     natural_ntree 
					       {ihsg=All_subgoals_hyp;
						 isgintro="apply"} x])
			   ltree ln)]
        ]
and natural_rem_goals ltree =
  let lg = List.map concl ltree in
  match lg with
    [] -> spe
  | [sg]->
      spv
        [ reste_a_montrer_LA [spt sg];
	  sph [spi ; natural_ntree 
		  {ihsg=All_subgoals_hyp;
		    isgintro="apply"} (List.hd ltree)]
	]       
  | _ ->
      let ln = List.map (fun _ -> new_name()) lg in
      spv
        [   reste_a_montrer_LA 
	    (List.map2 (fun g n -> sph [sps ("("^n^")"); spb; spt g])
	       lg ln);
	  sph [spi; spv (List.map2
			   (fun x n -> sph [sps ("("^n^"):"); spb;
					     natural_ntree 
					       {ihsg=All_subgoals_hyp;
						 isgintro="apply"} x])
			   ltree ln)]
        ]
and natural_exact ig lh g gs arg ltree =
spv
         [  
             (natural_lhyp lh ig.ihsg);
             (let {ihsg=pi;isgintro=ig}= ig in
               (show_goal2 lh {ihsg=pi;isgintro=""}
                   g gs ""));
             (match gs with
               Prop(Null) -> _A_est_immediat_par_B g arg
              |_ -> le_resultat_est arg)

        ]
and natural_cut ig lh g gs arg ltree =
  spv
         [  (natural_lhyp lh ig.ihsg);
             (show_goal2 lh ig g gs "");
             (prli(natural_ntree  
                    {ihsg=All_subgoals_hyp;isgintro="standard"})
                            (List.rev ltree));
             de_A_on_deduit_donc_B arg g
        ]
and natural_cutintro ig lh g gs arg ltree =
  spv
         [  (natural_lhyp lh ig.ihsg);
             (show_goal2 lh ig g gs "");
             sph [spi;
                    (natural_ntree  
                       {ihsg=All_subgoals_hyp;isgintro=""}
                       (List.nth ltree 1))];
             sph [spi;
                    (natural_ntree  
                       {ihsg=No_subgoals_hyp;isgintro=""}
                       (List.nth ltree 0))]
        ]
and whd_betadeltaiota x = whd_betaiotaevar (Global.env()) Evd.empty x
and type_of_ast s c = type_of (Global.env()) Evd.empty (constr_of_ast c)
and prod_head t =
  match (kind_of_term (strip_outer_cast t)) with 
     Prod(_,_,c) -> prod_head c
(*    |App(f,a) -> f *)
    | _ -> t
and string_of_sp sp = string_of_id (basename sp)
and constr_of_mind mip i =
  (string_of_id mip.mind_consnames.(i-1))
and arity_of_constr_of_mind env indf i =
     (get_constructors env indf).(i-1).cs_nargs
and gLOB ge = Global.env_of_context ge  (* (Global.env()) *)

and natural_case ig lh g gs ge arg1 ltree with_intros =
 let env= (gLOB ge) in
 let targ1 = prod_head (type_of env Evd.empty arg1) in
 let IndType (indf,targ) = find_rectype env Evd.empty targ1 in
 let ncti= Array.length(get_constructors env indf) in
 let (ind,_) = dest_ind_family indf in
 let (mib,mip) = lookup_mind_specif env ind in
 let ti =(string_of_id mip.mind_typename) in
 let type_arg= targ1 (* List.nth targ (mis_index dmi)*)  in
 if  ncti<>1
(* Zéro ou Plusieurs constructeurs *)
 then (   
   spv
         [  (natural_lhyp lh ig.ihsg);
             (show_goal2 lh ig g gs "");
             (match (nsort targ1) with
               Prop(Null) ->
		 (match ti with
		   "or" ->  discutons_avec_A type_arg
                 | _ -> utilisons_A arg1)
             |_ -> selon_les_valeurs_de_A arg1);
            (let ci=ref 0 in
             (prli
                 (fun treearg -> ci:=!ci+1;
                      let nci=(constr_of_mind mip !ci) in
                      let aci=if with_intros
			      then (arity_of_constr_of_mind env indf !ci)
		              else 0 in
                      let ici= (!ci) in
                    sph[ (natural_ntree  
                          {ihsg=
                             (match (nsort targ1) with
                                Prop(Null) ->
                                   Case_prop_subgoals_hyp (supposons (),arg1,ici,aci,
                                     (List.length ltree))
                               |_-> Case_subgoals_hyp ("",arg1,nci,aci,
                                                (List.length ltree)));
                           isgintro= if with_intros then "" else "standard"}
                          treearg)
                    ])
                  (nrem ltree ((List.length ltree)- ncti))));
	    (sph [spi; (natural_rem_goals
			  (nhd ltree ((List.length ltree)- ncti)))])
         ] )
(* Cas d'un seul constructeur *)
     else (  

     spv
     [ (natural_lhyp lh ig.ihsg);
       (show_goal2 lh ig g gs "");
       de_A_on_a arg1;
       (let treearg=List.hd ltree in
       let nci=(constr_of_mind mip 1) in
       let aci=
	 if with_intros
         then (arity_of_constr_of_mind env indf 1)
	 else 0 in
       let _ici= 1 in
       sph[ (natural_ntree  
               {ihsg=
                 (match (nsort targ1) with
                   Prop(Null) ->
                     Case_prop_subgoals_hyp ("",arg1,1,aci,
					     (List.length ltree))
                 |_-> Case_subgoals_hyp ("",arg1,nci,aci,
                                         (List.length ltree)));
                 isgintro=""}
               treearg)
          ]);
       (sph [spi; (natural_rem_goals
		     (nhd ltree ((List.length ltree)- 1)))])
     ] 
     )
(*    with _ ->natural_generic ig lh g gs (sps "Case")  (spt arg1) ltree *)

(*****************************************************************************)
(*
   Elim
*)
and prod_list_var t =
   match (kind_of_term (strip_outer_cast t)) with 
      Prod(_,t,c) -> t::(prod_list_var c)
     |_ -> []
and  hd_is_mind t ti =
    try (let env = Global.env() in
         let IndType (indf,targ) = find_rectype env Evd.empty t in
	 let _ncti= Array.length(get_constructors env indf) in
	 let (ind,_) = dest_ind_family indf in
         let (mib,mip) = lookup_mind_specif env ind in
	 (string_of_id mip.mind_typename) = ti)
    with _ -> false
and mind_ind_info_hyp_constr indf c =
  let env = Global.env() in
  let (ind,_) = dest_ind_family indf in
  let (mib,mip) = lookup_mind_specif env ind in
  let _p = mib.mind_nparams in
  let a = arity_of_constr_of_mind env indf c in
  let lp=ref (get_constructors env indf).(c).cs_args in
  let lr=ref [] in
  let ti = (string_of_id mip.mind_typename) in
  for i=1 to a do
     match !lp with
     ((_,_,t)::lp1)->
       if hd_is_mind t ti
       then (lr:=(!lr)@["argrec";"hyprec"]; lp:=List.tl lp1)
       else (lr:=(!lr)@["arg"];lp:=lp1)
     |  _ -> raise (Failure "mind_ind_info_hyp_constr")
  done;
  !lr
(*
 mind_ind_info_hyp_constr "le" 2;;
donne  ["arg"; "argrec"] 
mind_ind_info_hyp_constr "le" 1;;
donne []
 mind_ind_info_hyp_constr "nat" 2;;
donne ["argrec"]
*)

and natural_elim ig lh g gs ge arg1 ltree with_intros=
 let env= (gLOB ge) in
 let targ1 = prod_head (type_of env Evd.empty arg1) in
 let IndType (indf,targ) = find_rectype env Evd.empty targ1 in
 let ncti= Array.length(get_constructors env indf) in
 let (ind,_) = dest_ind_family indf in
 let (mib,mip) = lookup_mind_specif env ind in
 let _ti =(string_of_id mip.mind_typename) in
 let _type_arg=targ1 (* List.nth targ (mis_index dmi) *) in
  spv
         [  (natural_lhyp lh ig.ihsg);
             (show_goal2 lh ig g gs "");
             (match (nsort targ1) with
               Prop(Null) -> utilisons_A arg1
	     |_ ->procedons_par_recurrence_sur_A arg1);
            (let ci=ref 0 in
             (prli
                 (fun treearg -> ci:=!ci+1;
                      let nci=(constr_of_mind mip !ci) in
                      let aci=(arity_of_constr_of_mind env indf !ci) in
                      let hci=
			if with_intros
			then mind_ind_info_hyp_constr indf  !ci
		      	else [] in
                      let ici= (!ci) in
                    sph[ (natural_ntree  
                          {ihsg=
                             (match (nsort targ1) with
                                Prop(Null) ->
                                   Elim_prop_subgoals_hyp (arg1,ici,aci,hci,
                                     (List.length ltree))
                               |_-> Elim_subgoals_hyp (arg1,nci,aci,hci,
                                                (List.length ltree)));
                           isgintro= ""}
                          treearg)
                    ])
                  (nhd ltree ncti)));
	    (sph [spi; (natural_rem_goals (nrem ltree ncti))])
        ]
(* )
  with _ ->natural_generic ig lh g gs (sps "Elim")  (spt arg1) ltree *)

(*****************************************************************************)
(*
   InductionIntro n
*) 
and natural_induction ig lh g gs ge arg2 ltree with_intros=
 let env = (gLOB (g_env (List.hd ltree))) in
 let arg1= mkVar arg2 in
 let targ1 = prod_head (type_of env Evd.empty arg1) in
 let IndType (indf,targ) = find_rectype env Evd.empty targ1 in
 let _ncti= Array.length(get_constructors env indf) in
 let (ind,_) = dest_ind_family indf in
 let (mib,mip) = lookup_mind_specif env ind in
 let _ti =(string_of_id mip.mind_typename) in
 let _type_arg= targ1(*List.nth targ (mis_index dmi)*) in

 let lh1= hyps (List.hd ltree) in (* la liste des hyp jusqu'a n *)
 (* on les enleve des hypotheses des sous-buts *)
 let ltree = List.map
     (fun {t_info=info;
	    t_goal={newhyp=lh;t_concl=g;t_full_concl=gf;t_full_env=ge};
	    t_proof=p} ->
	  {t_info=info;
	    t_goal={newhyp=(nrem lh (List.length lh1));
		     t_concl=g;t_full_concl=gf;t_full_env=ge};
	    t_proof=p}) ltree in
 spv
   [  (natural_lhyp lh ig.ihsg);
             (show_goal2 lh ig g gs "");
	   (natural_lhyp lh1 All_subgoals_hyp);
             (match (print_string "targ1------------\n";(nsort targ1)) with
               Prop(Null) -> utilisons_A arg1
	     |_ -> procedons_par_recurrence_sur_A arg1);
            (let ci=ref 0 in
             (prli
                 (fun treearg -> ci:=!ci+1;
                      let nci=(constr_of_mind mip !ci) in
                      let aci=(arity_of_constr_of_mind env indf !ci) in
                      let hci= 
			if with_intros
			then mind_ind_info_hyp_constr indf  !ci
		      	else [] in
                      let ici= (!ci) in
                    sph[ (natural_ntree  
                          {ihsg=
                             (match (nsort targ1) with
                                Prop(Null) ->
                                   Elim_prop_subgoals_hyp (arg1,ici,aci,hci,
                                     (List.length ltree))
                               |_-> Elim_subgoals_hyp (arg1,nci,aci,hci,
                                                (List.length ltree)));
                           isgintro= "standard"}
                          treearg)
                    ])
                  ltree))
        ]
(************************************************************************)
(* Points fixes *)

and natural_fix ig lh g gs narg ltree =
  let {t_info=info;
	t_goal={newhyp=lh1;t_concl=g1;t_full_concl=gf1;
                   t_full_env=ge1};t_proof=p1}=(List.hd ltree) in
  match lh1 with
     {hyp_name=nfun;hyp_type=tfun}::lh2 ->
  let ltree=[{t_info=info;
	       t_goal={newhyp=lh2;t_concl=g1;t_full_concl=gf1;
                          t_full_env=ge1};
	       t_proof=p1}] in
  spv
         [  (natural_lhyp lh ig.ihsg);
             calculons_la_fonction_F_de_type_T_par_recurrence_sur_son_argument_A  nfun tfun narg;
             (prli(natural_ntree  
                   {ihsg=All_subgoals_hyp;isgintro=""})
                            ltree)
        ]
   | _ -> assert false
and natural_reduce ig lh g gs ge mode la ltree =
  match la with
    {onhyps=Some[]} when la.concl_occs <> no_occurrences_expr -> 
      spv
        [  (natural_lhyp lh ig.ihsg);
          (show_goal2 lh ig g gs ""); 
          (prl (natural_ntree 
		  {ihsg=All_subgoals_hyp;isgintro="simpl"})
             ltree)
        ]
  | {onhyps=Some[hyp]} when la.concl_occs = no_occurrences_expr ->
      spv
        [  (natural_lhyp lh ig.ihsg);
          (show_goal2 lh ig g gs ""); 
          (prl (natural_ntree 
		  {ihsg=Reduce_hyp;isgintro=""})
             ltree)
        ]
  | _ -> assert false
and natural_split ig lh g gs ge la ltree =
  match la with
    [arg] -> 
      let _env= (gLOB ge) in
      let arg1= (*dbize _env*) arg in
      spv
      	[ (natural_lhyp lh ig.ihsg);
          (show_goal2 lh ig g gs ""); 
	  pour_montrer_G_la_valeur_recherchee_est_A  g arg1;
          (prl (natural_ntree 
		  {ihsg=All_subgoals_hyp;isgintro="standard"})
             ltree)
        ]
  | [] ->
      spv
        [ (natural_lhyp lh ig.ihsg);
          (prli(natural_ntree  
                  {ihsg=All_subgoals_hyp;isgintro="standard"})
             ltree)
        ]
  | _ -> assert false
and natural_generalize ig lh g gs ge la ltree =
  match la with
    [(_,(_,arg)),_] ->
      let _env= (gLOB ge) in
      let arg1= (*dbize env*) arg in
      let _type_arg=type_of (Global.env()) Evd.empty arg in
(*      let type_arg=type_of_ast ge arg in*)
      spv
      	[ (natural_lhyp lh ig.ihsg);
          (show_goal2 lh ig g gs ""); 
	  on_se_sert_de_A   arg1;
          (prl (natural_ntree 
		  {ihsg=All_subgoals_hyp;isgintro=""})
             ltree)
        ]
    | _ -> assert false
and natural_right ig lh g gs ltree =
  spv
         [ (natural_lhyp lh ig.ihsg);
            (prli(natural_ntree  
                {ihsg=All_subgoals_hyp;isgintro="standard"})
                            ltree); 
            d_ou_A g  
        ]
and natural_left ig lh g gs ltree =
  spv
         [ (natural_lhyp lh ig.ihsg);
            (prli(natural_ntree  
                {ihsg=All_subgoals_hyp;isgintro="standard"})
                            ltree); 
             d_ou_A g  
        ]
and natural_auto ig lh g gs ltree =
  match ig.isgintro with
   "trivial_equality" -> spe
  | _ -> 
      if ltree=[]
      then sphv [(natural_lhyp lh ig.ihsg);
		  (show_goal2 lh ig g gs "");
		  coq_le_demontre_seul ()]
      else spv [(natural_lhyp lh ig.ihsg);
		 (show_goal2 lh ig g gs "");
		 (prli (natural_ntree {ihsg=All_subgoals_hyp;isgintro=""}
			  )
                    ltree)]
and natural_infoauto ig lh g gs ltree =
 match ig.isgintro with
   "trivial_equality" ->
     spshrink "trivial_equality"
       (natural_ntree {ihsg=All_subgoals_hyp;isgintro="standard"}
		 (List.hd ltree))
  | _ ->   sphv [(natural_lhyp lh ig.ihsg);
	 (show_goal2 lh ig g gs "");
	 coq_le_demontre_seul ();
       spshrink "auto"
		    (sph [spi;
		       (natural_ntree
			  {ihsg=All_subgoals_hyp;isgintro=""}
			  (List.hd ltree))])]
and natural_trivial ig lh g gs ltree =
  if ltree=[]
  then sphv [(natural_lhyp lh ig.ihsg);
	      (show_goal2 lh ig g gs "");
	      ce_qui_est_trivial () ]
  else spv [(natural_lhyp lh ig.ihsg);
	     (show_goal2 lh ig g gs ". ");
            (prli(natural_ntree  
                      {ihsg=All_subgoals_hyp;isgintro="standard"})
                            ltree)]
and natural_rewrite ig lh g gs arg ltree =
  spv
         [  (natural_lhyp lh ig.ihsg);
             (show_goal2 lh ig g gs "");
             en_utilisant_l_egalite_A arg;
            (prli(natural_ntree  
                 {ihsg=All_subgoals_hyp;isgintro="rewrite"})
                            ltree)
        ]
;;

let natural_ntree_path ig g =
  Random.init(0);
        natural_ntree ig g
;;

let show_proof lang gpath =
  (match lang with
     "fr" -> natural_language:=French
    |"en" -> natural_language:=English
    | _ -> natural_language:=English);
  path:=List.rev gpath;
  name_count:=0;
  let ntree=(get_nproof ()) in
  let {t_info=i;t_goal=g;t_proof=p} =ntree in
  root_of_text_proof
    (sph [(natural_ntree_path {ihsg=All_subgoals_hyp;
				isgintro="standard"}
	                      {t_info="not_proved";t_goal=g;t_proof=p});
           spr])
    ;;

let show_nproof path =
  pp (sp_print (sph [spi; show_proof "fr" path]));;

vinterp_add "ShowNaturalProof"
	    (fun _ ->
		 (fun () ->show_nproof[];()));;

(***********************************************************************
debug sous cygwin:

PATH=/usr/local/bin:/usr/bin:$PATH
COQTOP=d:/Tools/coq-7avril
CAMLLIB=/usr/local/lib/ocaml
CAMLP4LIB=/usr/local/lib/camlp4
export CAMLLIB
export COQTOP
export CAMLP4LIB 
cd d:/Tools/pcoq/src/text
d:/Tools/coq-7avril/bin/coqtop.byte.exe -I /cygdrive/D/Tools/pcoq/src/abs_syntax  -I /cygdrive/D/Tools/pcoq/src/text -I /cygdrive/D/Tools/pcoq/src/coq -I /cygdrive/D/Tools/pcoq/src/pbp -I /cygdrive/D/Tools/pcoq/src/dad -I /cygdrive/D/Tools/pcoq/src/history

 
 
Lemma l1: (A, B : Prop) A \/ B -> B ->  A.
Intros.
Elim H.
Auto.
Qed.
 

Drop.

#use "/cygdrive/D/Tools/coq-7avril/dev/base_include";;
#load "xlate.cmo";;
#load "translate.cmo";;
#load "showproof_ct.cmo";;
#load "showproof.cmo";;
#load "pbp.cmo";;
#load "debug_tac.cmo";;
#load "name_to_ast.cmo";;
#load "paths.cmo";;
#load "dad.cmo";;
#load "vtp.cmo";;
#load "history.cmo";;
#load "centaur.cmo";;
Xlate.set_xlate_mut_stuff Centaur.globcv;;
Xlate.declare_in_coq();;

#use "showproof.ml";;

let pproof x = pP (sp_print x);;
Pp_control.set_depth_boxes 100;;
#install_printer  pproof;;

ep();;
let bidon = ref (constr_of_string "O");; 

#trace to_nproof;;
***********************************************************************)
let ep()=show_proof "fr" [];;
