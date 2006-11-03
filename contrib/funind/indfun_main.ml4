(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*i camlp4deps: "parsing/grammar.cma" i*)
open Term
open Names
open Pp
open Topconstr
open Indfun_common 
open Indfun
open Genarg
open Pcoq
open Tacticals

let pr_binding prc = function
  | loc, Rawterm.NamedHyp id, c -> hov 1 (Ppconstr.pr_id id ++ str " := " ++ cut () ++ prc c)
  | loc, Rawterm.AnonHyp n, c -> hov 1 (int n ++ str " := " ++ cut () ++ prc c)

let pr_bindings prc prlc = function
  | Rawterm.ImplicitBindings l ->
      brk (1,1) ++ str "with" ++ brk (1,1) ++
      Util.prlist_with_sep spc prc l
  | Rawterm.ExplicitBindings l ->
      brk (1,1) ++ str "with" ++ brk (1,1) ++ 
        Util.prlist_with_sep spc (fun b -> str"(" ++ pr_binding prlc b ++ str")") l
  | Rawterm.NoBindings -> mt ()


let pr_with_bindings prc prlc (c,bl) =
  prc c ++ hv 0 (pr_bindings prc prlc bl)


let pr_fun_ind_using  prc prlc _ opt_c = 
  match opt_c with
    | None -> mt ()
    | Some (p,b) -> spc () ++ hov 2 (str "using" ++ spc () ++ pr_with_bindings prc prlc (p,b))


ARGUMENT EXTEND fun_ind_using
  TYPED AS constr_with_bindings_opt
  PRINTED BY pr_fun_ind_using
| [ "using" constr_with_bindings(c) ] -> [ Some c ]
| [ ] -> [ None ]
END


TACTIC EXTEND newfuninv
   [ "functional" "inversion"  quantified_hypothesis(hyp) reference_opt(fname) ] -> 
     [
       Invfun.invfun hyp fname
     ]
END


let pr_intro_as_pat prc _ _ pat = 
  match pat with 
    | Some pat -> spc () ++ str "as" ++ spc () ++ pr_intro_pattern pat
    | None -> mt ()


ARGUMENT EXTEND with_names TYPED AS intro_pattern_opt PRINTED BY pr_intro_as_pat
|   [ "as"  simple_intropattern(ipat) ] -> [ Some ipat ] 
| []  ->[ None ] 
END




TACTIC EXTEND newfunind
   ["functional" "induction" ne_constr_list(cl) fun_ind_using(princl) with_names(pat)] -> 
     [ 
       let pat = 
	 match pat with 
	   | None -> IntroAnonymous
	   | Some pat -> pat
       in
       let c = match cl with 
	 | [] -> assert false
	 | [c] -> c 
	 | c::cl -> applist(c,cl)
       in 
       functional_induction true c  princl pat ]
END
(***** debug only ***)
TACTIC EXTEND snewfunind
   ["soft" "functional" "induction" ne_constr_list(cl) fun_ind_using(princl) with_names(pat)] -> 
     [ 
       let pat = 
	 match pat with 
	   | None -> IntroAnonymous
	   | Some pat -> pat
       in
       let c = match cl with 
	 | [] -> assert false
	 | [c] -> c 
	 | c::cl -> applist(c,cl)
       in 
       functional_induction false c princl pat ]
END


let pr_constr_coma_sequence prc _ _ = Util.prlist_with_sep Util.pr_coma prc

ARGUMENT EXTEND constr_coma_sequence'
  TYPED AS constr_list
  PRINTED BY pr_constr_coma_sequence
| [ constr(c) "," constr_coma_sequence'(l) ] -> [ c::l ]
| [ constr(c) ] -> [ [c] ]
END

let pr_auto_using prc _prlc _prt = Pptactic.pr_auto_using prc

ARGUMENT EXTEND auto_using'
  TYPED AS constr_list
  PRINTED BY pr_auto_using
| [ "using" constr_coma_sequence'(l) ] -> [ l ]
| [ ] -> [ [] ]
END

VERNAC ARGUMENT EXTEND rec_annotation2
  [ "{"  "struct" ident(id)  "}"] -> [ Struct id ]
| [ "{" "wf" constr(r) ident_opt(id) auto_using'(l) "}" ] -> [ Wf(r,id,l) ]
| [ "{" "measure" constr(r) ident_opt(id) auto_using'(l) "}" ] -> [ Mes(r,id,l) ] 
END


VERNAC ARGUMENT EXTEND binder2
    [ "(" ne_ident_list(idl) ":" lconstr(c)  ")"] ->
     [
       LocalRawAssum (List.map (fun id -> (Util.dummy_loc,Name id)) idl,c) ]
END


VERNAC ARGUMENT EXTEND rec_definition2
 [ ident(id)  binder2_list( bl)
     rec_annotation2_opt(annot) ":" lconstr( type_)
	":=" lconstr(def)] ->
    [let names = List.map snd (Topconstr.names_of_local_assums bl) in
     let check_one_name () =
       if List.length names > 1 then
         Util.user_err_loc
           (Util.dummy_loc,"Function",
            Pp.str "the recursive argument needs to be specified");
     in
     let check_exists_args an =
       try 
	 let id = match an with 
	   | Struct id -> id | Wf(_,Some id,_) -> id | Mes(_,Some id,_) -> id 
	   | Wf(_,None,_) | Mes(_,None,_) -> failwith "check_exists_args" 
	 in 
	 (try ignore(Util.list_index (Name id) names - 1); annot
	  with Not_found ->  Util.user_err_loc
            (Util.dummy_loc,"Function",
             Pp.str "No argument named " ++ Nameops.pr_id id)
	 )
       with Failure "check_exists_args" ->  check_one_name ();annot
     in
     let ni =
       match annot with
         | None ->
             annot
	 | Some an ->
	     check_exists_args an
     in
     (id, ni, bl, type_, def) ]
      END


VERNAC ARGUMENT EXTEND rec_definitions2
| [ rec_definition2(rd) ] -> [ [rd] ]
| [ rec_definition2(hd) "with" rec_definitions2(tl) ] -> [ hd::tl ]
END


VERNAC COMMAND EXTEND Function
   ["Function" rec_definitions2(recsl)] ->
	[ 
	  do_generate_principle false  recsl; 
	  
	]
END


VERNAC ARGUMENT EXTEND fun_scheme_arg
| [ ident(princ_name) ":=" "Induction" "for" reference(fun_name) "Sort" sort(s) ] -> [ (princ_name,fun_name,s) ] 
END 

VERNAC ARGUMENT EXTEND fun_scheme_args
| [ fun_scheme_arg(fa) ] -> [ [fa] ] 
| [ fun_scheme_arg(fa) "with" fun_scheme_args(fas) ] -> [fa::fas]
END 

VERNAC COMMAND EXTEND NewFunctionalScheme
   ["Functional" "Scheme" fun_scheme_args(fas) ] ->
    [
      try 
	Functional_principles_types.build_scheme fas
      with Functional_principles_types.No_graph_found -> 
	match fas with 
	  | (_,fun_name,_)::_ -> 
	      begin
		make_graph (Nametab.global fun_name);
		try Functional_principles_types.build_scheme fas
		with Functional_principles_types.No_graph_found -> 
		  Util.error ("Cannot generate induction principle(s)")
	      end
	  | _ -> assert false (* we can only have non empty  list *)
    ]
END
(***** debug only ***)

VERNAC COMMAND EXTEND NewFunctionalCase
   ["Functional" "Case" fun_scheme_arg(fas) ] ->
    [
      Functional_principles_types.build_case_scheme fas
    ]
END

(***** debug only ***)
VERNAC COMMAND EXTEND GenerateGraph 
["Generate" "graph" "for" reference(c)] -> [ make_graph (Nametab.global c) ]
END





(* FINDUCTION *)

(* comment this line to see debug msgs *)
let msg x = () ;; let pr_lconstr c = str ""
  (* uncomment this to see debugging *)
let prconstr c =  msg (str"  " ++ Printer.pr_lconstr c ++ str"\n")
let prlistconstr lc = List.iter prconstr lc
let prstr s = msg(str s)
let prNamedConstr s c = 
  begin
    msg(str "");
    msg(str(s^"==>\n ") ++ Printer.pr_lconstr c ++ str "\n<==\n");
    msg(str "");
  end



(** Information about an occurrence of a function call (application)
    inside a term. *)
type fapp_info = {
  fname: constr; (** The function applied *)
  largs: constr list; (** List of arguments *)
  free: bool; (** [true] if all arguments are debruijn free *)
  max_rel: int; (** max debruijn index in the funcall *)
  onlyvars: bool (** [true] if all arguments are variables (and not debruijn) *)
}


(** [constr_head_match(a b c) a] returns true, false otherwise. *)
let constr_head_match u t=
  if isApp u 
  then 
    let uhd,args= destApp u in
    uhd=t
  else false

(** [hdMatchSub inu t] returns the list of occurrences of [t] in
    [inu]. DeBruijn are not pushed, so some of them may be unbound in
    the result. *)
let rec hdMatchSub inu (test: constr -> bool) : fapp_info list =
  let subres = 
    match kind_of_term inu with
      | Lambda (nm,tp,cstr) | Prod (nm,tp,cstr) -> 
	  hdMatchSub tp test @ hdMatchSub (lift 1 cstr) test
      | Fix (_,(lna,tl,bl))  -> (* not sure Fix is correct *)
	  Array.fold_left 
	    (fun acc cstr -> acc @ hdMatchSub (lift (Array.length tl) cstr) test) 
	    [] bl
      | _ -> (* Cofix will be wrong *)
	  fold_constr 
	    (fun l cstr -> 
	      l @ hdMatchSub cstr test) [] inu in 
  if not (test inu) then subres
  else
    let f,args = decompose_app inu in
    let freeset = Termops.free_rels inu in
    let max_rel = try Util.Intset.max_elt freeset with Not_found -> -1 in
    {fname = f; largs = args; free = Util.Intset.is_empty freeset;
    max_rel = max_rel; onlyvars = List.for_all isVar args } 
    ::subres

let mkEq typ c1 c2 = 
  mkApp (Coqlib.build_coq_eq(),[| typ; c1; c2|])


let poseq_unsafe idunsafe cstr gl =
  let typ = Tacmach.pf_type_of gl cstr in
  tclTHEN
    (Tactics.letin_tac true (Name idunsafe) cstr allClauses)
    (tclTHENFIRST 
      (Tactics.assert_as true IntroAnonymous (mkEq typ (mkVar idunsafe) cstr)) 
      Tactics.reflexivity)
    gl
  

let poseq id cstr gl =
  let x = Tactics.fresh_id [] id gl in
  poseq_unsafe x cstr gl

(* dirty? *)

let list_constr_largs = ref []

let rec poseq_list_ids_rec lcstr gl =
  match lcstr with
    | [] -> tclIDTAC gl
    | c::lcstr' -> 
	match kind_of_term c with
	  | Var _ -> 
	      (list_constr_largs:=c::!list_constr_largs ; poseq_list_ids_rec lcstr' gl)
	  | _ -> 
	      let _ = prstr "c = " in
	      let _ = prconstr c in
	      let _ = prstr "\n" in
	      let typ = Tacmach.pf_type_of gl c in
	      let cname = Termops.id_of_name_using_hdchar (Global.env()) typ Anonymous in
	      let x = Tactics.fresh_id [] cname gl in
	      let _ = list_constr_largs:=mkVar x :: !list_constr_largs in
	      let _ = prstr " list_constr_largs = " in
	      let _ = prlistconstr !list_constr_largs in
	      let _ = prstr "\n" in

	      tclTHEN
		(poseq_unsafe x c)
		(poseq_list_ids_rec lcstr')
		gl

let poseq_list_ids lcstr gl = 
  let _ = list_constr_largs := [] in
  poseq_list_ids_rec lcstr gl

(** [find_fapp test g] returns the list of [app_info] of all calls to
    functions that satisfy [test] in the conclusion of goal g. Trivial
    repetition (not modulo conversion) are deleted. *)
let find_fapp (test:constr -> bool) g : fapp_info list = 
  let pre_res = hdMatchSub (Tacmach.pf_concl g) test in
  let res = 
    List.fold_right (fun x acc -> if List.mem x acc then acc else x::acc) pre_res [] in
  (prlistconstr (List.map (fun x -> applist (x.fname,x.largs)) res);
  res)



(** [finduction id filter g] tries to apply functional induction on
    an occurence of function [id] in the conclusion of goal [g]. If
    [id]=[None] then calls to any function are selected. In any case
    [heuristic] is used to select the most pertinent occurrence. *)
let finduction (oid:identifier option) (heuristic: fapp_info list -> fapp_info list)
    (nexttac:Proof_type.tactic) g =
  let test = match oid with
    | Some id -> 
	let idconstr = mkConst (const_of_id id) in
	(fun u -> constr_head_match u idconstr) (* select only id *)
    | None -> (fun u -> isApp u) in (* select calls to any function *)
  let info_list = find_fapp test g in
  let ordered_info_list = heuristic info_list in
  prlistconstr (List.map (fun x -> applist (x.fname,x.largs)) ordered_info_list); 
  if List.length ordered_info_list = 0 then Util.error "function not found in goal\n";
  let taclist: Proof_type.tactic list = 
    List.map 
      (fun info ->
	(tclTHEN
	  (tclTHEN (poseq_list_ids info.largs)
	    (
	      fun gl -> 
		  (functional_induction 
		    true (applist (info.fname, List.rev !list_constr_largs)) 
		    None IntroAnonymous) gl)) 
	  nexttac)) ordered_info_list in
  (* we try each (f t u v) until one does not fail *)
  (* TODO: try also to mix functional schemes *)
  tclFIRST taclist g




(** [chose_heuristic oi x] returns the heuristic for reordering
    (and/or forgetting some elts of) a list of occurrences of
     function calls infos to chose first with functional induction. *)
let chose_heuristic (oi:int option) : fapp_info list -> fapp_info list =
  match oi with
    | Some i -> (fun l -> [ List.nth l (i-1) ]) (* occurrence was given by the user *)
    | None -> 
	(* Default heuristic: put first occurrences where all arguments
	   are *bound* (meaning already introduced) variables *)
	let ordering x y =
	  if x.free && x.onlyvars && y.free && y.onlyvars then 0 (* both pertinent *)
	  else if x.free && x.onlyvars then -1
	  else if y.free && y.onlyvars then 1
	  else 0 (* both not pertinent *)
	in
	List.sort ordering



TACTIC EXTEND finduction
    ["finduction" ident(id) natural_opt(oi)] -> 
      [ 
	match oi with
	  | Some(n) when n<=0 -> Util.error "numerical argument must be > 0"
	  | _ -> 
	      let heuristic = chose_heuristic oi in
	      finduction (Some id) heuristic tclIDTAC
      ]
END



TACTIC EXTEND fauto
    [ "fauto" tactic(tac)] -> 
      [
	let heuristic = chose_heuristic None in
	finduction None heuristic (snd tac)
      ]
  |
    [ "fauto" ] -> 
      [
	let heuristic = chose_heuristic None in
	finduction None heuristic tclIDTAC
      ]

END


TACTIC EXTEND poseq
  [ "poseq" ident(x) constr(c) ] -> 
      [ poseq x c ]
END

VERNAC COMMAND EXTEND Showindinfo
  [ "showindinfo" ident(x) ] -> [ Merge.showind x ]
END

VERNAC COMMAND EXTEND MergeFunind
  [ "Mergeschemes" lconstr(c) "with" lconstr(c') "using" ident(id) ] -> 
     [ 
       let c1 = Constrintern.interp_constr Evd.empty (Global.env()) c in
       let c2 = Constrintern.interp_constr Evd.empty (Global.env()) c' in
       let id1,args1 = 
	 try 
	   let hd,args = destApp c1 in
	   if Term.isInd hd then hd , args 
	   else raise (Util.error "Ill-formed (fst) argument")
	 with Invalid_argument _ 
	     -> Util.error ("Bad argument form for merging schemes") in
       let id2,args2 = 
	 try
 	   let hd,args = destApp c2 in
	   if isInd hd then hd , args 
	   else raise (Util.error "Ill-formed (snd) argument")
	 with Invalid_argument _ 
	     -> Util.error ("Bad argument form for merging schemes") in
       (* TOFO: enlever le ignore et declarer l'inductif *)
       ignore(Merge.merge c1 c2 args1 args2 id)
     ]
END
