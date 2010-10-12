(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*i camlp4deps: "parsing/grammar.cma" i*)
open Util
open Term
open Names
open Pp
open Topconstr
open Indfun_common
open Indfun
open Genarg
open Pcoq
open Tacticals
open Constr

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
    | Some b -> spc () ++ hov 2 (str "using" ++ spc () ++ pr_with_bindings prc prlc b)

(* Duplication of printing functions because "'a with_bindings" is
   (internally) not uniform in 'a: indeed constr_with_bindings at the
   "typed" level has type "open_constr with_bindings" instead of
   "constr with_bindings"; hence, its printer cannot be polymorphic in
   (prc,prlc)... *)

let pr_with_bindings_typed prc prlc (c,bl) =
  prc c ++
  hv 0 (pr_bindings prc prlc bl)

let pr_fun_ind_using_typed prc prlc _ opt_c =
  match opt_c with
    | None -> mt ()
    | Some b -> spc () ++ hov 2 (str "using" ++ spc () ++ pr_with_bindings_typed prc prlc b.Evd.it)


ARGUMENT EXTEND fun_ind_using
  TYPED AS constr_with_bindings_opt
  PRINTED BY pr_fun_ind_using_typed
  RAW_TYPED AS constr_with_bindings_opt
  RAW_PRINTED BY pr_fun_ind_using
  GLOB_TYPED AS constr_with_bindings_opt
  GLOB_PRINTED BY pr_fun_ind_using
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
       let c = match cl with
	 | [] -> assert false
	 | [c] -> c
	 | c::cl -> applist(c,cl)
       in
       Extratactics.onSomeWithHoles (fun x -> functional_induction true c x pat) princl ]
END
(***** debug only ***)
TACTIC EXTEND snewfunind
   ["soft" "functional" "induction" ne_constr_list(cl) fun_ind_using(princl) with_names(pat)] ->
     [
       let c = match cl with
	 | [] -> assert false
	 | [c] -> c
	 | c::cl -> applist(c,cl)
       in
       Extratactics.onSomeWithHoles (fun x -> functional_induction false c x pat) princl ]
END


let pr_constr_coma_sequence prc _ _ = Util.prlist_with_sep Util.pr_comma prc

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

module Gram = Pcoq.Gram
module Vernac = Pcoq.Vernac_
module Tactic = Pcoq.Tactic

module FunctionGram =
struct
  let gec s = Gram.entry_create ("Function."^s)
		(* types *)
  let function_rec_definition_loc : (Vernacexpr.fixpoint_expr * Vernacexpr.decl_notation list) located Gram.entry = gec "function_rec_definition_loc"
end
open FunctionGram

GEXTEND Gram
  GLOBAL: function_rec_definition_loc ;

  function_rec_definition_loc:
    [ [ g = Vernac.rec_definition -> loc, g ]]
    ;

  END
type 'a function_rec_definition_loc_argtype = ((Vernacexpr.fixpoint_expr * Vernacexpr.decl_notation list) located, 'a) Genarg.abstract_argument_type

let (wit_function_rec_definition_loc : Genarg.tlevel function_rec_definition_loc_argtype),
  (globwit_function_rec_definition_loc : Genarg.glevel function_rec_definition_loc_argtype),
  (rawwit_function_rec_definition_loc : Genarg.rlevel function_rec_definition_loc_argtype) =
  Genarg.create_arg "function_rec_definition_loc"
VERNAC COMMAND EXTEND Function
   ["Function" ne_function_rec_definition_loc_list_sep(recsl,"with")] ->
	[
	  do_generate_principle false (List.map snd recsl);

	]
END

let pr_fun_scheme_arg (princ_name,fun_name,s) =
  Nameops.pr_id princ_name ++ str " :=" ++ spc() ++ str "Induction for " ++
  Libnames.pr_reference fun_name ++ spc() ++ str "Sort " ++
  Ppconstr.pr_rawsort s

VERNAC ARGUMENT EXTEND fun_scheme_arg
PRINTED BY pr_fun_scheme_arg
| [ ident(princ_name) ":=" "Induction" "for" reference(fun_name) "Sort" sort(s) ] -> [ (princ_name,fun_name,s) ]
END


let warning_error names e =
  match e with
    | Building_graph e ->
	Pp.msg_warning
	  (str "Cannot define graph(s) for " ++
	     h 1 (prlist_with_sep (fun _ -> str","++spc ()) Libnames.pr_reference names) ++
	     if do_observe () then (spc () ++ Cerrors.explain_exn e) else mt ())
    | Defining_principle e ->
	Pp.msg_warning
	  (str "Cannot define principle(s) for "++
	     h 1 (prlist_with_sep (fun _ -> str","++spc ()) Libnames.pr_reference names) ++
	     if do_observe () then Cerrors.explain_exn e else mt ())
    | _ -> raise e


VERNAC COMMAND EXTEND NewFunctionalScheme
   ["Functional" "Scheme" ne_fun_scheme_arg_list_sep(fas,"with") ] ->
    [
      begin
	try
	  Functional_principles_types.build_scheme fas
	with Functional_principles_types.No_graph_found ->
	  begin
	    match fas with
	      | (_,fun_name,_)::_ ->
		  begin
		    begin
		      make_graph (Nametab.global fun_name)
		    end
		    ;
		    try Functional_principles_types.build_scheme fas
		    with Functional_principles_types.No_graph_found ->
		      Util.error ("Cannot generate induction principle(s)")
    		      | e ->
			  let names = List.map (fun (_,na,_) -> na) fas in
			  warning_error names e

		  end
	      | _ -> assert false (* we can only have non empty  list *)
	  end
	  | e -> 
	      let names = List.map (fun (_,na,_) -> na) fas in
	      warning_error names e
      end

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
    (Tactics.letin_tac None (Name idunsafe) cstr None allHypsAndConcl)
    (tclTHENFIRST
      (Tactics.assert_tac Anonymous (mkEq typ (mkVar idunsafe) cstr))
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
	      let cname = Namegen.id_of_name_using_hdchar (Global.env()) typ Anonymous in
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
		    None None) gl))
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
	finduction None heuristic (Tacinterp.eval_tactic tac)
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
  [ "Mergeschemes" "(" ident(id1) ne_ident_list(cl1) ")"
      "with" "(" ident(id2) ne_ident_list(cl2)  ")" "using" ident(id) ] ->
     [
       let f1 = Constrintern.interp_constr Evd.empty (Global.env())
	 (CRef (Libnames.Ident (Util.dummy_loc,id1))) in
       let f2 = Constrintern.interp_constr Evd.empty (Global.env())
	 (CRef (Libnames.Ident (Util.dummy_loc,id2))) in
       let f1type = Typing.type_of (Global.env()) Evd.empty f1 in
       let f2type = Typing.type_of (Global.env()) Evd.empty f2 in
       let ar1 = List.length (fst (decompose_prod f1type)) in
       let ar2 = List.length (fst (decompose_prod f2type)) in
       let _ =
	 if ar1 <> List.length cl1 then
	   Util.error ("not the right number of arguments for " ^ string_of_id id1) in
       let _ =
	 if ar2 <> List.length cl2 then
	   Util.error ("not the right number of arguments for " ^ string_of_id id2) in
       Merge.merge id1 id2 (Array.of_list cl1) (Array.of_list cl2)  id
     ]
END
