(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Printers for the ocaml toplevel. *)

open Util
open Pp
open Names
open Libnames
open Globnames
open Nameops
open Univ
open Environ
open Printer
open Term
open Evd
open Goptions
open Genarg
open Clenv
open Universes

let _ = Detyping.print_evar_arguments := true
let _ = Detyping.print_universes := true
let _ = set_bool_option_value ["Printing";"Matching"] false
let _ = Detyping.set_detype_anonymous (fun _ _ -> raise Not_found)

(* std_ppcmds *)
let pppp x = pp x

(** Future printer *)

let ppfuture kx = pp (Future.print (fun _ -> str "_") kx)

(* name printers *)
let ppid id = pp (pr_id id)
let pplab l = pp (pr_lab l)
let ppmbid mbid = pp (str (MBId.debug_to_string mbid))
let ppdir dir = pp (pr_dirpath dir)
let ppmp mp = pp(str (string_of_mp mp))
let ppcon con = pp(debug_pr_con con)
let ppproj con = pp(debug_pr_con (Projection.constant con))
let ppkn kn = pp(pr_kn kn)
let ppmind kn = pp(debug_pr_mind kn)
let ppind (kn,i) = pp(debug_pr_mind kn ++ str"," ++int i)
let ppsp sp = pp(pr_path sp)
let ppqualid qid = pp(pr_qualid qid)
let ppclindex cl = pp(Classops.pr_cl_index cl)
let ppscheme k = pp (Ind_tables.pr_scheme_kind k)

let pprecarg = function
  | Declarations.Norec -> str "Norec"
  | Declarations.Mrec (mind,i) ->
     str "Mrec[" ++ MutInd.print mind ++ pr_comma () ++ int i ++ str "]"
  | Declarations.Imbr (mind,i) ->
     str "Imbr[" ++ MutInd.print mind ++ pr_comma () ++ int i ++ str "]"
let ppwf_paths x = pp (Rtree.pp_tree pprecarg x)

let pprecarg = function
  | Declarations.Norec -> str "Norec"
  | Declarations.Mrec (mind,i) ->
     str "Mrec[" ++ MutInd.print mind ++ pr_comma () ++ int i ++ str "]"
  | Declarations.Imbr (mind,i) ->
     str "Imbr[" ++ MutInd.print mind ++ pr_comma () ++ int i ++ str "]"
let ppwf_paths x = pp (Rtree.pp_tree pprecarg x)

(* term printers *)
let rawdebug = ref false
let ppevar evk = pp (str (Evd.string_of_existential evk))
let ppconstr x = pp (Termops.print_constr x)
let ppconstr_expr x = pp (Ppconstr.pr_constr_expr x)
let ppconstrdb x = pp(Flags.with_option rawdebug Termops.print_constr x)
let ppterm = ppconstr
let ppsconstr x = ppconstr (Mod_subst.force_constr x)
let ppconstr_univ x = Constrextern.with_universes ppconstr x
let ppglob_constr = (fun x -> pp(pr_lglob_constr x))
let pppattern = (fun x -> pp(pr_constr_pattern x))
let pptype = (fun x -> try pp(pr_ltype x) with e -> pp (str (Printexc.to_string e)))
let ppfconstr c = ppconstr (Closure.term_of_fconstr c)

let ppbigint n = pp (str (Bigint.to_string n));;

let prset pr l = str "[" ++ hov 0 (prlist_with_sep spc pr l) ++ str "]"
let ppintset l = pp (prset int (Int.Set.elements l))
let ppidset l = pp (prset pr_id (Id.Set.elements l))

let prset' pr l = str "[" ++ hov 0 (prlist_with_sep pr_comma pr l) ++ str "]"

let pridmap pr l =
  let pr (id,b) = pr_id id ++ str "=>" ++ pr id b in
  prset' pr (Id.Map.fold (fun a b l -> (a,b)::l) l [])

let ppidmap pr l = pp (pridmap pr l)

let ppevarsubst = ppidmap (fun id0 -> prset (fun (c,copt,id) ->
  hov 0
  (Termops.print_constr c ++
   (match copt with None -> mt () | Some c -> spc () ++ str "<expanded: " ++
    Termops.print_constr c ++ str">") ++
   (if id = id0 then mt ()
    else spc () ++ str "<canonical: " ++ pr_id id ++ str ">"))))

let prididmap = pridmap (fun _ -> pr_id)
let ppididmap = ppidmap (fun _ -> pr_id)

let prconstrunderbindersidmap = pridmap (fun _ (l,c) ->
  hov 1 (str"[" ++  prlist_with_sep spc Id.print l ++ str"]")
  ++ str "," ++ spc () ++ Termops.print_constr c)

let ppconstrunderbindersidmap l = pp (prconstrunderbindersidmap l)

let ppunbound_ltac_var_map l = ppidmap (fun _ arg ->
  str"<genarg:" ++ pr_argument_type(genarg_tag arg) ++ str">")

open Glob_term

let rec pr_closure {idents=idents;typed=typed;untyped=untyped} =
  hov 1 (str"{idents=" ++ prididmap idents ++ str";" ++ spc() ++
         str"typed=" ++ prconstrunderbindersidmap typed ++ str";" ++ spc() ++
         str"untyped=" ++ pr_closed_glob_constr_idmap untyped ++ str"}")
and pr_closed_glob_constr_idmap x =
  pridmap (fun _ -> pr_closed_glob_constr) x
and pr_closed_glob_constr {closure=closure;term=term} =
  pr_closure closure ++ pr_lglob_constr term

let ppclosure x = pp (pr_closure x)
let ppclosedglobconstr x = pp (pr_closed_glob_constr x)
let ppclosedglobconstridmap x = pp (pr_closed_glob_constr_idmap x)

let pP s = pp (hov 0 s)

let safe_pr_global = function
  | ConstRef kn -> pp (str "CONSTREF(" ++ debug_pr_con kn ++ str ")")
  | IndRef (kn,i) -> pp (str "INDREF(" ++ debug_pr_mind kn ++ str "," ++
			  int i ++ str ")")
  | ConstructRef ((kn,i),j) -> pp (str "INDREF(" ++ debug_pr_mind kn ++ str "," ++
				      int i ++ str "," ++ int j ++ str ")")
  | VarRef id -> pp (str "VARREF(" ++ pr_id id ++ str ")")

let ppglobal x = try pp(pr_global x) with _ -> safe_pr_global x

let ppconst (sp,j) =
    pp (str"#" ++ pr_kn sp ++ str"=" ++ pr_lconstr j.uj_val)

let ppvar ((id,a)) =
    pp (str"#" ++ pr_id id ++ str":" ++ pr_lconstr a)

let genppj f j = let (c,t) = f j in (c ++ str " : " ++ t)

let ppj j = pp (genppj pr_ljudge j)

let prsubst s = pp (Mod_subst.debug_pr_subst s)
let prdelta s = pp (Mod_subst.debug_pr_delta s)

let pp_idpred s = pp (pr_idpred s)
let pp_cpred s = pp (pr_cpred s)
let pp_transparent_state s = pp (pr_transparent_state s)
let pp_stack_t n = pp (Reductionops.Stack.pr Termops.print_constr n)
let pp_cst_stack_t n = pp (Reductionops.Cst_stack.pr n)
let pp_state_t n = pp (Reductionops.pr_state n)

(* proof printers *)
let pr_evar ev = Pp.int (Evar.repr ev)
let ppmetas metas = pp(pr_metaset metas)
let ppevm evd = pp(pr_evar_map ~with_univs:!Flags.univ_print (Some 2) evd)
let ppevmall evd = pp(pr_evar_map ~with_univs:!Flags.univ_print None evd)
let pr_existentialset evars =
  prlist_with_sep spc pr_evar (Evar.Set.elements evars)
let ppexistentialset evars =
  pp (pr_existentialset evars)
let ppexistentialfilter filter = match Evd.Filter.repr filter with
| None -> pp (Pp.str "ø")
| Some f -> pp (prlist_with_sep spc bool f)
let ppclenv clenv = pp(pr_clenv clenv)
let ppgoalgoal gl = pp(Goal.pr_goal gl)
let ppgoal g = pp(Printer.pr_goal g)
let ppgoalsigma g = pp(Printer.pr_goal g ++ pr_evar_map None (Refiner.project g))
let pphintdb db = pp(Hints.pr_hint_db db)
let ppproofview p =
  let gls,sigma = Proofview.proofview p in
  pp(pr_enum Goal.pr_goal gls ++ fnl () ++ pr_evar_map (Some 1) sigma)

let ppopenconstr (x : Evd.open_constr) =
  let (evd,c) = x in pp (pr_evar_map (Some 2) evd ++ pr_constr c)
(* spiwack: deactivated until a replacement is found
let pppftreestate p = pp(print_pftreestate p)
*)

(* let ppgoal g = pp(db_pr_goal g) *)
(* let pr_gls gls = *)
(*   hov 0 (pr_evar_defs (sig_sig gls) ++ fnl () ++ db_pr_goal (sig_it gls)) *)

(* let pr_glls glls = *)
(*   hov 0 (pr_evar_defs (sig_sig glls) ++ fnl () ++ *)
(*          prlist_with_sep fnl db_pr_goal (sig_it glls)) *)

(* let ppsigmagoal g = pp(pr_goal (sig_it g)) *)
(* let prgls gls = pp(pr_gls gls) *)
(* let prglls glls = pp(pr_glls glls) *)
(* let pproof p = pp(print_proof Evd.empty empty_named_context p) *)

let ppuni u = pp(pr_uni u)
let ppuni_level u = pp (Level.pr u)
let ppuniverse u = pp (str"[" ++ Universe.pr u ++ str"]")

let prlev = Universes.pr_with_global_universes
let ppuniverse_set l = pp (LSet.pr prlev l)
let ppuniverse_instance l = pp (Instance.pr prlev l)
let ppuniverse_context l = pp (pr_universe_context prlev l)
let ppuniverse_context_set l = pp (pr_universe_context_set prlev l)
let ppuniverse_subst l = pp (Univ.pr_universe_subst l)
let ppuniverse_opt_subst l = pp (Universes.pr_universe_opt_subst l)
let ppuniverse_level_subst l = pp (Univ.pr_universe_level_subst l)
let ppevar_universe_context l = pp (Evd.pr_evar_universe_context l)
let ppconstraints_map c = pp (Universes.pr_constraints_map c)
let ppconstraints c = pp (pr_constraints Level.pr c)
let ppuniverseconstraints c = pp (Universes.Constraints.pr c)
let ppuniverse_context_future c = 
  let ctx = Future.force c in
    ppuniverse_context ctx
let ppuniverses u = pp (Univ.pr_universes Level.pr u)
let ppnamedcontextval e =
  pp (pr_named_context (Global.env ()) Evd.empty (named_context_of_val e))

let ppenv e = pp
  (str "[" ++ pr_named_context_of e Evd.empty ++ str "]" ++ spc() ++
   str "[" ++ pr_rel_context e Evd.empty (rel_context e) ++ str "]")

let pptac = (fun x -> pp(Pptactic.pr_glob_tactic (Global.env()) x))

let ppobj obj = Format.print_string (Libobject.object_tag obj)

let cnt = ref 0

let cast_kind_display k =
  match k with
  | VMcast -> "VMcast"
  | DEFAULTcast -> "DEFAULTcast"
  | REVERTcast -> "REVERTcast"
  | NATIVEcast -> "NATIVEcast"

let constr_display csr =
  let rec term_display c = match kind_of_term c with
  | Rel n -> "Rel("^(string_of_int n)^")"
  | Meta n -> "Meta("^(string_of_int n)^")"
  | Var id -> "Var("^(Id.to_string id)^")"
  | Sort s -> "Sort("^(sort_display s)^")"
  | Cast (c,k, t) ->
      "Cast("^(term_display c)^","^(cast_kind_display k)^","^(term_display t)^")"
  | Prod (na,t,c) ->
      "Prod("^(name_display na)^","^(term_display t)^","^(term_display c)^")\n"
  | Lambda (na,t,c) ->
      "Lambda("^(name_display na)^","^(term_display t)^","^(term_display c)^")\n"
  | LetIn (na,b,t,c) ->
      "LetIn("^(name_display na)^","^(term_display b)^","
      ^(term_display t)^","^(term_display c)^")"
  | App (c,l) -> "App("^(term_display c)^","^(array_display l)^")\n"
  | Evar (e,l) -> "Evar("^(string_of_existential e)^","^(array_display l)^")"
  | Const (c,u) -> "Const("^(string_of_con c)^","^(universes_display u)^")"
  | Ind ((sp,i),u) ->
      "MutInd("^(string_of_mind sp)^","^(string_of_int i)^","^(universes_display u)^")"
  | Construct (((sp,i),j),u) ->
      "MutConstruct(("^(string_of_mind sp)^","^(string_of_int i)^"),"
      ^","^(universes_display u)^(string_of_int j)^")"
  | Proj (p, c) -> "Proj("^(string_of_con (Projection.constant p))^","^term_display c ^")"
  | Case (ci,p,c,bl) ->
      "MutCase(<abs>,"^(term_display p)^","^(term_display c)^","
      ^(array_display bl)^")"
  | Fix ((t,i),(lna,tl,bl)) ->
      "Fix(([|"^(Array.fold_right (fun x i -> (string_of_int x)^(if not(i="")
        then (";"^i) else "")) t "")^"|],"^(string_of_int i)^"),"
      ^(array_display tl)^",[|"
      ^(Array.fold_right (fun x i -> (name_display x)^(if not(i="")
        then (";"^i) else "")) lna "")^"|],"
      ^(array_display bl)^")"
  | CoFix(i,(lna,tl,bl)) ->
      "CoFix("^(string_of_int i)^"),"
      ^(array_display tl)^","
      ^(Array.fold_right (fun x i -> (name_display x)^(if not(i="")
        then (";"^i) else "")) lna "")^","
      ^(array_display bl)^")"

  and array_display v =
    "[|"^
    (Array.fold_right
       (fun x i -> (term_display x)^(if not(i="") then (";"^i) else ""))
       v "")^"|]"

  and univ_display u =
    incr cnt; pp (str "with " ++ int !cnt ++ str" " ++ pr_uni u ++ fnl ())

  and level_display u =
    incr cnt; pp (str "with " ++ int !cnt ++ str" " ++ Level.pr u ++ fnl ())

  and sort_display = function
    | Prop(Pos) -> "Prop(Pos)"
    | Prop(Null) -> "Prop(Null)"
    | Type u -> univ_display u;
	"Type("^(string_of_int !cnt)^")"

  and universes_display l = 
    Array.fold_right (fun x i -> level_display x; (string_of_int !cnt)^(if not(i="")
        then (" "^i) else "")) (Instance.to_array l) ""

  and name_display = function
    | Name id -> "Name("^(Id.to_string id)^")"
    | Anonymous -> "Anonymous"

  in
  Pp.pp (str (term_display csr) ++fnl ()); Pp.pp_flush ()

open Format;;

let print_pure_constr csr =
  let rec term_display c = match kind_of_term c with
  | Rel n -> print_string "#"; print_int n
  | Meta n -> print_string "Meta("; print_int n; print_string ")"
  | Var id -> print_string (Id.to_string id)
  | Sort s -> sort_display s
  | Cast (c,_, t) -> open_hovbox 1;
      print_string "("; (term_display c); print_cut();
      print_string "::"; (term_display t); print_string ")"; close_box()
  | Prod (Name(id),t,c) ->
      open_hovbox 1;
      print_string"("; print_string (Id.to_string id);
      print_string ":"; box_display t;
      print_string ")"; print_cut();
      box_display c; close_box()
  | Prod (Anonymous,t,c) ->
      print_string"("; box_display t; print_cut(); print_string "->";
      box_display c; print_string ")";
  | Lambda (na,t,c) ->
      print_string "["; name_display na;
      print_string ":"; box_display t; print_string "]";
      print_cut(); box_display c;
  | LetIn (na,b,t,c) ->
      print_string "["; name_display na; print_string "=";
      box_display b; print_cut();
      print_string ":"; box_display t; print_string "]";
      print_cut(); box_display c;
  | App (c,l) ->
      print_string "(";
      box_display c;
      Array.iter (fun x -> print_space (); box_display x) l;
      print_string ")"
  | Evar (e,l) -> print_string "Evar#"; print_int (Evar.repr e); print_string "{";
      Array.iter (fun x -> print_space (); box_display x) l;
      print_string"}"
  | Const (c,u) -> print_string "Cons(";
      sp_con_display c;
      print_string ","; universes_display u;
      print_string ")"
  | Proj (p,c') -> print_string "Proj(";
      sp_con_display (Projection.constant p);
      print_string ",";
      box_display c';
      print_string ")"
  | Ind ((sp,i),u) ->
      print_string "Ind(";
      sp_display sp;
      print_string ","; print_int i;
      print_string ","; universes_display u;
      print_string ")"
  | Construct (((sp,i),j),u) ->
      print_string "Constr(";
      sp_display sp;
      print_string ",";
      print_int i; print_string ","; print_int j; 
      print_string ","; universes_display u;
      print_string ")"
  | Case (ci,p,c,bl) ->
      open_vbox 0;
      print_string "<"; box_display p; print_string ">";
      print_cut(); print_string "Case";
      print_space(); box_display c; print_space (); print_string "of";
      open_vbox 0;
      Array.iter (fun x ->  print_cut();  box_display x) bl;
      close_box();
      print_cut();
      print_string "end";
      close_box()
  | Fix ((t,i),(lna,tl,bl)) ->
      print_string "Fix("; print_int i; print_string ")";
      print_cut();
      open_vbox 0;
      let print_fix () =
        for k = 0 to (Array.length tl) - 1 do
	  open_vbox 0;
	  name_display lna.(k); print_string "/";
	  print_int t.(k); print_cut(); print_string ":";
	  box_display tl.(k) ; print_cut(); print_string ":=";
	  box_display bl.(k); close_box ();
	  print_cut()
        done
      in print_string"{"; print_fix(); print_string"}"
  | CoFix(i,(lna,tl,bl)) ->
      print_string "CoFix("; print_int i; print_string ")";
      print_cut();
      open_vbox 0;
      let print_fix () =
        for k = 0 to (Array.length tl) - 1 do
          open_vbox 1;
	  name_display lna.(k);  print_cut(); print_string ":";
	  box_display tl.(k) ; print_cut(); print_string ":=";
	  box_display bl.(k); close_box ();
	  print_cut();
        done
      in print_string"{"; print_fix (); print_string"}"

  and box_display c = open_hovbox 1; term_display c; close_box()

  and universes_display u =
    Array.iter (fun u -> print_space (); pp (Level.pr u)) (Instance.to_array u)

  and sort_display = function
    | Prop(Pos) -> print_string "Set"
    | Prop(Null) -> print_string "Prop"
    | Type u -> open_hbox();
	print_string "Type("; pp (pr_uni u); print_string ")"; close_box()

  and name_display = function
    | Name id -> print_string (Id.to_string id)
    | Anonymous -> print_string "_"
(* Remove the top names for library and Scratch to avoid long names *)
  and sp_display sp =
(*    let dir,l = decode_kn sp in
    let ls =
      match List.rev_map Id.to_string (DirPath.repr dir) with
          ("Top"::l)-> l
	| ("Coq"::_::l) -> l
	| l             -> l
    in  List.iter (fun x -> print_string x; print_string ".") ls;*)
      print_string (debug_string_of_mind sp)
  and sp_con_display sp =
(*    let dir,l = decode_kn sp in
    let ls =
      match List.rev_map Id.to_string (DirPath.repr dir) with
          ("Top"::l)-> l
	| ("Coq"::_::l) -> l
	| l             -> l
    in  List.iter (fun x -> print_string x; print_string ".") ls;*)
      print_string (debug_string_of_con sp)

  in
    try
     box_display csr; print_flush()
    with e ->
	print_string (Printexc.to_string e);print_flush ();
	raise e

let ppfconstr c = ppconstr (Closure.term_of_fconstr c)

let pploc x = let (l,r) = Loc.unloc x in
  print_string"(";print_int l;print_string",";print_int r;print_string")"

let pp_argument_type t = pp (pr_argument_type t)

let pp_generic_argument arg =
  pp(str"<genarg:"++pr_argument_type(genarg_tag arg)++str">")

let prgenarginfo arg =
  let tpe = pr_argument_type (genarg_tag arg) in
  let pr_gtac _ x = Pptactic.pr_glob_tactic (Global.env()) x in
  try
    let data = Pptactic.pr_top_generic pr_constr pr_lconstr pr_gtac pr_constr_pattern arg in
    str "<genarg:" ++ tpe ++ str " := [ " ++ data ++ str " ] >"
  with _any ->
    str "<genarg:" ++ tpe ++ str ">"

let ppgenarginfo arg = pp (prgenarginfo arg)

let ppist ist =
  let pr id arg = prgenarginfo arg in
  pp (pridmap pr ist.Geninterp.lfun)

(**********************************************************************)
(* Vernac-level debugging commands                                    *)

let in_current_context f c =
  let (evmap,sign) =
    try Pfedit.get_current_goal_context ()
    with e when Logic.catchable_exception e -> (Evd.empty, Global.env()) in
  f (fst (Constrintern.interp_constr sign evmap c))(*FIXME*)

(* We expand the result of preprocessing to be independent of camlp4

VERNAC COMMAND EXTEND PrintPureConstr
| [ "PrintPureConstr" constr(c) ] -> [ in_current_context print_pure_constr c ]
END
VERNAC COMMAND EXTEND PrintConstr
  [ "PrintConstr" constr(c) ] -> [ in_current_context constr_display c ]
END
*)

open Pcoq
open Genarg
open Constrarg
open Egramml

let _ =
  try
    Vernacinterp.vinterp_add ("PrintConstr", 0)
      (function
         [c] when genarg_tag c = ConstrArgType && true ->
           let c = out_gen (rawwit wit_constr) c in
           (fun () -> in_current_context constr_display c)
       | _ -> failwith "Vernac extension: cannot occur")
  with
    e -> Pp.pp (Errors.print e)
let _ =
  extend_vernac_command_grammar ("PrintConstr", 0) None
    [GramTerminal "PrintConstr";
      GramNonTerminal
        (Loc.ghost,ConstrArgType,Aentry ("constr","constr"),
	 Some (Names.Id.of_string "c"))]

let _ =
  try
    Vernacinterp.vinterp_add ("PrintPureConstr", 0)
      (function
         [c] when genarg_tag c = ConstrArgType && true ->
           let c = out_gen (rawwit wit_constr) c in
           (fun () -> in_current_context print_pure_constr c)
       | _ -> failwith "Vernac extension: cannot occur")
  with
    e -> Pp.pp (Errors.print e)
let _ =
  extend_vernac_command_grammar ("PrintPureConstr", 0) None
    [GramTerminal "PrintPureConstr";
      GramNonTerminal
        (Loc.ghost,ConstrArgType,Aentry ("constr","constr"),
	 Some (Names.Id.of_string "c"))]

(* Setting printer of unbound global reference *)
open Names
open Libnames

let encode_path loc prefix mpdir suffix id =
  let dir = match mpdir with
    | None -> []
    | Some (mp,dir) ->
	(DirPath.repr (dirpath_of_string (string_of_mp mp))@
	DirPath.repr dir) in
  Qualid (loc, make_qualid
    (DirPath.make (List.rev (Id.of_string prefix::dir@suffix))) id)

let raw_string_of_ref loc _ = function
  | ConstRef cst ->
      let (mp,dir,id) = repr_con cst in
      encode_path loc "CST" (Some (mp,dir)) [] (Label.to_id id)
  | IndRef (kn,i) ->
      let (mp,dir,id) = repr_mind kn in
      encode_path loc "IND" (Some (mp,dir)) [Label.to_id id]
	(Id.of_string ("_"^string_of_int i))
  | ConstructRef ((kn,i),j) ->
      let (mp,dir,id) = repr_mind kn in
      encode_path loc "CSTR" (Some (mp,dir))
	[Label.to_id id;Id.of_string ("_"^string_of_int i)]
	(Id.of_string ("_"^string_of_int j))
  | VarRef id ->
      encode_path loc "SECVAR" None [] id

let short_string_of_ref loc _ = function
  | VarRef id -> Ident (loc,id)
  | ConstRef cst -> Ident (loc,Label.to_id (pi3 (repr_con cst)))
  | IndRef (kn,0) -> Ident (loc,Label.to_id (pi3 (repr_mind kn)))
  | IndRef (kn,i) ->
      encode_path loc "IND" None [Label.to_id (pi3 (repr_mind kn))]
        (Id.of_string ("_"^string_of_int i))
  | ConstructRef ((kn,i),j) ->
      encode_path loc "CSTR" None
        [Label.to_id (pi3 (repr_mind kn));Id.of_string ("_"^string_of_int i)]
        (Id.of_string ("_"^string_of_int j))

(* Anticipate that printers can be used from ocamldebug and that 
   pretty-printer should not make calls to the global env since ocamldebug
   runs in a different process and does not have the proper env at hand *)
let _ = Flags.in_debugger := true
let _ = Constrextern.set_extern_reference
  (if !rawdebug then raw_string_of_ref else short_string_of_ref)
