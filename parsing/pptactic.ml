(****************************************************************************)
(*                                                                          *)
(*                          The Coq Proof Assistant                         *)
(*                                                                          *)
(*                                 Projet Coq                               *)
(*                                                                          *)
(*                     INRIA        LRI-CNRS        ENS-CNRS                *)
(*              Rocquencourt         Orsay          Lyon                    *)
(*                                                                          *)
(****************************************************************************)

(* $Id$ *)

open Pp
open Names
open Nameops
open Util
open Extend
open Ppconstr
open Tacexpr
open Rawterm
open Genarg

  (* Extensions *)
let prtac_tab = Hashtbl.create 17

let declare_extra_tactic_pprule s f g =
  Hashtbl.add prtac_tab s (f,g)

let genarg_pprule = ref Stringmap.empty

let declare_extra_genarg_pprule (rawwit, f) (wit, g) =
  let s = match unquote wit with
    | ExtraArgType s -> s 
    | _ -> error
	"Can declare a pretty-printing rule only for extra argument types"
  in
  let f x = f (out_gen rawwit x) in
  let g x = g (out_gen wit x) in
  genarg_pprule := Stringmap.add s (f,g) !genarg_pprule 

(* [pr_rawtac] is here to cheat with ML typing system,
   gen_tactic_expr is polymorphic but with some occurrences of its
   instance raw_tactic_expr in it; then pr_tactic should be
   polymorphic but with some calls to instance of itself, what ML does
   not accept; pr_rawtac0 denotes this instance of pr_tactic on
   raw_tactic_expr *)

let pr_rawtac =
  ref (fun _ -> failwith "Printer for raw tactic expr is not defined"
       : raw_tactic_expr -> std_ppcmds)
let pr_rawtac0 =
  ref (fun _ -> failwith "Printer for raw tactic expr is not defined"
       : raw_tactic_expr -> std_ppcmds)

let pr_arg pr x = spc () ++ pr x

let pr_name = function
  | Anonymous -> mt ()
  | Name id -> spc () ++ pr_id id

let pr_metanum pr = function
  | AN (_,x) -> pr x
  | MetaNum (_,n) -> str "?" ++ int n

let pr_or_var pr = function
  | ArgArg x -> pr x
  | ArgVar (_,s) -> pr_id s

let pr_opt pr = function
  | None -> mt ()
  | Some x -> spc () ++ pr x

let pr_or_meta pr = function
  | AI x -> pr x
  | _ -> failwith "pr_hyp_location: unexpected quotation meta-variable"

let pr_casted_open_constr = pr_constr

let pr_quantified_hypothesis = function
  | AnonHyp n -> int n
  | NamedHyp id -> pr_id id 

let pr_quantified_hypothesis_arg h = spc () ++ pr_quantified_hypothesis h

let pr_binding prc = function
  | NamedHyp id, c -> hov 1 (pr_id id ++ str ":=" ++ cut () ++ prc c)
  | AnonHyp n, c -> hov 1 (int n ++ str ":=" ++ cut () ++ prc c)

let pr_bindings prc = function
  | ImplicitBindings l ->
      brk (1,1) ++ str "with" ++ brk (1,1) ++
      prlist_with_sep spc prc l
  | ExplicitBindings l ->
      brk (1,1) ++ str "with" ++ brk (1,1) ++ 
        prlist_with_sep spc (pr_binding prc) l
  | NoBindings -> mt ()

let pr_with_bindings prc (c,bl) = prc c ++ hv 0 (pr_bindings prc bl)

let rec pr_intro_pattern = function
  | IntroOrAndPattern pll ->
      str "[" ++
      hv 0 (prlist_with_sep pr_coma (prlist_with_sep spc pr_intro_pattern) pll)
      ++ str "]"
(*
  | IntroAndPattern pl ->
      str "(" ++ hov 0 (prlist_with_sep pr_coma pr_intro_pattern pl) ++ str ")"
*)
  | IntroWildcard -> str "_"
  | IntroIdentifier id -> pr_id id

let pr_hyp_location pr_id = function
  | InHyp id -> spc () ++ pr_id id
  | InHypType id -> spc () ++ str "(Type of " ++ pr_id id ++ str ")"

let pr_clause pr_id = function
  | [] -> mt ()
  | l -> spc () ++ hov 0 (str "in" ++ prlist (pr_hyp_location pr_id) l)

let pr_clause_pattern pr_id = function (* To check *)
  | (None, []) -> mt ()
  | (glopt,l) ->
      str "in" ++
      prlist
        (fun (id,nl) -> spc () ++ prlist_with_sep spc int nl 
	  ++ spc () ++ pr_id id) l ++
        pr_opt (prlist_with_sep spc int) glopt

let pr_induction_arg prc = function
  | ElimOnConstr c -> prc c
  | ElimOnIdent (_,id) -> pr_id id
  | ElimOnAnonHyp n -> int n

let pr_match_pattern = function
  | Term a -> pr_pattern a
  | Subterm (None,a) -> str "[" ++ pr_pattern a ++ str "]"
  | Subterm (Some id,a) -> pr_id id ++ str "[" ++ pr_pattern a ++ str "]"

let pr_match_hyps = function
  | NoHypId mp -> str "_:" ++ pr_match_pattern mp
  | Hyp ((_,id),mp) -> pr_id id ++ str ":" ++ pr_match_pattern mp

let pr_match_rule m pr = function
  | Pat ([],mp,t) when m ->
      str "[" ++ pr_match_pattern mp ++ str "]"
      ++ spc () ++ str "->" ++ brk (1,2) ++ pr t
  | Pat (rl,mp,t) ->
      str "[" ++ prlist_with_sep pr_semicolon pr_match_hyps rl ++ spc () ++ 
      str "|-" ++ spc () ++ pr_match_pattern mp ++ spc () ++ str "]" ++
      spc () ++ str "->" ++ brk (1,2) ++ pr t
  | All t -> str "_" ++ spc () ++ str "->" ++ brk (1,2) ++ pr t

let pr_funvar = function
  | None -> spc () ++ str "()"
  | Some id -> spc () ++ pr_id id

let pr_let_clause k pr = function
  | ((_,id),None,t) -> hv 0(str k ++ pr_id id ++ str " =" ++ brk (1,1) ++ pr t)
  | ((_,id),Some c,t) -> str "TODO(LETCLAUSE)"

let pr_let_clauses pr = function
  | hd::tl ->
      hv 0
        (pr_let_clause "Let " pr hd ++ spc () ++
         prlist_with_sep spc (pr_let_clause "And " pr) tl)
  | [] -> anomaly "LetIn must declare at least one binding"

let pr_rec_clause pr ((_,id),(l,t)) =
  pr_id id ++ prlist pr_funvar l ++ str "->" ++ spc () ++ pr t

let pr_rec_clauses pr l = 
  prlist_with_sep (fun () -> fnl () ++ str "And ") (pr_rec_clause pr) l

let pr_hintbases = function
  | None -> spc () ++ str "with *"
  | Some [] -> mt ()
  | Some l ->
      spc () ++ str "with" ++ hv 0 (prlist (fun s -> spc () ++ str s) l)

let pr_autoarg_adding = function
  | [] -> mt ()
  | l ->
      spc () ++ str "Adding [" ++
        hv 0 (prlist_with_sep spc (fun (_,x) -> pr_qualid x) l) ++ str "]"

let pr_autoarg_destructing = function
  | true -> spc () ++ str "Destructing"
  | false -> mt ()

let pr_autoarg_usingTDB = function
  | true -> spc () ++ str "Using TDB"
  | false -> mt ()

let rec pr_rawgen prtac x =
  match Genarg.genarg_tag x with
  | BoolArgType -> pr_arg str (if out_gen rawwit_bool x then "true" else "false")
  | IntArgType -> pr_arg int (out_gen rawwit_int x)
  | IntOrVarArgType -> pr_arg (pr_or_var pr_int) (out_gen rawwit_int_or_var x)
  | StringArgType -> spc () ++ str "\"" ++ str (out_gen rawwit_string x) ++ str "\""
  | PreIdentArgType -> pr_arg str (out_gen rawwit_pre_ident x)
  | IdentArgType -> pr_arg pr_id (out_gen rawwit_ident x)
  | QualidArgType -> pr_arg pr_qualid (snd (out_gen rawwit_qualid x))
  | ConstrArgType -> pr_arg pr_constr (out_gen rawwit_constr x)
  | ConstrMayEvalArgType ->
      pr_arg (pr_may_eval pr_constr) (out_gen rawwit_constr_may_eval x)
  | QuantHypArgType ->
      pr_arg pr_quantified_hypothesis (out_gen rawwit_quant_hyp x)
  | RedExprArgType ->
      pr_arg (pr_red_expr (pr_constr,pr_metanum pr_qualid)) (out_gen rawwit_red_expr x)
  | TacticArgType -> pr_arg prtac (out_gen rawwit_tactic x)
  | CastedOpenConstrArgType ->
      pr_arg pr_casted_open_constr (out_gen rawwit_casted_open_constr x)
  | ConstrWithBindingsArgType -> 
      pr_arg (pr_with_bindings pr_constr)
      (out_gen rawwit_constr_with_bindings x)
  | List0ArgType _ -> 
      hov 0 (fold_list0 (fun x a -> pr_rawgen prtac x ++ a) x (mt()))
  | List1ArgType _ ->
      hov 0 (fold_list1 (fun x a -> pr_rawgen prtac x ++ a) x (mt()))
  | OptArgType _ -> hov 0 (fold_opt (pr_rawgen prtac) (mt()) x)
  | PairArgType _ ->
      hov 0
        (fold_pair
	  (fun a b -> pr_rawgen prtac a ++ spc () ++ pr_rawgen prtac b)
	  x)
  | ExtraArgType s -> 
      try fst (Stringmap.find s !genarg_pprule) x
      with Not_found -> str " [no printer for " ++ str s ++ str "] "

let rec pr_raw_tacarg_using_rule pr_gen = function
  | Egrammar.TacTerm s :: l, al -> str s ++ pr_raw_tacarg_using_rule pr_gen (l,al)
  | Egrammar.TacNonTerm _ :: l, a :: al -> pr_gen a ++ pr_raw_tacarg_using_rule  pr_gen (l,al)
  | [], [] -> mt ()
  | _ -> failwith "Inconsistent arguments of extended tactic"

let pr_raw_extend prt s l =
  try 
    let (s,pl) = fst (Hashtbl.find prtac_tab s) l in
    str s ++ pr_raw_tacarg_using_rule (pr_rawgen prt) (pl,l)
  with Not_found ->
    str "TODO(" ++ str s ++ prlist (pr_rawgen prt) l ++ str ")"

open Closure

let pr_evaluable_reference = function 
  | EvalVarRef id -> pr_id id
  | EvalConstRef sp -> pr_global (Nametab.ConstRef sp)

let pr_inductive ind = pr_global (Nametab.IndRef ind)

let rec pr_generic prtac x =
  match Genarg.genarg_tag x with
  | BoolArgType -> pr_arg str (if out_gen wit_bool x then "true" else "false")
  | IntArgType -> pr_arg int (out_gen wit_int x)
  | IntOrVarArgType -> pr_arg (pr_or_var pr_int) (out_gen wit_int_or_var x)
  | StringArgType -> spc () ++ str "\"" ++ str (out_gen wit_string x) ++ str "\""
  | PreIdentArgType -> pr_arg str (out_gen wit_pre_ident x)
  | IdentArgType -> pr_arg pr_id (out_gen wit_ident x)
  | QualidArgType -> pr_arg pr_global (out_gen wit_qualid x)
  | ConstrArgType -> pr_arg Printer.prterm (out_gen wit_constr x)
  | ConstrMayEvalArgType ->
      pr_arg Printer.prterm (out_gen wit_constr_may_eval x)
  | QuantHypArgType ->
      pr_arg pr_quantified_hypothesis (out_gen wit_quant_hyp x)
  | RedExprArgType ->
      pr_arg (pr_red_expr (Printer.prterm,pr_evaluable_reference)) (out_gen wit_red_expr x)
  | TacticArgType -> pr_arg prtac (out_gen wit_tactic x)
  | CastedOpenConstrArgType ->
      pr_arg Printer.prterm (snd (out_gen wit_casted_open_constr x))
  | ConstrWithBindingsArgType -> 
      pr_arg (pr_with_bindings Printer.prterm)
      (out_gen wit_constr_with_bindings x)
  | List0ArgType _ -> 
      hov 0 (fold_list0 (fun x a -> pr_generic prtac x ++ a) x (mt()))
  | List1ArgType _ ->
      hov 0 (fold_list1 (fun x a -> pr_generic prtac x ++ a) x (mt()))
  | OptArgType _ -> hov 0 (fold_opt (pr_generic prtac) (mt()) x)
  | PairArgType _ ->
      hov 0
        (fold_pair
	  (fun a b -> pr_generic prtac a ++ spc () ++ pr_generic prtac b)
	  x)
  | ExtraArgType s -> 
      try snd (Stringmap.find s !genarg_pprule) x
      with Not_found -> str "[no printer for " ++ str s ++ str "]"

let rec pr_tacarg_using_rule prt = function
  | Egrammar.TacTerm s :: l, al -> str s ++ pr_tacarg_using_rule prt (l,al)
  | Egrammar.TacNonTerm _ :: l, a :: al -> pr_generic prt a ++ pr_tacarg_using_rule prt (l,al)
  | [], [] -> mt ()
  | _ -> failwith "Inconsistent arguments of extended tactic"

let pr_extend prt s l =
  try 
    let (s,pl) = snd (Hashtbl.find prtac_tab s) l in
    str s ++ pr_tacarg_using_rule prt (pl,l)
  with Not_found ->
    str s ++ prlist (pr_generic prt) l

let make_pr_tac (pr_constr,pr_cst,pr_ind,pr_ident,pr_extend) =

let pr_bindings = pr_bindings pr_constr in
let pr_with_bindings = pr_with_bindings pr_constr in
let pr_constrarg c = spc () ++ pr_constr c in
let pr_intarg n = spc () ++ int n in

  (* Printing tactics as arguments *)
let rec pr_atom0 = function
  | TacIntroPattern [] -> str "Intros"
  | TacIntroMove (None,None) -> str "Intro"
  | TacAssumption -> str "Assumption"
  | TacAnyConstructor None -> str "Constructor"
  | TacTrivial (Some []) -> str "Trivial"
  | TacAuto (None,Some []) -> str "Auto"
  | TacAutoTDB None -> str "AutoTDB"
  | TacDestructConcl -> str "DConcl"
  | TacReflexivity -> str "Reflexivity"
  | TacSymmetry -> str "Symmetry"
  | t -> str "(" ++ pr_atom1 t ++ str ")"

  (* Main tactic printer *)
and pr_atom1 = function
  | TacExtend (s,l) -> pr_extend !pr_rawtac s l
  | TacAlias (s,l,_) -> pr_extend !pr_rawtac s (List.map snd l)

  (* Basic tactics *)
  | TacIntroPattern [] as t -> pr_atom0 t
  | TacIntroPattern (_::_ as p) -> 
      hov 1 (str "Intro" ++ spc () ++ prlist_with_sep spc pr_intro_pattern p)
  | TacIntrosUntil h ->
      hv 1 (str "Intros until" ++ pr_arg pr_quantified_hypothesis h)
  | TacIntroMove (None,None) as t -> pr_atom0 t
  | TacIntroMove (Some id1,None) -> str "Intro " ++ pr_id id1
  | TacIntroMove (ido1,Some (_,id2)) ->
      hov 1
      (str "Intro" ++ pr_opt pr_id ido1 ++ spc () ++ str "after " ++ pr_id id2)
  | TacAssumption as t -> pr_atom0 t
  | TacExact c -> hov 1 (str "Exact" ++ pr_arg pr_constr c)
  | TacApply cb -> hov 1 (str "Apply" ++ spc () ++ pr_with_bindings cb)
  | TacElim (cb,None) -> hov 1 (str "Elim" ++ spc () ++ pr_with_bindings cb)
  | TacElim (cb,Some cb') ->
      hov 1 (str "Elim" ++ pr_arg pr_with_bindings cb ++ 
      spc () ++ str "using" ++ pr_arg pr_with_bindings cb')
  | TacElimType c -> hov 1 (str "ElimType" ++ pr_arg pr_constr c)
  | TacCase cb -> hov 1 (str "Case" ++ spc () ++ pr_with_bindings cb)
  | TacCaseType c -> hov 1 (str "CaseType" ++ pr_arg pr_constr c)
  | TacFix (ido,n) -> hov 1 (str "Fix" ++ pr_opt pr_id ido ++ pr_intarg n)
  | TacMutualFix (id,n,l) ->
      hov 1 (str "Cofix" ++ spc () ++ pr_id id ++ pr_intarg n ++ spc () ++
        hov 0 (str "with" ++ brk (1,1) ++
          prlist_with_sep spc
	    (fun (id,n,c) ->
	      spc () ++ pr_id id ++ pr_intarg n ++ pr_arg pr_constr c)
	  l))
  | TacCofix ido -> hov 1 (str "Cofix" ++ pr_opt pr_id ido)
  | TacMutualCofix (id,l) ->
      hov 1 (str "Cofix" ++ spc () ++ pr_id id ++ spc () ++
        hov 0 (str "with" ++ brk (1,1) ++
          prlist (fun (id,c) -> spc () ++ pr_id id ++ pr_arg pr_constr c)
	  l))
  | TacCut c -> hov 1 (str "Cut" ++ pr_arg pr_constr c)
  | TacTrueCut (None,c) -> 
      hov 1 (str "Assert" ++ pr_arg pr_constr c)
  | TacTrueCut (Some id,c) -> 
      hov 1 (str "Assert" ++ spc () ++ pr_id id ++ str ":" ++ pr_constr c)
  | TacForward (false,na,c) ->
      hov 1 (str "Assert" ++ pr_name na ++ str ":=" ++ pr_constr c)
  | TacForward (true,na,c) ->
      hov 1 (str "Pose" ++ pr_name na ++ str ":=" ++ pr_constr c)
  | TacGeneralize l ->
      hov 0 (str "Generalize" ++ brk (1,1) ++ prlist_with_sep spc pr_constr l)
  | TacGeneralizeDep c ->
      hov 1 (str "Generalize" ++ spc () ++ str "Dependent" ++ spc () ++
      pr_constr c)
  | TacLetTac (id,c,cl) ->
      hov 1 (str "LetTac" ++ spc () ++ pr_id id ++ str ":=" ++
        pr_constr c ++ pr_clause_pattern pr_ident cl)
  | TacInstantiate (n,c) ->
      hov 1 (str "Instantiate" ++ pr_arg int n ++ pr_arg pr_constr c)

  (* Derived basic tactics *)
  | TacOldInduction h ->
      hov 1 (str "Induction" ++ pr_arg pr_quantified_hypothesis h)
  | TacNewInduction h ->
      hov 1 (str "NewInduction" ++ spc () ++ pr_induction_arg pr_constr h)
  | TacOldDestruct h ->
      hov 1 (str "Destruct" ++ pr_arg pr_quantified_hypothesis h)
  | TacNewDestruct h ->
      hov 1 (str "NewDestruct" ++ spc () ++ pr_induction_arg pr_constr h)
  | TacDoubleInduction (h1,h2) ->
      hov 1
        (str "Double Induction" ++ 
         pr_arg pr_quantified_hypothesis h1 ++
 	 pr_arg pr_quantified_hypothesis h2)
  | TacDecomposeAnd c ->
      hov 1 (str "Decompose Record" ++ pr_arg pr_constr c)
  | TacDecomposeOr c ->
      hov 1 (str "Decompose Sum" ++ pr_arg pr_constr c)
  | TacDecompose (l,c) ->
      hov 1 (str "Decompose" ++ spc () ++
        hov 0 (str "[" ++ prlist_with_sep spc (pr_metanum pr_ind) l
	  ++ str "]"))
  | TacSpecialize (n,c) ->
      hov 1 (str "Specialize" ++ pr_opt int n ++ pr_with_bindings c)
  | TacLApply c -> 
      hov 1 (str "LApply" ++ pr_constr c)

  (* Automation tactics *)
  | TacTrivial (Some []) as x -> pr_atom0 x
  | TacTrivial db -> hov 0 (str "Trivial" ++ pr_hintbases db)
  | TacAuto (None,Some []) as x -> pr_atom0 x
  | TacAuto (n,db) -> hov 0 (str "Auto" ++ pr_opt int n ++ pr_hintbases db)
  | TacAutoTDB None as x -> pr_atom0 x
  | TacAutoTDB (Some n) -> hov 0 (str "AutoTDB" ++ spc () ++ int n)
  | TacDestructHyp (true,(_,id)) -> hov 0 (str "CDHyp" ++ spc () ++ pr_id id)
  | TacDestructHyp (false,(_,id)) -> hov 0 (str "DHyp" ++ spc () ++ pr_id id)
  | TacDestructConcl as x -> pr_atom0 x
  | TacSuperAuto (n,l,b1,b2) ->
      hov 0 (str "SuperAuto" ++ pr_opt int n ++ pr_autoarg_adding l ++ 
             pr_autoarg_destructing b1 ++ pr_autoarg_usingTDB b2)
  | TacDAuto (n,p) ->
      hov 0 (str "Auto" ++ pr_opt int n ++ str "Decomp" ++ pr_opt int p)

  (* Context management *)
  | TacClear l ->
      hov 0
        (str "Clear" ++ brk (1,1) ++ prlist_with_sep spc (pr_metanum pr_id) l)
  | TacClearBody l ->
      hov 0
        (str "Clear" ++ brk (1,1) ++ prlist_with_sep spc (pr_metanum pr_id) l)
  | TacMove (b,(_,id1),(_,id2)) ->
      (* Rem: only b = true is available for users *)
      assert b;
      hov 1
        (str "Move" ++ brk (1,1) ++ pr_id id1 ++ spc () ++ 
	 str "after" ++ brk (1,1) ++ pr_id id2)
  | TacRename ((_,id1),(_,id2)) ->
      hov 1
        (str "Rename" ++ brk (1,1) ++ pr_id id1 ++ spc () ++ 
	 str "into" ++ brk (1,1) ++ pr_id id2)

  (* Constructors *)
  | TacLeft l -> hov 1 (str "Left" ++ pr_bindings l)
  | TacRight l -> hov 1 (str "Right" ++ pr_bindings l)
  | TacSplit l -> hov 1 (str "Split" ++ pr_bindings l)
  | TacAnyConstructor (Some t) ->
      hov 1 (str "Constructor" ++ pr_arg !pr_rawtac0 t)
  | TacAnyConstructor None as t -> pr_atom0 t
  | TacConstructor (n,l) ->
      hov 1 (str "Constructor" ++ pr_or_meta pr_intarg n ++ pr_bindings l)

  (* Conversion *)  
  | TacReduce (r,h) ->
      hov 1 (pr_red_expr (pr_constr,pr_cst) r ++ pr_clause pr_ident h)
  | TacChange (c,h) ->
      hov 1 (str "Change" ++ brk (1,1) ++ pr_constr c ++ pr_clause pr_ident h)

  (* Equivalence relations *)
  | (TacReflexivity | TacSymmetry) as x -> pr_atom0 x
  | TacTransitivity c -> str "Transitivity" ++ pr_arg pr_constr c

and pr_tactic_seq_body tl = 
  hv 0 (str "[ " ++
        prlist_with_sep (fun () -> spc () ++ str "| ") prtac tl ++ str " ]")

  (* Strictly closed atomic tactic expressions *)
and pr0 = function
  | TacFirst tl -> str "First" ++ spc () ++ pr_tactic_seq_body tl
  | TacSolve tl -> str "Solve" ++ spc () ++ pr_tactic_seq_body tl
  | TacId -> str "Idtac"
  | TacFail 0 -> str "Fail"
  | TacAtom (_,t) -> pr_atom0 t
  | TacArg c -> pr_tacarg c
  | t -> str "(" ++ prtac t ++ str ")"

  (* Semi-closed atomic tactic expressions *)
and pr1 = function
  | TacAtom (_,t) -> pr_atom1 t
  | TacFail n -> str "Fail " ++ int n
  | t -> pr0 t

  (* Orelse tactic expressions (printed as if parsed associating on the right
     though the semantics is purely associative) *)
and pr2 = function
  | TacOrelse (t1,t2) ->
      hov 1 (pr1 t1 ++ str " Orelse" ++ brk (1,1) ++ pr3 t2)
  | t -> pr1 t

  (* Non closed prefix tactic expressions *)
and pr3 = function
  | TacTry t -> hov 1 (str "Try" ++ spc () ++ pr3 t)
  | TacDo (n,t) -> hov 1 (str "Do " ++ int n ++ spc () ++ pr3 t)
  | TacRepeat t -> hov 1 (str "Repeat" ++ spc () ++ pr3 t)
  | TacProgress t -> hov 1 (str "Progress" ++ spc () ++ pr3 t)
  | TacInfo t -> hov 1 (str "Info" ++ spc () ++ pr3 t)
  | t -> pr2 t

and pr4 = function
  | t -> pr3 t

  (* THEN and THENS tactic expressions (printed as if parsed
     associating on the left though the semantics is purely associative) *)
and pr5 = function
  | TacThens (t,tl) -> 
      hov 1 (pr5 t ++ str ";" ++ spc () ++ pr_tactic_seq_body tl)
  | TacThen (t1,t2) ->
      hov 1 (pr5 t1 ++ str ";" ++ spc () ++ pr4 t2)
  | t -> pr4 t

  (* Ltac tactic expressions *)
and pr6 = function
  |(TacAtom _
  | TacThen _
  | TacThens _
  | TacFirst _
  | TacSolve _
  | TacTry _
  | TacOrelse _
  | TacDo _
  | TacRepeat _
  | TacProgress _
  | TacId
  | TacFail _
  | TacInfo _) as t -> pr5 t

  | TacAbstract (t,None) -> str "Abstract " ++ pr6 t
  | TacAbstract (t,Some s) -> 
      hov 0
       (str "Abstract " ++ pr6 t ++ spc () ++ str "using" ++ spc () ++ pr_id s)
  | TacLetRecIn (l,t) -> 
      hv 0
        (str "Rec " ++ pr_rec_clauses prtac l ++
        spc () ++ str "In" ++ fnl () ++ prtac t)
  | TacLetIn (llc,u) ->
      v 0
       (hv 0 (pr_let_clauses pr_tacarg0 llc ++ spc () ++ str "In") ++ fnl () ++ prtac u)
  | TacLetCut llc ->
      pr_let_clauses pr_tacarg0
        (List.map (fun (id,c,t) -> ((dummy_loc,id),Some c,t)) llc)
      ++ fnl ()
  | TacMatch (t,lrul) ->
      hov 0 (str "Match" ++ spc () ++ pr_may_eval Ppconstr.pr_constr t ++ spc()
        ++ str "With"
        ++ prlist
	  (fun r -> fnl () ++ str "|" ++ spc () ++ pr_match_rule true prtac r)
	lrul)
  | TacMatchContext (lr,lrul) ->
      hov 0 (
	str (if lr then "Match Reverse Context With" else "Match Context With")
	++ prlist
	  (fun r -> fnl () ++ str "|" ++ spc () ++ pr_match_rule false prtac r)
	lrul)
  | TacFun (lvar,body) ->
      hov 0 (str "Fun" ++
        prlist pr_funvar lvar ++ spc () ++ str "->" ++ spc () ++ prtac body)
  | TacFunRec t ->
      hov 0 (str "Rec " ++ pr_rec_clause prtac t)

  | TacArg c -> pr_tacarg c

and pr_tacarg0 = function
  | TacDynamic (_,t) -> str ("<dynamic ["^(Dyn.tag t)^"]>")
  | MetaNumArg (_,n) -> str ("?" ^ string_of_int n )
  | MetaIdArg (_,s) -> str ("$" ^ s)
  | TacVoid -> str "()"
  | Reference (RQualid (_,qid)) -> pr_qualid qid
  | Reference (RIdent (_,id)) -> pr_id id
  | ConstrMayEval (ConstrTerm c) -> str "'" ++ pr_constr c
  | ConstrMayEval c -> pr_may_eval pr_constr c
  | Integer n -> int n
(*
  | Tac of
      'c * (Coqast.t,qualid or_metanum, identifier or_metaid) gen_tactic_expr
*)
  | (TacCall _ | Tacexp _) as t -> str "(" ++ pr_tacarg1 t ++ str ")"

and pr_tacarg1 = function
  | TacCall (_,f,l) ->
      hov 0 (pr_tacarg0 f ++ spc () ++ prlist_with_sep spc pr_tacarg0 l)
  | Tacexp t -> !pr_rawtac t
  | t -> pr_tacarg0 t

and pr_tacarg x = pr_tacarg1 x

and prtac x = pr6 x

in (prtac,pr0,pr_match_rule)

let (pr_raw_tactic,pr_raw_tactic0,pr_match_rule) =
  make_pr_tac
    (Ppconstr.pr_constr,
     pr_metanum pr_qualid,
     pr_qualid,
     pr_or_meta (fun (loc,id) -> pr_id id),
     pr_raw_extend)

let _ = pr_rawtac := pr_raw_tactic
let _ = pr_rawtac0 := pr_raw_tactic0

let (pr_tactic,_,_) =
  make_pr_tac
    (Printer.prterm,
     pr_evaluable_reference,
     pr_inductive,
     pr_id,
     pr_extend)
