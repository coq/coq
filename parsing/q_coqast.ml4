(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

let dummy_loc = (0,0)

let is_meta s = String.length s > 0 && s.[0] == '$'

let not_impl name x =
  let desc =
    if Obj.is_block (Obj.repr x) then
      "tag = " ^ string_of_int (Obj.tag (Obj.repr x))
    else 
      "int_val = " ^ string_of_int (Obj.magic x)
  in
  failwith ("<Q_coqast." ^ name ^ ", not impl: " ^ desc)

let purge_str s =
  if String.length s == 0 || s.[0] <> '$' then s
  else String.sub s 1 (String.length s - 1)

let anti loc x =
  let e =
    let loc = (1, snd loc - fst loc) in <:expr< $lid:purge_str x$ >>
  in
  <:expr< $anti:e$ >>

(* [expr_of_ast] contributes to translate g_*.ml4 files into g_*.ppo *)
(* This is where $id's (and macros) in ast are translated in ML variables *)
(* which will bind their actual ast value *)

let rec expr_of_ast = function
  | Coqast.Nmeta loc id -> anti loc id
  | Coqast.Id loc id when is_meta id -> <:expr< Coqast.Id loc $anti loc id$ >>
  | Coqast.Node _ "$VAR" [Coqast.Nmeta loc x] ->
      <:expr< let s = $anti loc x$ in
      if String.length s > 0 && String.sub s 0 1 = "$" then
	failwith "Wrong ast: $VAR should not be bound to a meta variable"
      else
	Coqast.Nvar loc (Identifier.id_of_string s) >>
  | Coqast.Node _ "$PATH" [Coqast.Nmeta loc x] ->
      <:expr< Coqast.Path loc $anti loc x$ >>
  | Coqast.Node _ "$ID" [Coqast.Nmeta loc x] ->
      <:expr< Coqast.Id loc $anti loc x$ >>
  | Coqast.Node _ "$STR" [Coqast.Nmeta loc x] ->
      <:expr< Coqast.Str loc $anti loc x$ >>
(* Obsolète
  | Coqast.Node _ "$SLAM" [Coqast.Nmeta loc idl; y] ->
      <:expr<
      List.fold_right (Pcoq.slam_ast loc) $anti loc idl$ $expr_of_ast y$ >>
*)
  | Coqast.Node loc "$ABSTRACT" [Coqast.Str _ s; x; y] ->
      <:expr<
      Pcoq.abstract_binders_ast loc $str:s$ $expr_of_ast x$ $expr_of_ast y$ >>
  | Coqast.Node loc nn al ->
      let e = expr_list_of_ast_list al in
      <:expr< Coqast.Node loc $str:nn$ $e$ >>
  | Coqast.Nvar loc id ->
      <:expr< Coqast.Nvar loc (Identifier.id_of_string $str:Identifier.string_of_id id$) >>
  | Coqast.Slam loc None a ->
      <:expr< Coqast.Slam loc None $expr_of_ast a$ >>
  | Coqast.Smetalam loc s a ->
      <:expr< 
      match $anti loc s$ with
	[ Coqast.Nvar _ id -> Coqast.Slam loc (Some id) $expr_of_ast a$
	| Coqast.Nmeta _ s -> Coqast.Smetalam loc s $expr_of_ast a$
	| _ -> failwith "Slam expects a var or a metavar" ] >>
  | Coqast.Slam loc (Some s) a ->
      let se = <:expr< Identifier.id_of_string $str:Identifier.string_of_id s$ >> in
      <:expr< Coqast.Slam loc (Some $se$) $expr_of_ast a$ >>
  | Coqast.Num loc i -> <:expr< Coqast.Num loc $int:string_of_int i$ >>
  | Coqast.Id loc id -> <:expr< Coqast.Id loc $str:id$ >>
  | Coqast.Str loc str -> <:expr< Coqast.Str loc $str:str$ >>
  | Coqast.Path loc qid ->
      let l,a,_ = Libnames.repr_path qid in
      let expr_of_modid id =
	<:expr< Identifier.id_of_string $str:Identifier.string_of_id id$ >> in
      let e = List.map expr_of_modid (Names.repr_dirpath l) in
      let e = expr_list_of_var_list e in 
      <:expr< Coqast.Path loc (Libnames.make_path (Names.make_dirpath
      $e$) (Identifier.id_of_string $str:Identifier.string_of_id a$) Libnames.CCI) >> 
  | Coqast.Dynamic _ _ ->
      failwith "Q_Coqast: dynamic: not implemented"

and expr_list_of_ast_list al =
  List.fold_right
    (fun a e2 -> match a with
       | (Coqast.Node _ "$LIST" [Coqast.Nmeta locv pv]) ->
           let e1 = anti locv pv in
           let loc = (fst(MLast.loc_of_expr e1), snd(MLast.loc_of_expr e2)) in
	     if e2 = (let loc = dummy_loc in <:expr< [] >>)
	     then <:expr< $e1$ >>
	     else <:expr< ( $lid:"@"$ $e1$ $e2$) >>
       | _ ->
           let e1 = expr_of_ast a in
           let loc = (fst(MLast.loc_of_expr e1), snd(MLast.loc_of_expr e2)) in
	   <:expr< [$e1$ :: $e2$] >> )
    al (let loc = dummy_loc in <:expr< [] >>)

and expr_list_of_var_list sl =
  let loc = dummy_loc in
  List.fold_right
    (fun e1 e2 ->
       let loc = (fst (MLast.loc_of_expr e1), snd (MLast.loc_of_expr e2)) in
       <:expr< [$e1$ :: $e2$] >>)
    sl <:expr< [] >>
  
let rec patt_of_expr e =
  let loc = MLast.loc_of_expr e in
  match e with
    | <:expr< $e1$.$e2$ >> -> <:patt< $patt_of_expr e1$.$patt_of_expr e2$ >>
    | <:expr< $e1$ $e2$ >> -> <:patt< $patt_of_expr e1$ $patt_of_expr e2$ >>
    | <:expr< loc >> -> <:patt< _ >>
    | <:expr< $lid:s$ >> -> <:patt< $lid:s$ >>
    | <:expr< $uid:s$ >> -> <:patt< $uid:s$ >>
    | <:expr< $str:s$ >> -> <:patt< $str:s$ >>
    | <:expr< $anti:e$ >> -> <:patt< $anti:patt_of_expr e$ >>
    | _ -> not_impl "patt_of_expr" e

let f e =
  let ee s =
    expr_of_ast (Pcoq.Gram.Entry.parse e
                     (Pcoq.Gram.parsable (Stream.of_string s)))
  in
  let ep s = patt_of_expr (ee s) in
  Quotation.ExAst (ee, ep)

let _ = 
  Quotation.add "constr" (f Pcoq.Constr.constr_eoi);
  Quotation.add "tactic" (f Pcoq.Tactic.tactic_eoi);
  Quotation.add "vernac" (f Pcoq.Vernac_.vernac_eoi);
  Quotation.add "ast" (f Pcoq.Prim.ast_eoi);
  Quotation.default := "constr"

