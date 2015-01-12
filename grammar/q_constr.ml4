(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4deps: "tools/compat5b.cmo" i*)

open Q_util
open Compat
open Pcaml
open PcamlSig (* necessary for camlp4 *)

let loc = CompatLoc.ghost
let dloc = <:expr< Loc.ghost >>

let apply_ref f l =
  <:expr<
    Glob_term.GApp ($dloc$, Glob_term.GRef ($dloc$, Lazy.force $f$, None), $mlexpr_of_list (fun x -> x) l$)
  >>

EXTEND
  GLOBAL: expr;
  expr:
    [ [ "PATTERN"; "["; c = constr; "]" ->
      <:expr< snd (Patternops.pattern_of_glob_constr $c$) >> ] ]
  ;
  sort:
    [ [ "Set"  -> Misctypes.GSet
      | "Prop" -> Misctypes.GProp
      | "Type" -> Misctypes.GType [] ] ]
  ;
  ident:
    [ [ s = string -> <:expr< Names.Id.of_string $str:s$ >> ] ]
  ;
  name:
    [ [ "_" -> <:expr< Anonymous >> | id = ident -> <:expr< Name $id$ >> ] ]
  ;
  string:
    [ [ s = UIDENT -> s | s = LIDENT -> s ] ]
  ;
  constr:
    [ "200" RIGHTA
      [ LIDENT "forall"; id = ident; ":"; c1 = constr; ","; c2 = constr ->
        <:expr< Glob_term.GProd ($dloc$,Name $id$,Decl_kinds.Explicit,$c1$,$c2$) >>
      | "fun"; id = ident; ":"; c1 = constr; "=>"; c2 = constr ->
        <:expr< Glob_term.GLambda ($dloc$,Name $id$,Decl_kinds.Explicit,$c1$,$c2$) >>
      | "let"; id = ident; ":="; c1 = constr; "in"; c2 = constr ->
        <:expr< Glob_term.RLetin ($dloc$,Name $id$,$c1$,$c2$) >>
      (* fix todo *)
      ]
    | "100" RIGHTA
      [ c1 = constr; ":"; c2 = SELF ->
        <:expr< Glob_term.GCast($dloc$,$c1$,DEFAULTcast,$c2$) >> ]
    | "90" RIGHTA
      [ c1 = constr; "->"; c2 = SELF ->
        <:expr< Glob_term.GProd ($dloc$,Anonymous,Decl_kinds.Explicit,$c1$,$c2$) >> ]
    | "75" RIGHTA
      [ "~"; c = constr ->
        apply_ref <:expr< coq_not_ref >> [c] ]
    | "70" RIGHTA
      [ c1 = constr; "="; c2 = NEXT; ":>"; t = NEXT ->
        apply_ref <:expr< coq_eq_ref >> [t;c1;c2] ]
    | "10" LEFTA
      [ f = constr; args = LIST1 NEXT ->
        let args = mlexpr_of_list (fun x -> x) args in
        <:expr< Glob_term.GApp ($dloc$,$f$,$args$) >> ]
    | "0"
      [ s = sort -> <:expr< Glob_term.GSort ($dloc$,s) >>
      | id = ident -> <:expr< Glob_term.GVar ($dloc$,$id$) >>
      | "_" -> <:expr< Glob_term.GHole ($dloc$,Evar_kinds.QuestionMark (Evar_kinds.Define False),Misctypes.IntroAnonymous,None) >>
      | "?"; id = ident -> <:expr< Glob_term.GPatVar($dloc$,(False,$id$)) >>
      | "{"; c1 = constr; "}"; "+"; "{"; c2 = constr; "}" ->
          apply_ref <:expr< coq_sumbool_ref >> [c1;c2]
      | "%"; e = string -> <:expr< Glob_term.GRef ($dloc$,Lazy.force $lid:e$, None) >>
      | c = match_constr -> c
      | "("; c = constr LEVEL "200"; ")" -> c ] ]
  ;
  match_constr:
    [ [ "match"; c = constr LEVEL "100"; (ty,nal) = match_type;
        "with"; OPT"|"; br = LIST0 eqn SEP "|"; "end" ->
          let br = mlexpr_of_list (fun x -> x) br in
     <:expr< Glob_term.GCases ($dloc$,$ty$,[($c$,$nal$)],$br$) >>
    ] ]
  ;
  match_type:
    [ [ "as"; id = ident; "in"; ind = LIDENT; nal = LIST0 name;
        "return"; ty = constr LEVEL "100" ->
          let nal = mlexpr_of_list (fun x -> x) nal in
          <:expr< Some $ty$ >>,
          <:expr< (Name $id$, Some ($dloc$,$lid:ind$,$nal$)) >>
      | -> <:expr< None >>, <:expr< (Anonymous, None) >> ] ]
  ;
  eqn:
    [ [ (lid,pl) = pattern; "=>"; rhs = constr ->
        let lid = mlexpr_of_list (fun x -> x) lid in
        <:expr< ($dloc$,$lid$,[$pl$],$rhs$) >>
    ] ]
  ;
  pattern:
    [ [ "%"; e = string; lip = LIST0 patvar ->
        let lp = mlexpr_of_list (fun (_,x) -> x) lip in
        let lid = List.flatten (List.map fst lip) in
        lid, <:expr< Glob_term.PatCstr ($dloc$,$lid:e$,$lp$,Anonymous) >>
      | p = patvar -> p
      | "("; p = pattern; ")" -> p ] ]
  ;
  patvar:
    [ [ "_" -> [], <:expr< Glob_term.PatVar ($dloc$,Anonymous) >>
      | id = ident -> [id], <:expr< Glob_term.PatVar ($dloc$,Name $id$) >>
    ] ]
  ;
  END;;

(* Example
open Coqlib
let a = PATTERN [ match ?X with %path_of_S n => n | %path_of_O => ?X end ]
*)
