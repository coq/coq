(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Compat
open Pp
open Errors
open Util
open Names
open Pcoq
open Glob_term
open Tacexpr
open Libnames
open Globnames
open Detyping
open Misctypes
open Decl_kinds
open Genredexpr
open Tok (* necessary for camlp4 *)

(* Generic xml parser without raw data *)

type attribute = string * (Loc.t * string)
type xml = XmlTag of Loc.t * string * attribute list * xml list

let check_tags loc otag ctag =
  if not (String.equal otag ctag) then
    user_err_loc (loc,"",str "closing xml tag " ++ str ctag ++
      str "does not match open xml tag " ++ str otag ++ str ".")

let xml_eoi = (Gram.entry_create "xml_eoi" : xml Gram.entry)

GEXTEND Gram
  GLOBAL: xml_eoi;

  xml_eoi:
    [ [ x = xml; EOI -> x ] ]
  ;
  xml:
    [ [ "<"; otag = IDENT; attrs = LIST0 attr; ">"; l = LIST1 xml;
        "<"; "/"; ctag = IDENT; ">"  ->
	  check_tags (!@loc) otag ctag;
	  XmlTag (!@loc,ctag,attrs,l)
      | "<"; tag = IDENT; attrs = LIST0 attr; "/"; ">" ->
	  XmlTag (!@loc,tag,attrs,[])
    ] ]
  ;
  attr:
    [ [ name = IDENT; "="; data = STRING -> (name, (!@loc, data)) ] ]
  ;
END

(* Errors *)

let error_bad_arity loc n =
  let s = match n with 0 -> "none" | 1 -> "one" | 2 -> "two" | _ -> "many" in
  user_err_loc (loc,"",str ("wrong number of arguments (expect "^s^")."))

(* Interpreting attributes *)

let nmtoken (loc,a) =
  try int_of_string a
  with Failure _ -> user_err_loc (loc,"",str "nmtoken expected.")

let get_xml_attr s al =
  try String.List.assoc s al
  with Not_found -> error ("No attribute "^s)

(* Interpreting specific attributes *)

let ident_of_cdata (loc,a) = Id.of_string a

let uri_of_data s =
  try
    let n = String.index s ':' in
    let p = String.index s '.' in
    let s = String.sub s (n+2) (p-n-2) in
    for i = 0 to String.length s - 1 do
      match s.[i] with
      | '/' -> s.[i] <- '.'
      | _ -> ()
    done;
    qualid_of_string s
  with Not_found | Invalid_argument _ ->
    error ("Malformed URI \""^s^"\"")

let constant_of_cdata (loc,a) =
  let q = uri_of_data a in
  try Nametab.locate_constant q
  with Not_found -> error ("No such constant "^string_of_qualid q)

let global_of_cdata (loc,a) =
  let q = uri_of_data a in
  try Nametab.locate q
  with Not_found -> error ("No such global "^string_of_qualid q)

let inductive_of_cdata a = match global_of_cdata a with
  | IndRef (kn,_) -> kn
  | _ -> error (string_of_qualid (uri_of_data (snd a)) ^" is not an inductive")

let ltacref_of_cdata (loc,a) =
  let q = uri_of_data a in
  try (loc,Nametab.locate_tactic q)
  with Not_found -> error ("No such ltac "^string_of_qualid q)

let sort_of_cdata (loc,a) = match a with
  | "Prop" -> GProp
  | "Set" -> GSet
  | "Type" -> GType None
  | _ -> user_err_loc (loc,"",str "sort expected.")

let get_xml_sort al = sort_of_cdata (get_xml_attr "value" al)

let get_xml_inductive_kn al =
  inductive_of_cdata (* uriType apparent synonym of uri *)
    (try get_xml_attr "uri" al
     with UserError _ -> get_xml_attr "uriType" al)

let get_xml_constant al = constant_of_cdata (get_xml_attr "uri" al)

let get_xml_inductive al =
  (get_xml_inductive_kn al, nmtoken (get_xml_attr "noType" al))

let get_xml_constructor al =
  (get_xml_inductive al, nmtoken (get_xml_attr "noConstr" al))

let get_xml_binder al =
  try Name (ident_of_cdata (String.List.assoc "binder" al))
  with Not_found -> Anonymous

let get_xml_ident al = ident_of_cdata (get_xml_attr "binder" al)

let get_xml_name al = ident_of_cdata (get_xml_attr "name" al)

let get_xml_noFun al = nmtoken (get_xml_attr "noFun" al)

let get_xml_no al = Evar.unsafe_of_int (nmtoken (get_xml_attr "no" al))

(* A leak in the xml dtd: arities of constructor need to know global env *)

let compute_branches_lengths ind =
  let (_,mip) = Inductive.lookup_mind_specif (Global.env()) ind in
  mip.Declarations.mind_consnrealdecls

let compute_inductive_ndecls ind =
  Inductiveops.inductive_nrealdecls ind

(* Interpreting constr as a glob_constr *)

let rec interp_xml_constr = function
  | XmlTag (loc,"REL",al,[]) ->
      GVar (loc, get_xml_ident al)
  | XmlTag (loc,"VAR",al,[]) ->
      error "XML parser: unable to interp free variables"
  | XmlTag (loc,"LAMBDA",al,(_::_ as xl)) ->
      let body,decls = List.sep_last xl in
      let ctx = List.map interp_xml_decl decls in
      List.fold_right (fun (na,t) b -> GLambda (loc, na, Explicit, t, b))
	ctx (interp_xml_target body)
  | XmlTag (loc,"PROD",al,(_::_ as xl)) ->
      let body,decls = List.sep_last xl in
      let ctx = List.map interp_xml_decl decls in
      List.fold_right (fun (na,t) b -> GProd (loc, na, Explicit, t, b))
	ctx (interp_xml_target body)
  | XmlTag (loc,"LETIN",al,(_::_ as xl)) ->
      let body,defs = List.sep_last xl in
      let ctx = List.map interp_xml_def defs in
      List.fold_right (fun (na,t) b -> GLetIn (loc, na, t, b))
        ctx (interp_xml_target body)
  | XmlTag (loc,"APPLY",_,x::xl) ->
      GApp (loc, interp_xml_constr x, List.map interp_xml_constr xl)
  | XmlTag (loc,"instantiate",_,
      (XmlTag (_,("CONST"|"MUTIND"|"MUTCONSTRUCT"),_,_) as x)::xl) ->
      GApp (loc, interp_xml_constr x, List.map interp_xml_arg xl)
  | XmlTag (loc,"META",al,xl) ->
      GEvar (loc, get_xml_name al, Some (List.map interp_xml_substitution xl))
  | XmlTag (loc,"CONST",al,[]) ->
      GRef (loc, ConstRef (get_xml_constant al), None)
  | XmlTag (loc,"MUTCASE",al,x::y::yl) ->
      let ind = get_xml_inductive al in
      let p = interp_xml_patternsType x in
      let tm = interp_xml_inductiveTerm y in
      let vars = compute_branches_lengths ind in
      let brs = List.map_i (fun i c -> (i,vars.(i),interp_xml_pattern c)) 0 yl
      in
      let mat = simple_cases_matrix_of_branches ind brs in
      let n = compute_inductive_ndecls ind in
      let nal,rtn = return_type_of_predicate ind n p in
      GCases (loc,RegularStyle,rtn,[tm,nal],mat)
  | XmlTag (loc,"MUTIND",al,[]) ->
      GRef (loc, IndRef (get_xml_inductive al), None)
  | XmlTag (loc,"MUTCONSTRUCT",al,[]) ->
      GRef (loc, ConstructRef (get_xml_constructor al), None)
  | XmlTag (loc,"FIX",al,xl) ->
      let li,lnct = List.split (List.map interp_xml_FixFunction xl) in
      let ln,lc,lt = List.split3 lnct in
      let lctx = List.map (fun _ -> []) ln in
      GRec (loc, GFix (Array.of_list li, get_xml_noFun al), Array.of_list ln, Array.of_list lctx, Array.of_list lc, Array.of_list lt)
  | XmlTag (loc,"COFIX",al,xl) ->
      let ln,lc,lt = List.split3 (List.map interp_xml_CoFixFunction xl) in
      GRec (loc, GCoFix (get_xml_noFun al), Array.of_list ln, [||], Array.of_list lc, Array.of_list lt)
  | XmlTag (loc,"CAST",al,[x1;x2]) ->
      GCast (loc, interp_xml_term x1, CastConv (interp_xml_type x2))
  | XmlTag (loc,"SORT",al,[]) ->
      GSort (loc, get_xml_sort al)
  | XmlTag (loc,s,_,_) ->
      user_err_loc (loc,"", str "Unexpected tag " ++ str s ++ str ".")

and interp_xml_tag s = function
  | XmlTag (loc,tag,al,xl) when String.equal tag s -> (loc,al,xl)
  | XmlTag (loc,tag,_,_) -> user_err_loc (loc, "",
    str "Expect tag " ++ str s ++ str " but find " ++ str s ++ str ".")

and interp_xml_constr_alias s x =
  match interp_xml_tag s x with
    | (_,_,[x]) -> interp_xml_constr x
    | (loc,_,_) -> error_bad_arity loc 1

and interp_xml_term x = interp_xml_constr_alias "term" x
and interp_xml_type x = interp_xml_constr_alias "type" x
and interp_xml_target x = interp_xml_constr_alias "target" x
and interp_xml_body x = interp_xml_constr_alias "body" x
and interp_xml_pattern x = interp_xml_constr_alias "pattern" x
and interp_xml_patternsType x = interp_xml_constr_alias "patternsType" x
and interp_xml_inductiveTerm x = interp_xml_constr_alias "inductiveTerm" x
and interp_xml_arg x = interp_xml_constr_alias "arg" x
and interp_xml_substitution x =
  match interp_xml_tag "substitution" x with
    _, al, [x] -> get_xml_name al, interp_xml_constr x
  | loc, _, _ -> error_bad_arity loc 1
                     (* no support for empty substitution from official dtd *)

and interp_xml_decl_alias s x =
  match interp_xml_tag s x with
    | (_,al,[x]) -> (get_xml_binder al, interp_xml_constr x)
    | (loc,_,_) -> error_bad_arity loc 1

and interp_xml_def x = interp_xml_decl_alias "def" x
and interp_xml_decl x = interp_xml_decl_alias "decl" x

and interp_xml_recursionOrder x =
  let (loc, al, l) = interp_xml_tag "RecursionOrder" x in
  let (locs, s) = get_xml_attr "type" al in
  match s, l with
  | "Structural", [] -> GStructRec
  | "Structural", _ -> error_bad_arity loc 0
  | "WellFounded", [c] -> GWfRec (interp_xml_type c)
  | "WellFounded", _ -> error_bad_arity loc 1
  | "Measure", [m;r] -> GMeasureRec (interp_xml_type m, Some (interp_xml_type r))
  | "Measure", _ -> error_bad_arity loc 2
  | _ -> user_err_loc (locs,"",str "Invalid recursion order.")

and interp_xml_FixFunction x =
  match interp_xml_tag "FixFunction" x with
  | (loc,al,[x1;x2;x3]) -> (* Not in official cic.dtd, not in constr *)
      ((Some (nmtoken (get_xml_attr "recIndex" al)),
	interp_xml_recursionOrder x1),
       (get_xml_name al, interp_xml_type x2, interp_xml_body x3))
  | (loc,al,[x1;x2]) ->
      ((Some (nmtoken (get_xml_attr "recIndex" al)), GStructRec),
       (get_xml_name al, interp_xml_type x1, interp_xml_body x2))
  | (loc,_,_) ->
      error_bad_arity loc 1

and interp_xml_CoFixFunction x =
  match interp_xml_tag "CoFixFunction" x with
  | (loc,al,[x1;x2]) ->
      (get_xml_name al, interp_xml_type x1, interp_xml_body x2)
    | (loc,_,_) ->
	error_bad_arity loc 1

(* Interpreting tactic argument *)

let rec interp_xml_tactic_arg = function
  | XmlTag (loc,"TERM",[],[x]) ->
      ConstrMayEval (ConstrTerm (interp_xml_constr x,None))
  | XmlTag (loc,"CALL",al,xl) ->
      let ltacref = ltacref_of_cdata (get_xml_attr "uri" al) in
      TacCall(loc,ArgArg ltacref,List.map interp_xml_tactic_arg xl)
  | XmlTag (loc,s,_,_) ->
      user_err_loc (loc,"", str "Unexpected tag " ++ str s ++ str ".")

let parse_tactic_arg ch =
  interp_xml_tactic_arg
    (Pcoq.Gram.entry_parse xml_eoi
       (Pcoq.Gram.parsable (Stream.of_channel ch)))
