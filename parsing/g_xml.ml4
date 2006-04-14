(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Pp
open Util
open Names
open Term
open Pcoq
open Rawterm
open Genarg
open Tacexpr
open Libnames

open Nametab

(* Generic xml parser without raw data *)

type attribute = string * (loc * string)
type xml = XmlTag of loc * string * attribute list * xml list

let check_tags loc otag ctag =
  if otag <> ctag then
    user_err_loc (loc,"",str "closing xml tag " ++ str ctag ++ 
      str "does not match open xml tag " ++ str otag)

let xml_eoi = (Gram.Entry.create "xml_eoi" : xml Gram.Entry.e)

GEXTEND Gram
  GLOBAL: xml_eoi;

  xml_eoi:
    [ [ x = xml; EOI -> x ] ]
  ;
  xml:
    [ [ "<"; otag = IDENT; attrs = LIST0 attr; ">"; l = LIST1 xml;
        "<"; "/"; ctag = IDENT; ">"  ->
	  check_tags loc otag ctag;
	  XmlTag (loc,ctag,attrs,l)
      | "<"; tag = IDENT; attrs = LIST0 attr; "/"; ">" ->
	  XmlTag (loc,tag,attrs,[])
    ] ]
  ;
  attr:
    [ [ name = IDENT; "="; data = STRING -> (name, (loc, data)) ] ]
  ;
END

(* Interpreting attributes *)

let nmtoken (loc,a) =
  try int_of_string a
  with Failure _ -> user_err_loc (loc,"",str "nmtoken expected")
  
let interp_xml_attr_qualid = function
  | "uri", s -> qualid_of_string s
  | _ -> error "Ill-formed xml attribute"

let get_xml_attr s al = 
  try List.assoc s al
  with Not_found -> error ("No attribute "^s)

(* Interpreting specific attributes *)

let ident_of_cdata (loc,a) = id_of_string a

let uri_of_data s =
  let n = String.index s ':' in
  let p = String.index s '.' in
  let s = String.sub s (n+2) (p-n-2) in
  for i=0 to String.length s - 1 do if s.[i]='/' then s.[i]<-'.' done;
  qualid_of_string s

let constant_of_cdata (loc,a) = Nametab.locate_constant (uri_of_data a)

let global_of_cdata (loc,a) = Nametab.locate (uri_of_data a)

let inductive_of_cdata a = match global_of_cdata a with
    | IndRef (kn,_) -> kn
    | _ -> failwith "kn"

let ltacref_of_cdata (loc,a) = (loc,locate_tactic (uri_of_data a))

let sort_of_cdata (loc,a) = match a with
  | "Prop" -> RProp Null
  | "Set" -> RProp Pos
  | "Type" -> RType None
  | _ -> user_err_loc (loc,"",str "sort expected")

let get_xml_sort al = sort_of_cdata (get_xml_attr "value" al)

let get_xml_inductive_kn al = inductive_of_cdata (get_xml_attr "uri" al)

let get_xml_constant al = constant_of_cdata (get_xml_attr "uri" al)

let get_xml_inductive al =
  (get_xml_inductive_kn al, nmtoken (get_xml_attr "noType" al))

let get_xml_constructor al =
  (get_xml_inductive al, nmtoken (get_xml_attr "noConstr" al))

let get_xml_name al =
  try Name (ident_of_cdata (List.assoc "binder" al))
  with Not_found -> Anonymous

let get_xml_ident al = ident_of_cdata (get_xml_attr "binder" al)

let get_xml_noFun al = nmtoken (get_xml_attr "noFun" al)

(* Interpreting constr as a rawconstr *)

let rec interp_xml_constr = function
  | XmlTag (loc,"REL",al,[]) ->
      RVar (loc, get_xml_ident al)
  | XmlTag (loc,"VAR",al,[]) -> failwith ""
  | XmlTag (loc,"LAMBDA",al,[x1;x2]) ->
      let na,t = interp_xml_decl x1 in
      RLambda (loc, na, t, interp_xml_target x2)
  | XmlTag (loc,"PROD",al,[x1;x2]) ->
      let na,t = interp_xml_decl x1 in
      RProd (loc, na, t, interp_xml_target x2)
  | XmlTag (loc,"LETIN",al,[x1;x2]) ->
      let na,t = interp_xml_def x1 in
      RLetIn (loc, na, t, interp_xml_target x2) 
  | XmlTag (loc,"APPLY",_,x::xl) ->
      RApp (loc, interp_xml_constr x, List.map interp_xml_constr xl)
  | XmlTag (loc,"META",al,xl) ->
      failwith "META: TODO"
  | XmlTag (loc,"CONST",al,[]) ->
      RRef (loc, ConstRef (get_xml_constant al))
  | XmlTag (loc,"MUTCASE",al,x::y::yl) -> (* BUGGE *)
      failwith "XML MUTCASE TO DO";
(*
      ROrderedCase (loc,RegularStyle,Some (interp_xml_patternsType x),
      interp_xml_inductiveTerm y,
      Array.of_list (List.map interp_xml_pattern yl),
      ref None)
*)
  | XmlTag (loc,"MUTIND",al,[]) ->
      RRef (loc, IndRef (get_xml_inductive al))
  | XmlTag (loc,"MUTCONSTRUCT",al,[]) ->
      RRef (loc, ConstructRef (get_xml_constructor al))
  | XmlTag (loc,"FIX",al,xl) ->
      let li,lnct = List.split (List.map interp_xml_FixFunction xl) in
      let ln,lc,lt = list_split3 lnct in
      RRec (loc, RFix (Array.of_list li, get_xml_noFun al), Array.of_list ln, [||], Array.of_list lc, Array.of_list lt)
  | XmlTag (loc,"COFIX",al,xl) ->
      let ln,lc,lt = list_split3 (List.map interp_xml_CoFixFunction xl) in
      RRec (loc, RCoFix (get_xml_noFun al), Array.of_list ln, [||], Array.of_list lc, Array.of_list lt)
  | XmlTag (loc,"CAST",al,[x1;x2]) ->
      RCast (loc, interp_xml_term x1, DEFAULTcast, interp_xml_type x2)
  | XmlTag (loc,"SORT",al,[]) ->
      RSort (loc, get_xml_sort al)
  | XmlTag (loc,s,_,_) -> user_err_loc (loc,"", str "Unexpected tag " ++ str s)

and interp_xml_tag s = function
  | XmlTag (loc,tag,al,xl) when tag=s -> (loc,al,xl)
  | XmlTag (loc,tag,_,_) -> user_err_loc (loc, "", 
    str "Expect tag " ++ str s ++ str " but find " ++ str s)

and interp_xml_constr_alias s x =
  match interp_xml_tag s x with
    | (_,_,[x]) -> interp_xml_constr x
    | (loc,_,_) -> 
        user_err_loc (loc,"",str "wrong number of arguments (expect one)")

and interp_xml_term x = interp_xml_constr_alias "term" x
and interp_xml_type x = interp_xml_constr_alias "type" x
and interp_xml_target x = interp_xml_constr_alias "target" x
and interp_xml_body x = interp_xml_constr_alias "body" x
and interp_xml_pattern x = interp_xml_constr_alias "pattern" x
and interp_xml_patternsType x = interp_xml_constr_alias "patternsType" x
and interp_xml_inductiveTerm x = interp_xml_constr_alias "inductiveTerm" x

and interp_xml_decl_alias s x =
  match interp_xml_tag s x with
    | (_,al,[x]) -> (get_xml_name al, interp_xml_constr x)
    | (loc,_,_) -> 
        user_err_loc (loc,"",str "wrong number of arguments (expect one)")

and interp_xml_def x = interp_xml_decl_alias "def" x
and interp_xml_decl x = interp_xml_decl_alias "decl" x

and interp_xml_recursionOrder x =
  let (loc, al, l) = interp_xml_tag "RecursionOrder" x in
  let (locs, s) = get_xml_attr "type" al in
    match s with
	"Structural" -> 
	  (match l with [] -> RStructRec
	     | _ -> user_err_loc (loc, "", str "wrong number of arguments (expected none)"))
      | "WellFounded" -> 
	  (match l with
	       [c] -> RWfRec (interp_xml_type c)
	     | _ -> user_err_loc (loc, "", str "wrong number of arguments (expected one)"))
      | _ ->
          user_err_loc (locs,"",str "invalid recursion order")


and interp_xml_FixFunction x =
  match interp_xml_tag "FixFunction" x with
  | (loc,al,[x1;x2;x3]) ->
      ((Some (nmtoken (get_xml_attr "recIndex" al)),
	interp_xml_recursionOrder x1),
       (get_xml_ident al, interp_xml_type x2, interp_xml_body x3))
  | (loc,al,[x1;x2]) -> (* For backwards compatibility *)
      ((Some (nmtoken (get_xml_attr "recIndex" al)), RStructRec),
       (get_xml_ident al, interp_xml_type x1, interp_xml_body x2))
  | (loc,_,_) -> 
        user_err_loc (loc,"",str "wrong number of arguments (expect one)")

and interp_xml_CoFixFunction x =
  match interp_xml_tag "CoFixFunction" x with
  | (loc,al,[x1;x2]) ->
      (get_xml_ident al, interp_xml_type x1, interp_xml_body x2)
    | (loc,_,_) -> 
        user_err_loc (loc,"",str "wrong number of arguments (expect one)")

(* Interpreting tactic argument *)

let rec (interp_xml_tactic_expr : xml -> glob_tactic_expr) = function
  | XmlTag (loc,"TACARG",[],[x]) ->
      TacArg (interp_xml_tactic_arg x)
  | _ -> error "Ill-formed xml tree"

and interp_xml_tactic_arg = function
  | XmlTag (loc,"TERM",[],[x]) ->
      ConstrMayEval (ConstrTerm (interp_xml_constr x,None))
  | XmlTag (loc,"CALL",al,xl) ->
      let ltacref = ltacref_of_cdata (get_xml_attr "uri" al) in
      TacCall(loc,ArgArg ltacref,List.map interp_xml_tactic_arg xl)
(*
  | XmlTag (loc,"TACTIC",[],[x]) ->
      Tacexp (interp_xml_tactic_expr x)
  | _ -> error "Ill-formed xml tree"
*)
  | XmlTag (loc,s,_,_) -> user_err_loc (loc,"", str "Unexpected tag " ++ str s)

let parse_tactic_arg ch =
  interp_xml_tactic_arg
    (Pcoq.Gram.Entry.parse xml_eoi
        (Pcoq.Gram.parsable (Stream.of_channel ch)))
