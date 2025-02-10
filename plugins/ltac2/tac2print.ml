(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Pp
open Names
open Tac2expr
open Tac2env

let pr_tacref avoid kn =
  try Libnames.pr_qualid (Tac2env.shortest_qualid_of_ltac avoid (TacConstant kn))
  with Not_found when !Flags.in_debugger || KNmap.mem kn (Tac2env.globals()) ->
    str (ModPath.to_string (KerName.modpath kn))
    ++ str"." ++ Label.print (KerName.label kn)
    ++ if !Flags.in_debugger then mt() else str " (* local *)"

(** Utils *)

let change_kn_label kn id =
  let mp = KerName.modpath kn in
  KerName.make mp (Label.of_id id)

let paren p = hov 2 (str "(" ++ p ++ str ")")

let t_list =
  KerName.make Tac2env.rocq_prefix (Label.of_id (Id.of_string "list"))

let c_nil = change_kn_label t_list (Id.of_string_soft "[]")
let c_cons = change_kn_label t_list (Id.of_string_soft "::")

(** Type printing *)

type typ_level =
| T5_l
| T5_r
| T2
| T1
| T0

let t_unit =
  KerName.make Tac2env.rocq_prefix (Label.of_id (Id.of_string "unit"))

let pr_typref kn =
  Libnames.pr_qualid (Tac2env.shortest_qualid_of_type kn)

let pr_glbtype_gen pr lvl c =
  let rec pr_glbtype lvl = function
  | GTypVar n -> str "'" ++ str (pr n)
  | GTypRef (Other kn, []) -> pr_typref kn
  | GTypRef (Other kn, [t]) ->
    let paren = match lvl with
    | T5_r | T5_l | T2 | T1 -> fun x -> x
    | T0 -> paren
    in
    paren (pr_glbtype T1 t ++ spc () ++ pr_typref kn)
  | GTypRef (Other kn, tl) ->
    let paren = match lvl with
    | T5_r | T5_l | T2 | T1 -> fun x -> x
    | T0 -> paren
    in
    paren (str "(" ++ prlist_with_sep pr_comma (pr_glbtype lvl) tl ++ str ")" ++ spc () ++ pr_typref kn)
  | GTypArrow (t1, t2) ->
    let paren = match lvl with
    | T5_r -> fun x -> x
    | T5_l | T2 | T1 | T0 -> paren
    in
    paren (pr_glbtype T5_l t1 ++ spc () ++ str "->" ++ spc () ++ pr_glbtype T5_r t2)
  | GTypRef (Tuple 0, []) ->
    Libnames.pr_qualid (Tac2env.shortest_qualid_of_type t_unit)
  | GTypRef (Tuple _, tl) ->
    let paren = match lvl with
    | T5_r | T5_l -> fun x -> x
    | T2 | T1 | T0 -> paren
    in
    paren (prlist_with_sep (fun () -> str " * ") (pr_glbtype T2) tl)
  in
  hov 0 (pr_glbtype lvl c)

let pr_glbtype pr c = pr_glbtype_gen pr T5_r c

let int_name () =
  let vars = ref Int.Map.empty in
  fun n ->
    if Int.Map.mem n !vars then Int.Map.find n !vars
    else
      let num = Int.Map.cardinal !vars in
      let base = num mod 26 in
      let rem = num / 26 in
      let name = String.make 1 (Char.chr (97 + base)) in
      let suff = if Int.equal rem 0 then "" else string_of_int rem in
      let name = name ^ suff in
      let () = vars := Int.Map.add n name !vars in
      name

(** Term printing *)

let pr_constructor kn =
  Libnames.pr_qualid (Tac2env.shortest_qualid_of_constructor kn)

let pr_projection kn =
  Libnames.pr_qualid (Tac2env.shortest_qualid_of_projection kn)

type exp_level = Tac2expr.exp_level =
| E5
| E4
| E3
| E2
| E1
| E0

let pr_atom = function
| AtmInt n -> Pp.int n
| AtmStr s -> qstring s

let pr_name = function
| Name id -> Id.print id
| Anonymous -> str "_"

let find_constructor n empty def =
  let rec find n = function
  | [] -> assert false
  | (_, id, []) as ans :: rem ->
    if empty then
      if Int.equal n 0 then ans
      else find (pred n) rem
    else find n rem
  | (_, id, _ :: _) as ans :: rem ->
    if not empty then
      if Int.equal n 0 then ans
      else find (pred n) rem
    else find n rem
  in
  find n def

let pr_internal_constructor tpe n is_const =
  let data = match Tac2env.interp_type tpe with
  | (_, GTydAlg data) -> data
  | _ -> assert false
  in
  let (_, id, _) = find_constructor n is_const data.galg_constructors in
  let kn = change_kn_label tpe id in
  pr_constructor kn

let order_branches cbr nbr def =
  let rec order cidx nidx def = match def with
  | [] -> []
  | (_, id, []) :: rem ->
    let ans = order (succ cidx) nidx rem in
    (id, [], cbr.(cidx)) :: ans
  | (_, id, _ :: _) :: rem ->
    let ans = order cidx (succ nidx) rem in
    let (vars, e) = nbr.(nidx) in
    (id, Array.to_list vars, e) :: ans
  in
  order 0 0 def

type ('a,'b) factorization =
  | FullList of 'a list
  | ListPrefix of 'a list * 'a
  | Other of 'b

let pr_factorized_constructor pr_rec lvl tpe = function
  | FullList l ->
      let pr e = pr_rec E4 e in
      hov 2 (str "[" ++ prlist_with_sep pr_semicolon pr (List.rev l) ++ str "]")
  | ListPrefix (l,e) ->
      let paren = match lvl with
        | E0 | E1 | E2 -> paren
        | E3 | E4 | E5 -> fun x -> x
      in
      let pr e = pr_rec E1 e in
      let pr_cons () = spc () ++ str "::" ++ spc () in
      paren (hov 2 (prlist_with_sep pr_cons pr (List.rev (e :: l))))
  | Other (n,cl) ->
  let _, data = Tac2env.interp_type tpe in
  match data with
  | GTydDef None -> str "<abstr>"
  | GTydAlg def ->
    let paren = match lvl with
      | E0 ->
        if List.is_empty cl then fun x -> x else paren
      | E1 | E2 | E3 | E4 | E5 -> fun x -> x
    in
    let cstr = pr_internal_constructor tpe n (List.is_empty cl) in
    let cl = match cl with
      | [] -> mt ()
      | _ -> spc () ++ pr_sequence (pr_rec E0) cl
    in
    paren (hov 2 (cstr ++ cl))
  | GTydRec def ->
    let args = List.combine def cl in
    let pr_arg ((id, _, _), arg) =
      let kn = change_kn_label tpe id in
      pr_projection kn ++ spc () ++ str ":=" ++ spc () ++ pr_rec E1 arg
    in
    let args = prlist_with_sep pr_semicolon pr_arg args in
    hv 0 (str "{" ++ spc () ++ args ++ spc () ++ str "}")
  | (GTydDef _ | GTydOpn) -> assert false

let pr_partial_pat_gen =
  let open PartialPat in
  let rec pr_pat lvl pat = match pat.CAst.v with
    | Var x -> pr_name x
    | Atom a -> pr_atom a
    | As (p, x) ->
      let paren = match lvl with
        | E0 -> paren
        | E1 | E2 | E3 | E4 | E5 -> fun x -> x
      in
      paren (hv 0 (pr_pat E1 p ++ spc() ++ str "as" ++ spc () ++ Id.print x))
    | Ref ({ctyp=None; cnargs=0}, _) -> str "()"
    | Ref ({ctyp=None}, args) ->
      let paren = match lvl with
        | E0 | E1 -> paren
        | E2 | E3 | E4 | E5 -> fun x -> x
      in
      paren (prlist_with_sep pr_comma (pr_pat E1) args)
    | Ref ({cindx=Open kn}, args) ->
      let paren = match lvl with
        | E0 -> paren
        | E1 | E2 | E3 | E4 | E5 -> fun x -> x
      in
      let c = pr_constructor kn in
      paren (hov 0 (c ++ spc () ++ (pr_sequence (pr_pat E0) args)))
    | Ref ({ctyp=Some ctyp; cindx=Closed i}, args) ->
      (* TODO when we have patterns for records this will need an update *)
      let factorized =
        if KerName.equal ctyp t_list then
          let rec factorize accu pat = match pat.CAst.v with
            | Ref (_, []) -> accu, None
            | Ref (_, [e; l]) -> factorize (e :: accu) l
            | _ -> accu, Some pat
          in
          let l, e = factorize [] pat in
          match e with
          | None -> FullList l
          | Some e -> ListPrefix (l,e)
        else Other (i,args)
      in
      pr_factorized_constructor pr_pat lvl ctyp factorized
    | Extension {example=None} -> str "*extension*"
    | Extension {example=Some a} -> pr_atom a
    | Or pats ->
      let paren = match lvl with
        | E0 -> paren
        | E1 | E2 | E3 | E4 | E5 -> fun x -> x
      in
      paren (hv 0 (prlist_with_sep (fun () -> spc() ++ str "|" ++ spc()) (pr_pat E1) pats))
  in
  fun lvl pat -> hov 0 (pr_pat lvl pat)

let pr_partial_pat pat = pr_partial_pat_gen E5 pat

(* Lets us share the pattern printing code *)
let rec partial_pat_of_glb_pat pat =
  let open PartialPat in
  let pat = match pat with
    | GPatVar x -> Var x
    | GPatAtm x -> Atom x
    | GPatRef (ctor,pats) -> Ref (ctor, List.map partial_pat_of_glb_pat pats)
    | GPatOr pats -> Or (List.map partial_pat_of_glb_pat pats)
    | GPatAs (p,x) -> As (partial_pat_of_glb_pat p, x)
  in
  CAst.make pat

let pr_glb_pat pat = pr_partial_pat (partial_pat_of_glb_pat pat)

let rec avoid_glb_pat avoid = function
  | GPatVar x -> Termops.add_vname avoid x
  | GPatAtm _ -> avoid
  | GPatRef (_, pats) -> List.fold_left avoid_glb_pat avoid pats
  | GPatOr [] -> assert false
  | GPatOr (p::_) -> avoid_glb_pat avoid p
  | GPatAs (p,x) -> avoid_glb_pat (Id.Set.add x avoid) p

let pr_glbexpr_gen lvl ~avoid c =
  let rec pr_glbexpr lvl avoid = function
  | GTacAtm atm -> pr_atom atm
  | GTacVar id -> Id.print id
  | GTacRef gr -> pr_tacref avoid gr
  | GTacFun (nas, c) ->
    let avoid = List.fold_left Termops.add_vname avoid nas in
    let nas = pr_sequence pr_name nas in
    let paren = match lvl with
    | E0 | E1 | E2 | E3 | E4 -> paren
    | E5 -> fun x -> x
    in
    paren (hov 0 (hov 2 (str "fun" ++ spc () ++ nas) ++ spc () ++ str "=>" ++ spc () ++
      pr_glbexpr E5 avoid c))
  | GTacApp (c, cl) ->
    let paren = match lvl with
    | E0 -> paren
    | E1 | E2 | E3 | E4 | E5 -> fun x -> x
    in
    paren (hov 2 (pr_glbexpr E1 avoid c ++ spc () ++ (pr_sequence (pr_glbexpr E0 avoid) cl)))
  | GTacLet (isrec, bnd, e) ->
    let paren = match lvl with
    | E0 | E1 | E2 | E3 | E4 -> paren
    | E5 -> fun x -> x
    in
    let pprec = if isrec then str "rec" ++ spc () else mt () in
    let avoidbnd = List.fold_left (fun avoid (na,_) -> Termops.add_vname avoid na) avoid bnd in
    let pr_bnd (na, e) =
      let avoid = if isrec then avoidbnd else avoid in
      pr_name na ++ spc () ++ str ":=" ++ spc () ++ hov 2 (pr_glbexpr E5 avoid e) ++ spc ()
    in
    let bnd = prlist_with_sep (fun () -> str "with" ++ spc ()) pr_bnd bnd in
    paren (hv 0 (hov 2 (str "let" ++ spc () ++ pprec ++ bnd ++ str "in") ++ spc () ++ pr_glbexpr E5 avoidbnd e))
  | GTacCst (Tuple 0, _, _) -> str "()"
  | GTacCst (Tuple _, _, cl) ->
    let paren = match lvl with
    | E0 | E1 -> paren
    | E2 | E3 | E4 | E5 -> fun x -> x
    in
    paren (prlist_with_sep (fun () -> str "," ++ spc ()) (pr_glbexpr E1 avoid) cl)
  | GTacCst (Other tpe, n, cl) ->
    pr_applied_constructor lvl avoid tpe n cl
  | GTacCse (e, info, cst_br, ncst_br) ->
    let e = pr_glbexpr E5 avoid e in
    let br = match info with
    | Other kn ->
      begin match Tac2env.interp_type kn with
      | _, GTydDef None -> str "<abstr>"
      | _, GTydDef _ | _, GTydRec _ | _, GTydOpn -> assert false
      | _, GTydAlg { galg_constructors = def } ->
        let br = order_branches cst_br ncst_br def in
        let pr_branch (cstr, vars, p) =
          let cstr = change_kn_label kn cstr in
          let cstr = pr_constructor cstr in
          let avoid = List.fold_left Termops.add_vname avoid vars in
          let vars = match vars with
            | [] -> mt ()
            | _ -> spc () ++ pr_sequence pr_name vars
          in
          hov 4 (str "|" ++ spc () ++ hov 0 (cstr ++ vars ++ spc () ++ str "=>") ++ spc () ++
                 hov 2 (pr_glbexpr E5 avoid p))
        in
        prlist_with_sep spc pr_branch br
      end
    | Tuple n ->
      let (vars, p) = if Int.equal n 0 then ([||], cst_br.(0)) else ncst_br.(0) in
      let avoid = Array.fold_left Termops.add_vname avoid vars in
      let p = pr_glbexpr E5 avoid p in
      let vars = prvect_with_sep (fun () -> str "," ++ spc ()) pr_name vars in
      hov 4 (str "|" ++ spc () ++ hov 0 (paren vars ++ spc () ++ str "=>") ++ spc () ++ p)
    in
    v 0 (hv 0 (str "match" ++ spc () ++ e ++ spc () ++ str "with") ++ spc () ++ br ++ spc () ++ str "end")
  | GTacWth wth ->
    let e = pr_glbexpr E5 avoid wth.opn_match in
    let pr_pattern c self vars avoid p =
      let avoid = Termops.add_vname avoid self in
      let self = match self with
      | Anonymous -> mt ()
      | Name id -> spc () ++ str "as" ++ spc () ++ Id.print id
      in
      hov 4 (str "|" ++ spc () ++ hov 0 (c ++ vars ++ self ++ spc () ++ str "=>") ++ spc () ++
        hov 2 (pr_glbexpr E5 avoid p)) ++ spc ()
    in
    let pr_branch (cstr, (self, vars, p)) =
      let cstr = pr_constructor cstr in
      let avoid = Array.fold_left Termops.add_vname avoid vars in
      let vars = match Array.to_list vars with
      | [] -> mt ()
      | vars -> spc () ++ pr_sequence pr_name vars
      in
      pr_pattern cstr self vars avoid p
    in
    let br = prlist pr_branch (KNmap.bindings wth.opn_branch) in
    let (def_as, def_p) = wth.opn_default in
    let def = pr_pattern (str "_") def_as (mt ()) avoid def_p in
    let br = br ++ def in
    v 0 (hv 0 (str "match" ++ spc () ++ e ++ spc () ++ str "with") ++ spc () ++ br ++ str "end")
  | GTacFullMatch (e, brs) ->
    let e = pr_glbexpr E5 avoid e in
    let pr_one_branch (pat,br) =
      let avoid = avoid_glb_pat avoid pat in
      hov 4 (str "|" ++ spc() ++ hov 0 (pr_glb_pat pat ++ spc() ++ str "=>") ++ spc() ++
             hov 2 (pr_glbexpr E5 avoid br))
    in
    let brs = prlist_with_sep spc pr_one_branch brs in
    v 0 (hv 0 (str "match" ++ spc () ++ e ++ spc () ++ str "with") ++ spc () ++ brs ++ spc() ++ str "end")
  | GTacPrj (kn, e, n) ->
    begin  match Tac2env.interp_type kn with
    | _, GTydDef None -> str "<abstr>"
    | _, GTydDef _ | _, GTydAlg _ | _, GTydOpn -> assert false
    | _, GTydRec def ->
      let (proj, _, _) = List.nth def n in
      let proj = change_kn_label kn proj in
      let proj = pr_projection proj in
      let e = pr_glbexpr E0 avoid e in
      hov 0 (e ++ str "." ++ paren proj)
    end
  | GTacSet (kn, e, n, r) ->
    begin match Tac2env.interp_type kn with
    | _, GTydDef None -> str "<abstr>"
    | _, GTydDef _ | _, GTydAlg _ | _, GTydOpn -> assert false
    | _, GTydRec def ->
      let (proj, _, _) = List.nth def n in
      let proj = change_kn_label kn proj in
      let proj = pr_projection proj in
      let e = pr_glbexpr E0 avoid e in
      let r = pr_glbexpr E1 avoid r in
      hov 0 (e ++ str "." ++ paren proj ++ spc () ++ str ":=" ++ spc () ++ r)
    end
  | GTacOpn (kn, []) -> pr_constructor kn
  | GTacOpn (kn, cl) ->
    let paren = match lvl with
    | E0 -> paren
    | E1 | E2 | E3 | E4 | E5 -> fun x -> x
    in
    let c = pr_constructor kn in
    paren (hov 0 (c ++ spc () ++ (pr_sequence (pr_glbexpr E0 avoid) cl)))
  | GTacExt (tag, arg) ->
    let tpe = interp_ml_object tag in
    let env = Global.env() in
    let sigma = Evd.from_env env in
    hov 0 (tpe.ml_print env sigma arg)
  | GTacPrm prm ->
    hov 0 (str "@external" ++ spc () ++ qstring prm.mltac_plugin ++ spc () ++
      qstring prm.mltac_tactic)
  and pr_applied_constructor lvl avoid tpe n cl =
    let factorized =
      if KerName.equal tpe t_list then
        let rec factorize accu = function
          | GTacCst (_, 0, []) -> accu, None
          | GTacCst (_, 0, [e; l]) -> factorize (e :: accu) l
          | e -> accu, Some e
        in
        let l, e = factorize [] (GTacCst (Other tpe, n, cl)) in
        match e with
        | None -> FullList l
        | Some e -> ListPrefix (l,e)
      else Other (n,cl)
    in
    pr_factorized_constructor (fun lvl -> pr_glbexpr lvl avoid) lvl tpe factorized
  in
  hov 0 (pr_glbexpr lvl avoid c)

let pr_glbexpr ~avoid c =
  pr_glbexpr_gen E5 ~avoid c


(** Raw datas *)

let pr_relid pr = function
  | AbsKn x -> pr x
  | RelId qid -> Libnames.pr_qualid qid

let swap_tuple_relid : _ or_tuple or_relid -> _ or_relid or_tuple = function
  | RelId _ as x -> Other x
  | AbsKn (Tuple _ as x) -> x
  | AbsKn (Other x) -> Other (AbsKn x)

let rec pr_rawtype_gen lvl t = match t.CAst.v with
| CTypVar x -> pr_name x
| CTypArrow (t1, t2) ->
  let paren = match lvl with
    | T5_r -> fun x -> x
    | T5_l | T2 | T1 | T0 -> paren
  in
  paren (pr_rawtype_gen T5_l t1 ++ spc () ++ str "->" ++ spc () ++ pr_rawtype_gen T5_r t2)
| CTypRef (kn, args) -> match swap_tuple_relid kn with
  | Tuple n ->
    let () = if not (Int.equal n (List.length args))
      then CErrors.anomaly ?loc:t.loc Pp.(str "Incorrect tuple.")
    in
    if Int.equal n 0 then Libnames.pr_qualid (Tac2env.shortest_qualid_of_type t_unit)
    else
      let paren = match lvl with
        | T5_r | T5_l -> fun x -> x
        | T2 | T1 | T0 -> paren
      in
      paren (prlist_with_sep (fun () -> str " * ") (pr_rawtype_gen T2) args)
  | Other kn ->
    let ppkn = pr_relid pr_typref kn in
    match args with
    | [] -> ppkn
    | [arg] ->
      let paren = match lvl with
        | T5_r | T5_l | T2 | T1 -> fun x -> x
        | T0 -> paren
      in
      paren (pr_rawtype_gen T1 arg ++ spc () ++ ppkn)
    | _ ->
      let paren = match lvl with
        | T5_r | T5_l | T2 | T1 -> fun x -> x
        | T0 -> paren
      in
      paren (surround (prlist_with_sep pr_comma (pr_rawtype_gen lvl) args)
             ++ spc () ++ ppkn)


let rec ids_of_pattern accu {CAst.v=pat} = match pat with
| CPatVar Anonymous | CPatAtm _ -> accu
| CPatVar (Name id) -> Id.Set.add id accu
| CPatAs (p,id) -> ids_of_pattern (Id.Set.add id.v accu) p
| CPatRef (_, pl) | CPatOr pl ->
  List.fold_left ids_of_pattern accu pl
| CPatCnv (pat, _) -> ids_of_pattern accu pat
| CPatRecord pats -> List.fold_left (fun accu (_,pat) -> ids_of_pattern accu pat) accu pats

let rec pr_rawpat_gen lvl p = match p.CAst.v with
| CPatVar x -> pr_name x
| CPatAtm a -> pr_atom a
| CPatRef (AbsKn (Tuple n), pats) ->
  let () = if not (Int.equal n (List.length pats))
    then CErrors.anomaly ?loc:p.loc Pp.(str "Incorrect tuple.")
  in
  str "(" ++ prlist_with_sep pr_comma (pr_rawpat_gen E1) pats ++ str ")"
| CPatRef (RelId r,pats) ->
  let paren = match lvl with
    | E0 -> paren
    | E1 | E2 | E3 | E4 | E5 -> fun x -> x
  in
  paren (hov 0 (Libnames.pr_qualid r ++ spc() ++ pr_sequence (pr_rawpat_gen E0) pats))
| CPatRef (AbsKn (Other kn), pats) ->
  let rec factorize accu pat = match pat.CAst.v with
    | CPatRef (AbsKn (Other kn), pats) when KerName.equal kn c_nil ->
      let () = if not (CList.is_empty pats)
        then CErrors.anomaly ?loc:p.loc (str "Incorrect list pattern.")
      in
      accu, None
    | CPatRef (AbsKn (Other kn), pats) when KerName.equal kn c_cons ->
      let hd, tl = match pats with
        | [hd;tl] -> hd, tl
        | _ -> CErrors.anomaly ?loc:p.loc (str "Incorrect list pattern.")
      in
      factorize (hd::accu) tl
    | _ -> accu, Some pat
  in
  begin match factorize [] p with
  | pats, None ->
    hov 2 (str "[" ++ prlist_with_sep pr_semicolon (pr_rawpat_gen E4) (List.rev pats) ++ str "]")
  | (_ :: _) as pats, Some rest ->
    let paren = match lvl with
      | E0 | E1 | E2 -> paren
      | E3 | E4 | E5 -> fun x -> x
    in
    let pr_cons () = spc () ++ str "::" ++ spc () in
    paren (hov 2 (prlist_with_sep pr_cons (pr_rawpat_gen E1) (List.rev (rest :: pats))))
  | [], Some p' ->
    assert (p == p');
    if CList.is_empty pats then pr_constructor kn
    else
      let paren = match lvl with
        | E0 -> paren
        | E1 | E2 | E3 | E4 | E5 -> fun x -> x
      in
      paren (hov 0 (pr_constructor kn ++ spc() ++ pr_sequence (pr_rawpat_gen E0) pats))
  end
| CPatRecord pats ->
  let pr_field (proj, p) =
    pr_relid pr_projection proj ++ spc() ++ str ":=" ++ spc() ++ pr_rawpat_gen E1 p
  in
  hov 0 (str "{" ++ spc() ++ prlist_with_sep pr_semicolon pr_field pats ++ spc() ++ str "}")
| CPatCnv (pat,t) ->
  let paren = match lvl with
    | E0 -> paren
    | E1 | E2 | E3 | E4 | E5 -> fun x -> x
  in
  paren (pr_rawpat_gen E5 pat ++ spc() ++ str ":" ++ spc() ++ pr_rawtype_gen T5_l t)
| CPatOr pats ->
  let paren = match lvl with
    | E0 -> paren
    | E1 | E2 | E3 | E4 | E5 -> fun x -> x
  in
  paren (hv 0 (prlist_with_sep (fun () -> spc() ++ str "|" ++ spc()) (pr_rawpat_gen E1) pats))
| CPatAs (p,x) ->
  let paren = match lvl with
    | E0 -> paren
    | E1 | E2 | E3 | E4 | E5 -> fun x -> x
  in
  paren (hv 0 (pr_rawpat_gen E1 p ++ spc() ++ str "as" ++ spc () ++ Id.print x.v))

(* XXX in principle we could have collisions with user names *)
let base_internal_ty_ident = Id.of_string "__α"

let pr_rawexpr_gen lvl ~avoid c =
  let rec pr_rawexpr lvl avoid c =
  let loc = c.CAst.loc in
  match c.CAst.v with
  | CTacAtm a -> pr_atom a
  | CTacRef (RelId qid) -> Libnames.pr_qualid qid
  | CTacRef (AbsKn (TacConstant r)) -> pr_tacref avoid r
  | CTacRef (AbsKn (TacAlias _ as r)) -> Libnames.pr_qualid (Tac2env.shortest_qualid_of_ltac avoid r)
  | CTacCst (RelId qid) -> Libnames.pr_qualid qid
  | CTacCst (AbsKn (Tuple 0)) -> str "()"
  | CTacCst (AbsKn (Tuple n)) -> CErrors.anomaly ?loc Pp.(str "Incorrect tuple.")
  | CTacCst (AbsKn (Other kn)) when KerName.equal c_nil kn -> str "[]"
  | CTacCst (AbsKn (Other kn)) -> pr_constructor kn
  | CTacFun (pats, c) ->
    let avoid = List.fold_left ids_of_pattern avoid pats in
    let pats = pr_sequence (pr_rawpat_gen E0) pats in
    let paren = match lvl with
    | E0 | E1 | E2 | E3 | E4 -> paren
    | E5 -> fun x -> x
    in
    paren (hov 0 (hov 2 (str "fun" ++ spc() ++ pats) ++ spc() ++ str "=>" ++ spc() ++
      pr_rawexpr E5 avoid c))
  | CTacApp ({v=CTacCst (AbsKn (Tuple 0))}, args) ->
    let paren = match lvl with
      | E0 -> paren
      | E1 | E2 | E3 | E4 | E5 -> fun x -> x
    in
    paren (hov 0 (str "()" ++ spc() ++ pr_sequence (pr_rawexpr E0 avoid) args))
  | CTacApp ({v=CTacCst (AbsKn (Tuple n))}, args) ->
    let () = if not (Int.equal n (List.length args))
      then CErrors.anomaly ?loc Pp.(str "Incorrect tuple.")
    in
    surround (prlist_with_sep pr_comma (pr_rawexpr E1 avoid) args)
  | CTacApp ({v=CTacCst (AbsKn (Other kn))}, _) when KerName.equal kn c_cons ->
    let rec factorize accu c = match c.CAst.v with
      | CTacCst (AbsKn (Other kn)) when KerName.equal c_nil kn -> accu, None
      | CTacApp ({v=CTacCst (AbsKn (Other kn))}, args) when KerName.equal kn c_cons ->
        let hd, tl = match args with
          | [hd;tl] -> hd, tl
          | _ -> CErrors.anomaly ?loc (str "Incorrect list.")
        in
        factorize (hd::accu) tl
      | _ -> accu, Some c
    in
    begin match factorize [] c with
    | l, None ->
      hov 2 (str "[" ++ prlist_with_sep pr_semicolon (pr_rawexpr E4 avoid) (List.rev l) ++ str "]")
    | l, Some rest ->
      let paren = match lvl with
        | E0 | E1 | E2 -> paren
        | E3 | E4 | E5 -> fun x -> x
      in
      let pr_cons () = spc () ++ str "::" ++ spc () in
      paren (hov 2 (prlist_with_sep pr_cons (pr_rawexpr E1 avoid) (List.rev (rest :: l))))
    end
  | CTacApp (hd,args) ->
    let paren = match lvl with
      | E0 -> paren
      | E1 | E2 | E3 | E4 | E5 -> fun x -> x
    in
    paren (hov 0 (pr_rawexpr E0 avoid hd ++ spc() ++ pr_sequence (pr_rawexpr E0 avoid) args))
  | CTacSyn _ -> CErrors.anomaly ?loc Pp.(str "Unresolved notation.")
  | CTacLet (isrec, bnd, e) ->
    let paren = match lvl with
      | E0 | E1 | E2 | E3 | E4 -> paren
      | E5 -> fun x -> x
    in
    let pprec = if isrec then str "rec" ++ spc () else mt () in
    let avoidbnd = List.fold_left (fun avoid (pat,_) -> ids_of_pattern avoid pat) avoid bnd in
    let pr_bnd (pat, e) =
      let avoid = if isrec then avoidbnd else avoid in
      pr_rawpat_gen E0 pat ++ spc () ++ str ":=" ++ spc () ++ hov 2 (pr_rawexpr E5 avoid e) ++ spc ()
    in
    let bnd = prlist_with_sep (fun () -> str "with" ++ spc ()) pr_bnd bnd in
    paren (hv 0 (hov 2 (str "let" ++ spc () ++ pprec ++ bnd ++ str "in") ++ spc () ++ pr_rawexpr E5 avoidbnd e))
  | CTacCnv (e,t) ->
    let paren = match lvl with
      | E0 -> paren
      | E1 | E2 | E3 | E4 | E5 -> fun x -> x
    in
    paren (pr_rawexpr E5 avoid e ++ spc() ++ str ":" ++ spc() ++ pr_rawtype_gen T5_l t)
  | CTacSeq (e1,e2) ->
    let paren = match lvl with
    | E0 | E1 | E2 | E3 | E4 -> paren
    | E5 -> fun x -> x
    in
    paren (pr_rawexpr E4 avoid e1 ++ str ";" ++ spc() ++ pr_rawexpr E4 avoid e2)
  | CTacIft (b,e1,e2) ->
    let paren = match lvl with
    | E0 | E1 | E2 | E3 | E4 -> paren
    | E5 -> fun x -> x
    in
    paren (str "if" ++ spc() ++ pr_rawexpr E5 avoid b ++ spc()
           ++ str "then" ++ spc() ++ pr_rawexpr E5 avoid e1 ++ spc()
           ++ str "else" ++ spc() ++ pr_rawexpr E5 avoid e2)
  | CTacCse (e,brs) ->
    let pr_one_branch (pat,br) =
      let avoid = ids_of_pattern avoid pat in
      hov 4 (str "|" ++ spc() ++ hov 0 (pr_rawpat_gen E5 pat ++ spc() ++ str "=>") ++ spc() ++
             hov 2 (pr_rawexpr E5 avoid br))
    in
    let brs = prlist_with_sep spc pr_one_branch brs in
    v 0 (hv 0 (str "match" ++ spc() ++ pr_rawexpr E5 avoid e ++ spc() ++ str "with")
         ++ spc() ++ brs ++ spc() ++ str "end")
  | CTacRec (def,fields) ->
    let def = match def with
      | None -> mt()
      | Some def -> pr_rawexpr E0 avoid def ++ spc() ++ str "with" ++ spc()
    in
    let pr_field (proj,e) =
      pr_relid pr_projection proj ++ spc() ++ str ":=" ++ spc() ++ pr_rawexpr E1 avoid e
    in
    hov 2 (str "{" ++ spc() ++ def ++ prlist_with_sep pr_semicolon pr_field fields ++ str "}")
  | CTacPrj (e,p) ->
    hov 0 (pr_rawexpr E0 avoid e ++ str "." ++ paren (pr_relid pr_projection p))
  | CTacSet (e1,p,e2) ->
    hov 0 (pr_rawexpr E0 avoid e1 ++ str "." ++ paren (pr_relid pr_projection p)
           ++ spc() ++ str ":=" ++ spc() ++ pr_rawexpr E1 avoid e2)
  | CTacExt (tag,arg) ->
    let obj = interp_ml_object tag in
    let env = Global.env() in
    let sigma = Evd.from_env env in
    obj.ml_raw_print env sigma arg
  | CTacGlb (prms, args, body, ty) ->
    let avoid, tynames =
      Array.fold_left_map (fun avoid () ->
          let na = Namegen.next_ident_away base_internal_ty_ident avoid in
          let avoid = Id.Set.add na avoid in
          avoid, Id.to_string na)
        avoid
        (Array.make prms ())
    in
    let tynames i = tynames.(i) in
    let pr_arg (pat, arg, ty) =
      let bnd = match ty with
        | Some ty ->
          paren (pr_name pat.CAst.v ++ spc() ++ str ":" ++ spc() ++ pr_glbtype_gen tynames T5_l ty)
        | None -> pr_name pat.CAst.v
      in
      bnd ++ spc() ++ str ":=" ++ spc() ++ hov 2 (pr_rawexpr E5 avoid arg) ++ spc()
    in
    let paren = match lvl with
      | E0 | E1 | E2 | E3 | E4 -> paren
      | E5 -> fun x -> x
    in
    let bnd = prlist_with_sep (fun () -> str "with" ++ spc ()) pr_arg args in
    paren (hv 0 (hov 2 (str "let" ++ spc() ++ bnd ++ str "in") ++ spc()
                 ++ pr_glbexpr_gen ~avoid E5 body ++ spc()
                 ++ str ":" ++ pr_glbtype_gen tynames T5_l ty))
  in
  hov 0 (pr_rawexpr lvl avoid c)

(** Toplevel printers *)

let rec subst_type subst (t : 'a glb_typexpr) = match t with
| GTypVar id -> subst.(id)
| GTypArrow (t1, t2) -> GTypArrow (subst_type subst t1, subst_type subst t2)
| GTypRef (qid, args) ->
  GTypRef (qid, List.map (fun t -> subst_type subst t) args)

let unfold kn args =
  let (nparams, def) = Tac2env.interp_type kn in
  match def with
  | GTydDef (Some def) ->
    let args = Array.of_list args in
    Some (subst_type args def)
  | _ -> None

let rec kind t = match t with
| GTypVar id -> GTypVar id
| GTypRef (Other kn, tl) ->
  begin match unfold kn tl with
  | None -> t
  | Some t -> kind t
  end
| GTypArrow _ | GTypRef (Tuple _, _) -> t

type val_printer =
  { val_printer : 'a. Environ.env -> Evd.evar_map -> Tac2val.valexpr -> 'a glb_typexpr list -> Pp.t }

let printers = ref KNmap.empty

let register_val_printer kn pr =
  printers := KNmap.add kn pr !printers

open Tac2ffi

let rec pr_valexpr_gen env sigma lvl v t = match kind t with
| GTypVar _ -> str "<poly>"
| GTypRef (Other kn, params) ->
  let pr = try Some (KNmap.find kn !printers) with Not_found -> None in
  begin match pr with
  | Some pr ->
    (* for now assume all printers produce atomic expressions so no need to pass [lvl] *)
    pr.val_printer env sigma v params
  | None ->
    let n, repr = Tac2env.interp_type kn in
    if KerName.equal kn t_list then
      pr_val_list env sigma (to_list (fun v -> repr_to valexpr v) v) (List.hd params)
    else match repr with
    | GTydDef None -> str "<abstr>"
    | GTydDef (Some _) ->
      (* Shouldn't happen thanks to kind *)
      assert false
    | GTydAlg alg ->
      if Tac2val.Valexpr.is_int v then
        pr_internal_constructor kn (Tac2ffi.to_int v) true
      else
        let paren = match lvl with
          | E0 -> paren
          | E1 | E2 | E3 | E4 | E5 -> fun x -> x
        in
        let (n, args) = Tac2ffi.to_block v in
        let (_, id, tpe) = find_constructor n false alg.galg_constructors in
        let knc = change_kn_label kn id in
        let args = pr_constrargs env sigma params args tpe in
        paren (pr_constructor knc ++ spc () ++ args)
    | GTydRec rcd ->
      let (_, args) = Tac2ffi.to_block v in
      pr_record env sigma params args rcd
    | GTydOpn ->
      begin match Tac2ffi.to_open v with
      | (knc, [||]) -> pr_constructor knc
      | (knc, args) ->
        let paren = match lvl with
          | E0 -> paren
          | E1 | E2 | E3 | E4 | E5 -> fun x -> x
        in
        let data = Tac2env.interp_constructor knc in
        let args = pr_constrargs env sigma params args data.Tac2env.cdata_args in
        paren (pr_constructor knc ++ spc () ++ args)
      end
  end
| GTypArrow _ -> str "<fun>"
| GTypRef (Tuple 0, []) -> str "()"
| GTypRef (Tuple _, tl) ->
  let blk = Array.to_list (snd (to_block v)) in
  if List.length blk == List.length tl then
    let prs = List.map2 (fun v t -> pr_valexpr_gen env sigma E1 v t) blk tl in
    hv 2 (str "(" ++ prlist_with_sep pr_comma (fun p -> p) prs ++ str ")")
  else
    str "<unknown>"

and pr_constrargs env sigma params args tpe =
  let subst = Array.of_list params in
  let tpe = List.map (fun t -> subst_type subst t) tpe in
  let args = Array.to_list args in
  let args = List.combine args tpe in
  pr_sequence (fun (v, t) -> pr_valexpr_gen env sigma E0 v t) args

and pr_record env sigma params args rcd =
  let subst = Array.of_list params in
  let map (id, _, tpe) = (id, subst_type subst tpe) in
  let rcd = List.map map rcd in
  let args = Array.to_list args in
  let fields = List.combine rcd args in
  let pr_field ((id, t), arg) =
    Id.print id ++ spc () ++ str ":=" ++ spc () ++ pr_valexpr_gen env sigma E1 arg t
  in
  str "{" ++ spc () ++ prlist_with_sep pr_semicolon pr_field fields ++ spc () ++ str "}"

and pr_val_list env sigma args tpe =
  let pr v = pr_valexpr_gen env sigma E4 v tpe in
  hov 1 (str "[" ++ prlist_with_sep pr_semicolon pr args ++ str "]")

let pr_valexpr env sigma v t = pr_valexpr_gen env sigma E5 v t

let register_init n f =
  let kn = KerName.make Tac2env.rocq_prefix (Label.make n) in
  register_val_printer kn { val_printer = fun env sigma v _ -> f env sigma v }

let () = register_init "int" begin fun _ _ n ->
  let n = to_int n in
  Pp.int n
end

let () = register_init "string" begin fun _ _ s ->
  let s = to_string s in
  Pp.quote (str s)
end

let () = register_init "ident" begin fun _ _ id ->
  let id = to_ident id in
  str "@" ++ Id.print id
end

let () = register_init "constr" begin fun env sigma c ->
  let c = to_constr c in
  let c = try Printer.pr_leconstr_env env sigma c with _ -> str "..." in
  hov 2 (str "constr:(" ++ c ++ str ")")
end

let () = register_init "preterm" begin fun env sigma c ->
  let c = to_preterm c in
  (* XXX should we get the ltac2 env out of the closure and print it too? Maybe with a debug flag? *)
  let c = try Printer.pr_closed_glob_env env sigma c with _ -> str "..." in
  hov 2 (str "preterm:(" ++ c ++ str ")")
end

let () = register_init "pattern" begin fun env sigma c ->
  let c = to_pattern c in
  let c = try Printer.pr_lconstr_pattern_env env sigma c with _ -> str "..." in
  hov 2 (str "pat:(" ++ c ++ str ")")
end

let () = register_init "message" begin fun _ _ pp ->
  hov 2 (str "message:(" ++ to_pp pp ++ str ")")
end

let () = register_init "err" begin fun _ _ e ->
  let e = to_err e in
  hov 2 (str "err:(" ++ CErrors.iprint_no_report e ++ str ")")
end

let () =
  let kn = KerName.make Tac2env.rocq_prefix (Label.make "array") in
  let val_printer env sigma v arg = match arg with
  | [arg] ->
    let (_, v) = to_block v in
    str "[|" ++ spc () ++
      prvect_with_sep pr_semicolon (fun a -> pr_valexpr env sigma a arg) v ++
      spc () ++ str "|]"
  | _ -> assert false
  in
  register_val_printer kn { val_printer }

(** {5 Ltac2 primitive} *)

type format =
| FmtString
| FmtInt
| FmtConstr
| FmtIdent
| FmtLiteral of string
| FmtAlpha

let val_format = Tac2dyn.Val.create "format"

exception InvalidFormat

let parse_format (s : string) : format list =
  let len = String.length s in
  let buf = Buffer.create len in
  let rec parse i accu =
    if len <= i then accu
    else match s.[i] with
    | '%' -> parse_argument (i + 1) accu
    | _ ->
      let i' = parse_literal i in
      if Int.equal i i' then parse i' accu
      else
        let lit = Buffer.contents buf in
        let () = Buffer.clear buf in
        parse i' (FmtLiteral lit :: accu)
  and parse_literal i =
    if len <= i then i
    else match s.[i] with
    | '%' -> i
    | c ->
      let () = Buffer.add_char buf c in
      parse_literal (i + 1)
  and parse_argument i accu =
    if len <= i then raise InvalidFormat
    else match s.[i] with
    | '%' -> parse (i + 1) (FmtLiteral "%" :: accu)
    | 's' -> parse (i + 1) (FmtString :: accu)
    | 'i' -> parse (i + 1) (FmtInt :: accu)
    | 'I' -> parse (i + 1) (FmtIdent :: accu)
    | 't' -> parse (i + 1) (FmtConstr :: accu)
    | 'a' -> parse (i + 1) (FmtAlpha :: accu)
    | _ -> raise InvalidFormat
  in
  parse 0 []


let pr_profile_frame = let open Pp in function
  | FrAnon e -> str "<fun " ++ pr_glbexpr ~avoid:Id.Set.empty e ++ str ">"
  | FrLtac kn -> pr_tacref Id.Set.empty kn
  | FrPrim ml -> str "<" ++ str ml.mltac_plugin ++ str ":" ++ str ml.mltac_tactic ++ str ">"
  | FrExtn (tag,_) -> str "<extn:" ++ str (Tac2dyn.Arg.repr tag) ++ str ">"

let () = Hook.set Tac2bt.pr_frame_hook pr_profile_frame
