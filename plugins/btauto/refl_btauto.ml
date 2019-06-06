(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Constr

let bt_lib_constr n = lazy (UnivGen.constr_of_monomorphic_global @@ Coqlib.lib_ref n)

let decomp_term sigma (c : Constr.t) =
  Constr.kind (EConstr.Unsafe.to_constr (Termops.strip_outer_cast sigma (EConstr.of_constr c)))

let lapp c v  = Constr.mkApp (Lazy.force c, v)

let (===) = Constr.equal


module CoqList = struct
  let _nil =  bt_lib_constr "core.list.nil"
  let _cons = bt_lib_constr "core.list.cons"

  let cons ty h t = lapp _cons [|ty; h ; t|]
  let nil ty = lapp _nil [|ty|]
  let rec of_list ty = function
    | [] -> nil ty
    | t::q -> cons ty t (of_list ty q)

end

module CoqPositive = struct
  let _xH = bt_lib_constr "num.pos.xH"
  let _xO = bt_lib_constr "num.pos.xO"
  let _xI = bt_lib_constr "num.pos.xI"

  (* A coq nat from an int *)
  let rec of_int n =
    if n <= 1 then Lazy.force _xH
    else
      let ans = of_int (n / 2) in
      if n mod 2 = 0 then lapp _xO [|ans|]
      else lapp _xI [|ans|]

end

module Env = struct

  module ConstrHashtbl = Hashtbl.Make (Constr)

  type t = (int ConstrHashtbl.t * int ref)

  let add (tbl, off) (t : Constr.t) =
    try ConstrHashtbl.find tbl t 
    with
    | Not_found -> 
      let i = !off in 
      let () = ConstrHashtbl.add tbl t i in
      let () = incr off in
      i

  let empty () = (ConstrHashtbl.create 16, ref 1)

  let to_list (env, _) =
    (* we need to get an ordered list *)
    let fold constr key accu = (key, constr) :: accu in
    let l = ConstrHashtbl.fold fold env [] in
    let sorted_l = List.sort (fun p1 p2 -> Int.compare (fst p1) (fst p2)) l in
    List.map snd sorted_l

end

module Bool = struct

  let ind    = lazy (Globnames.destIndRef (Coqlib.lib_ref "core.bool.type"))
  let typ    = bt_lib_constr "core.bool.type"
  let trueb  = bt_lib_constr "core.bool.true"
  let falseb = bt_lib_constr "core.bool.false"
  let andb   = bt_lib_constr "core.bool.andb"
  let orb    = bt_lib_constr "core.bool.orb"
  let xorb   = bt_lib_constr "core.bool.xorb"
  let negb   = bt_lib_constr "core.bool.negb"

  type t =
  | Var of int
  | Const of bool
  | Andb of t * t
  | Orb of t * t
  | Xorb of t * t
  | Negb of t
  | Ifb of t * t * t

  let quote (env : Env.t) sigma (c : Constr.t) : t =
    let trueb = Lazy.force trueb in
    let falseb = Lazy.force falseb in
    let andb = Lazy.force andb in
    let orb = Lazy.force orb in
    let xorb = Lazy.force xorb in
    let negb = Lazy.force negb in

    let rec aux c = match decomp_term sigma c with
    | App (head, args) ->
      if head === andb && Array.length args = 2 then
        Andb (aux args.(0), aux args.(1))
      else if head === orb && Array.length args = 2 then
        Orb (aux args.(0), aux args.(1))
      else if head === xorb && Array.length args = 2 then
        Xorb (aux args.(0), aux args.(1))
      else if head === negb && Array.length args = 1 then
        Negb (aux args.(0))
      else Var (Env.add env c)
    | Case (info, r, arg, pats) ->
      let is_bool =
        let i = info.ci_ind in
        Names.eq_ind i (Lazy.force ind)
      in
      if is_bool then
        Ifb ((aux arg), (aux pats.(0)), (aux pats.(1)))
      else
        Var (Env.add env c)
    | _ ->
      if c === falseb then Const false
      else if c === trueb then Const true
      else Var (Env.add env c)
    in
    aux c

end

module Btauto = struct

  open Pp

  let eq = bt_lib_constr "core.eq.type"

  let f_var = bt_lib_constr "plugins.btauto.f_var"
  let f_btm = bt_lib_constr "plugins.btauto.f_btm"
  let f_top = bt_lib_constr "plugins.btauto.f_top"
  let f_cnj = bt_lib_constr "plugins.btauto.f_cnj"
  let f_dsj = bt_lib_constr "plugins.btauto.f_dsj"
  let f_neg = bt_lib_constr "plugins.btauto.f_neg"
  let f_xor = bt_lib_constr "plugins.btauto.f_xor"
  let f_ifb = bt_lib_constr "plugins.btauto.f_ifb"

  let eval = bt_lib_constr "plugins.btauto.eval"
  let witness = bt_lib_constr "plugins.btauto.witness"
  let soundness = bt_lib_constr "plugins.btauto.soundness"

  let rec convert = function
  | Bool.Var n -> lapp f_var [|CoqPositive.of_int n|]
  | Bool.Const true -> Lazy.force f_top
  | Bool.Const false -> Lazy.force f_btm
  | Bool.Andb (b1, b2) -> lapp f_cnj [|convert b1; convert b2|]
  | Bool.Orb (b1, b2) -> lapp f_dsj [|convert b1; convert b2|]
  | Bool.Negb b -> lapp f_neg [|convert b|]
  | Bool.Xorb (b1, b2) -> lapp f_xor [|convert b1; convert b2|]
  | Bool.Ifb (b1, b2, b3) -> lapp f_ifb [|convert b1; convert b2; convert b3|]

  let convert_env env : Constr.t = 
    CoqList.of_list (Lazy.force Bool.typ) env

  let reify env t = lapp eval [|convert_env env; convert t|]

  let print_counterexample p penv gl =
    let var = lapp witness [|p|] in
    let var = EConstr.of_constr var in
    (* Compute an assignment that dissatisfies the goal *)
    let redfun, _ = Redexpr.reduction_of_red_expr (Refiner.pf_env gl) Genredexpr.(CbvVm None) in
    let _, var = redfun Refiner.(pf_env gl) Refiner.(project gl) var in
    let var = EConstr.Unsafe.to_constr var in
    let rec to_list l = match decomp_term (Tacmach.project gl) l with
    | App (c, _)
      when c === (Lazy.force CoqList._nil) -> []
    | App (c, [|_; h; t|])
      when c === (Lazy.force CoqList._cons) ->
      if h === (Lazy.force Bool.trueb) then (true :: to_list t)
      else if h === (Lazy.force Bool.falseb) then (false :: to_list t)
      else invalid_arg "to_list"
    | _ -> invalid_arg "to_list"
    in
    let concat sep = function
    | [] -> mt ()
    | h :: t ->
      let rec aux = function
      | [] -> mt ()
      | x :: t -> (sep ++ x ++ aux t)
      in
      h ++ aux t
    in
    let msg =
      try
        let var = to_list var in
        let assign = List.combine penv var in
        let map_msg (key, v) =
          let b = if v then str "true" else str "false" in
          let sigma, env = Tacmach.project gl, Tacmach.pf_env gl in
          let term = Printer.pr_constr_env env sigma key in
          term ++ spc () ++ str ":=" ++ spc () ++ b
        in
        let assign = List.map map_msg assign in
        let l = str "[" ++ (concat (str ";" ++ spc ()) assign) ++ str "]" in
        str "Not a tautology:" ++ spc () ++ l
      with e when CErrors.noncritical e -> (str "Not a tautology")
    in
    Tacticals.tclFAIL 0 msg gl

  let try_unification env =
    Proofview.Goal.enter begin fun gl ->
      let concl = Proofview.Goal.concl gl in
      let eq = Lazy.force eq in
      let concl = EConstr.Unsafe.to_constr concl in
      let t = decomp_term (Tacmach.New.project gl) concl in
      match t with
      | App (c, [|typ; p; _|]) when c === eq ->
      (* should be an equality [@eq poly ?p (Cst false)] *)
          let tac = Tacticals.New.tclORELSE0 Tactics.reflexivity (Proofview.V82.tactic (print_counterexample p env)) in
          tac
      | _ ->
          let msg = str "Btauto: Internal error" in
          Tacticals.New.tclFAIL 0 msg
    end

  let tac =
    Proofview.Goal.enter begin fun gl ->
      let concl = Proofview.Goal.concl gl in
      let concl = EConstr.Unsafe.to_constr concl in
      let sigma = Tacmach.New.project gl in
      let eq = Lazy.force eq in
      let bool = Lazy.force Bool.typ in
      let t = decomp_term sigma concl in
      match t with
      | App (c, [|typ; tl; tr|])
          when typ === bool && c === eq ->
          let env = Env.empty () in
          let fl = Bool.quote env sigma tl in
          let fr = Bool.quote env sigma tr in
          let env = Env.to_list env in
          let fl = reify env fl in
          let fr = reify env fr in
          let changed_gl = Constr.mkApp (c, [|typ; fl; fr|]) in
          let changed_gl = EConstr.of_constr changed_gl in
          Tacticals.New.tclTHENLIST [
            Tactics.change_concl changed_gl;
            Tactics.apply (EConstr.of_constr (Lazy.force soundness));
            Tactics.normalise_vm_in_concl;
            try_unification env
          ]
      | _ ->
          let msg = str "Cannot recognize a boolean equality" in
          Tacticals.New.tclFAIL 0 msg
    end

end
