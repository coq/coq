open Printf
open Opname
open List

(* Definitions of [jterm]: *)
type  param = param'
   and operator = operator'
   and term = term'
   and bound_term = bound_term'
   and param' =
    | Number of int
    | String of string
    | Token of string
    | Var of string
    | ParamList of param list
   and operator' = { op_name : opname; op_params : param list }
   and term' = { term_op : operator; term_terms : bound_term list }
   and bound_term' = { bvars : string list; bterm : term }
;;

(* Debugging tools: *)
(*i*)
let mbreak s = Format.print_flush (); print_string ("-break at: "^s);
               Format.print_flush (); let _ = input_char stdin in ()
(*i*)

type error_msg =
    | TermMatchError of term * string
    | StringError of string

exception RefineError of string * error_msg

let ref_raise = function
 |  RefineError(s,e) -> raise (RefineError(s,e))
 |  _ -> raise (RefineError ("Jterm", StringError "unexpected error"))

(* Printing utilities: *)

let fprint_str ostream s =
    let _ = fprintf ostream "%s." s in ostream

let fprint_str_list ostream sl =
    ignore (List.fold_left fprint_str ostream sl);
    Format.print_flush ()

let fprint_opname ostream = function
    { opname_token= tk; opname_name = sl } ->
        fprint_str_list ostream sl

let rec fprint_param ostream = function
    | Number n -> fprintf ostream " %d " n
    | String s -> fprint_str_list ostream [s]
    | Token t -> fprint_str_list ostream [t]
    | Var v -> fprint_str_list ostream [v]
    | ParamList ps -> fprint_param_list ostream ps
and fprint_param_list ostream = function
    | [] -> ()
    | param::r -> fprint_param ostream param;
                  fprint_param_list ostream r
;;

let print_strs = fprint_str_list stdout


(* Interface to [Jall.ml]: *)
(* It is extracted from Meta-Prl's standard implementation. *)
(*c begin of the extraction *)

type term_subst = (string * term) list
let mk_term op bterms = { term_op = op; term_terms = bterms }
let make_term x = x (* external [make_term : term' -> term] = "%identity" *)
let dest_term x = x (* external [dest_term : term -> term'] = "%identity" *)
let mk_op name params =
   { op_name = name; op_params = params }

let make_op x = x (* external [make_op : operator' -> operator] = "%identity" *)
let dest_op x = x (* external [dest_op : operator -> operator'] = "%identity" *)
let mk_bterm bvars term = { bvars = bvars; bterm = term }
let make_bterm x = x (* external [make_bterm : bound_term' -> bound_term] = "%identity" *)
let dest_bterm x = x (* external [dest_bterm : bound_term -> bound_term'] = "%identity" *)
let make_param x = x (* external [make_param : param' -> param] = "%identity" *)
let dest_param x = x (* external [dest_param : param -> param'] = "%identity" *)

(*
 * Operator names.
 *)
let opname_of_term = function
   { term_op = { op_name = name } } ->
      name

(*
 * Get the subterms.
 * None of the subterms should be bound.
 *)
let subterms_of_term t =
   List.map (fun { bterm = t } -> t) t.term_terms

let subterm_count { term_terms = terms } =
   List.length terms

let subterm_arities { term_terms = terms } =
   List.map (fun { bvars = vars } -> List.length vars) terms

(*
 * Manifest terms are injected into the "perv" module.
 *)
let xperv = make_opname ["Perv"]
let sequent_opname = mk_opname "sequent" xperv

(*
 * Variables.
 *)

let var_opname = make_opname ["var"]

(*
 * See if a term is a variable.
 *)
let is_var_term = function
 | { term_op = { op_name = opname; op_params = [Var v] };
     term_terms = []
   } when Opname.eq opname var_opname -> true
 | _ ->
      false

(*
 * Destructor for a variable.
 *)
let dest_var = function
 | { term_op = { op_name = opname; op_params = [Var v] };
     term_terms = []
   } when Opname.eq opname var_opname -> v
 | t ->
       ref_raise(RefineError ("dest_var", TermMatchError (t, "not a variable")))
(*
 * Make a variable.
 *)
let mk_var_term v =
   { term_op = { op_name = var_opname; op_params = [Var v] };
     term_terms = []
   }

(*
 * Simple terms
 *)
(*
 * "Simple" terms have no parameters and no binding variables.
 *)
let is_simple_term_opname name = function
 | { term_op = { op_name = name'; op_params = [] };
     term_terms = bterms
   } when Opname.eq name' name ->
      let rec aux = function
       | { bvars = []; bterm = _ }::t -> aux t
       | _::t -> false
       | [] -> true
      in
         aux bterms
 | _ -> false

let mk_any_term op terms =
   let aux t =
      { bvars = []; bterm = t }
   in
      { term_op = op; term_terms = List.map aux terms }

let mk_simple_term name terms =
   mk_any_term { op_name = name; op_params = [] } terms

let dest_simple_term = function
 | ({ term_op = { op_name = name; op_params = [] };
      term_terms = bterms
    } : term) as t ->
      let aux = function
       | { bvars = []; bterm = t } ->
            t
       | _ ->
            ref_raise(RefineError ("dest_simple_term", TermMatchError (t, "binding vars exist")))
      in
         name, List.map aux bterms
 | t ->
      ref_raise(RefineError ("dest_simple_term", TermMatchError (t, "params exist")))

let dest_simple_term_opname name = function
 | ({ term_op = { op_name = name'; op_params = [] };
      term_terms = bterms
    } : term) as t ->
      if Opname.eq name name' then
         let aux = function
          | { bvars = []; bterm = t } -> t
          | _ -> ref_raise(RefineError ("dest_simple_term_opname", TermMatchError (t, "binding vars exist")))
         in
            List.map aux bterms
      else
         ref_raise(RefineError ("dest_simple_term_opname", TermMatchError (t, "opname mismatch")))
 | t ->
      ref_raise(RefineError ("dest_simple_term_opname", TermMatchError (t, "params exist")))

(*
 * Bound terms.
 *)
let mk_simple_bterm bterm =
   { bvars = []; bterm = bterm }

let dest_simple_bterm = function
 | { bvars = []; bterm = bterm } ->
      bterm
 | _ ->
      ref_raise(RefineError ("dest_simple_bterm", StringError ("bterm is not simple")))

(* Copy from [term_op_std.ml]: *)
(*i modified for Jprover, as a patch... i*)
let mk_string_term opname s =
   { term_op = { op_name = opname; op_params = [String s] }; term_terms = [] }

(*i let mk_string_term opname s =
  let new_opname={opname_token=opname.opname_token; opname_name=(List.tl opname.opname_name)@[s]} in
    { term_op = { op_name = new_opname; op_params = [String (List.hd opname.opname_name)] }; term_terms = [] }
i*)

(* Copy from [term_subst_std.ml]: *)

let rec free_vars_term gvars bvars = function
    | { term_op = { op_name = opname; op_params = [Var v] }; term_terms = bterms } when Opname.eq opname var_opname ->
         (* This is a variable *)
         let gvars' =
            if List.mem v bvars or List.mem v gvars then
               gvars
            else
               v::gvars
         in
            free_vars_bterms gvars' bvars bterms
    | { term_terms = bterms } ->
         free_vars_bterms gvars bvars bterms
   and free_vars_bterms gvars bvars = function
    | { bvars = vars; bterm = term}::l ->
         let bvars' = vars @ bvars in
         let gvars' = free_vars_term gvars bvars' term in
            free_vars_bterms gvars' bvars l
    | [] ->
         gvars

let free_vars_list = free_vars_term [] []


(* Termop: *)

let is_no_subterms_term opname = function
 | { term_op = { op_name = opname'; op_params = [] };
     term_terms = []
   } ->
      Opname.eq opname' opname
 | _ ->
      false

(*
 * Terms with one subterm.
 *)
let is_dep0_term opname = function
 | { term_op = { op_name = opname'; op_params = [] };
     term_terms = [{ bvars = [] }]
   } -> Opname.eq opname' opname
 | _ -> false

let mk_dep0_term opname t =
   { term_op = { op_name = opname; op_params = [] };
     term_terms = [{ bvars = []; bterm = t }]
   }

let dest_dep0_term opname = function
 | { term_op = { op_name = opname'; op_params = [] };
     term_terms = [{ bvars = []; bterm = t }]
   } when Opname.eq opname' opname -> t
 | t -> ref_raise(RefineError ("dest_dep0_term", TermMatchError (t, "not a dep0 term")))

(*
 * Terms with two subterms.
 *)
let is_dep0_dep0_term opname = function
 | { term_op = { op_name = opname'; op_params = [] };
     term_terms = [{ bvars = [] }; { bvars = [] }]
   } -> Opname.eq opname' opname
 | _ -> false

let mk_dep0_dep0_term opname = fun
   t1 t2 ->
      { term_op = { op_name = opname; op_params = [] };
        term_terms = [{ bvars = []; bterm = t1 };
                      { bvars = []; bterm = t2 }]
      }

let dest_dep0_dep0_term opname = function
 | { term_op = { op_name = opname'; op_params = [] };
     term_terms = [{ bvars = []; bterm = t1 };
                   { bvars = []; bterm = t2 }]
   } when Opname.eq opname' opname -> t1, t2
 | t -> ref_raise(RefineError ("dest_dep0_dep0_term", TermMatchError (t, "bad arity")))

(*
 * Bound term.
 *)

let is_dep0_dep1_term opname = function
 | { term_op = { op_name = opname'; op_params = [] };
     term_terms = [{ bvars = [] }; { bvars = [_] }]
   } when Opname.eq opname' opname -> true
 | _ -> false

let is_dep0_dep1_any_term = function
 | { term_op = { op_params = [] };
     term_terms = [{ bvars = [] }; { bvars = [_] }]
   } -> true
 | _ -> false

let mk_dep0_dep1_term opname = fun
   v t1 t2 -> { term_op = { op_name = opname; op_params = [] };
                term_terms = [{ bvars = []; bterm = t1 };
                              { bvars = [v]; bterm = t2 }]
              }

let dest_dep0_dep1_term opname = function
 | { term_op = { op_name = opname'; op_params = [] };
     term_terms = [{ bvars = []; bterm = t1 };
                   { bvars = [v]; bterm = t2 }]
   } when Opname.eq opname' opname -> v, t1, t2
 | t -> ref_raise(RefineError ("dest_dep0_dep1_term", TermMatchError (t, "bad arity")))

let rec smap f = function
 | [] -> []
 | (hd::tl) as l ->
      let hd' = f hd in
      let tl' = smap f tl in
      if (hd==hd')&&(tl==tl') then l else hd'::tl'

let rec try_check_assoc v v' = function
 | [] -> raise Not_found
 | (v1,v2)::tl ->
      begin match v=v1, v'=v2 with
       | true, true -> true
       | false, false -> try_check_assoc v v' tl
       | _ -> false
      end

let rec zip_list l l1 l2 = match (l1,l2) with
 | (h1::t1), (h2::t2) ->
      zip_list ((h1,h2)::l) t1 t2
 | [], [] ->
      l
 | _ -> raise (Failure "Term.zip_list")

let rec assoc_in_range eq y = function
 | (_, y')::tl ->
      (eq y y') || (assoc_in_range eq y tl)
 | [] ->
      false

let rec check_assoc v v' = function
 | [] -> v=v'
 | (v1,v2)::tl ->
      begin match v=v1, v'=v2 with
       | true, true -> true
       | false, false -> check_assoc v v' tl
       | _ -> false
      end

let rec zip a b = match (a,b) with
 | (h1::t1), (h2::t2) ->
      (h1, h2) :: zip t1 t2
 | [], [] ->
      []
 |
   _ -> raise (Failure "Term.zip")

let rec for_all2 f l1 l2 =
   match (l1,l2) with
    | h1::t1, h2::t2 -> for_all2 f t1 t2 & f h1 h2
    | [], [] -> true
    | _ -> false

let newname v i =
   v ^ "_" ^ (string_of_int i)

let rec new_var v avoid i =
   let v' = newname v i in
   if avoid v'
      then new_var v avoid (succ i)
      else v'

let vnewname v avoid = new_var v avoid 1

let rev_mem a b = List.mem b a

let rec find_index_aux v i = function
 | h::t ->
      if h = v then
         i
      else
         find_index_aux v (i + 1) t
 | [] ->
      raise Not_found

let find_index v l = find_index_aux v 0 l

let rec remove_elements l1 l2 =
   match l1, l2 with
    | flag::ft, h::t ->
         if flag then
            remove_elements ft t
         else
            h :: remove_elements ft t
    | _, l ->
         l

let rec subtract l1 l2 =
   match l1 with
    | h::t ->
         if List.mem h l2 then
            subtract t l2
         else
            h :: subtract t l2
    | [] ->
         []

let rec fv_mem fv v =
      match fv with
       | [] -> false
       | h::t ->
            List.mem v h || fv_mem t v

let rec new_vars fv = function
    | [] -> []
    | v::t ->
         (* Rename the first one, then add it to free vars *)
         let v' = vnewname v (fv_mem fv) in
            v'::(new_vars ([v']::fv) t)

let rec fsubtract l = function
    | [] -> l
    | h::t ->
         fsubtract (subtract l h) t

let add_renames_fv r l =
    let rec aux = function
    | [] -> l
    | v::t -> [v]::(aux t)
   in
      aux r

let add_renames_terms r l =
   let rec aux = function
    | [] -> l
    | v::t -> (mk_var_term v)::(aux t)
   in
      aux r

(*
 * First order simultaneous substitution.
 *)
let rec subst_term terms fv vars = function
 | { term_op = { op_name = opname; op_params = [Var(v)] }; term_terms = [] } as t
   when Opname.eq opname var_opname->
      (* Var case *)
      begin
         try List.nth terms (find_index v vars) with
            Not_found ->
               t
      end
 | { term_op = op; term_terms = bterms } ->
      (* Other term *)
      { term_op = op; term_terms = subst_bterms terms fv vars bterms }

and subst_bterms terms fv vars bterms =
   (* When subst through bterms, catch binding occurrences *)
   let rec subst_bterm = function
    | { bvars = []; bterm = term } ->
         (* Optimize the common case *)
         { bvars = []; bterm = subst_term terms fv vars term }

    | { bvars = bvars; bterm = term } ->
         (* First subtract bound instances *)
         let flags = List.map (function v -> List.mem v bvars) vars in
         let vars' = remove_elements flags vars in
         let fv' = remove_elements flags fv in
         let terms' = remove_elements flags terms in

         (* If any of the binding variables are free, rename them *)
         let renames = subtract bvars (fsubtract bvars fv') in
            if renames <> [] then
               let fv'' = (free_vars_list term)::fv' in
               let renames' = new_vars fv'' renames in
                  { bvars = subst_bvars renames' renames bvars;
                    bterm = subst_term
                            (add_renames_terms renames' terms')
                            (add_renames_fv renames' fv')
                            (renames @ vars')
                            term
                  }
            else
               { bvars = bvars;
                 bterm = subst_term terms' fv' vars' term
               }
   in
      List.map subst_bterm bterms

and subst_bvars renames' renames bvars =
   let subst_bvar v =
      try List.nth renames' (find_index v renames) with
         Not_found -> v
   in
      List.map subst_bvar bvars

let subst term vars terms =
      subst_term terms (List.map free_vars_list terms) vars term

(*i bug!!! in the [term_std] module
      let subst1 t var term =
      let fv = free_vars_list term in
      if List.mem var fv then
         subst_term [term] [fv] [var] t
      else
         t
The following is the correct implementation
i*)

let subst1 t var term =
if List.mem var (free_vars_list t) then
   subst_term [term] [free_vars_list term] [var] t
else
   t

let apply_subst t s =
   let vs,ts = List.split s in
   subst t vs ts

let rec equal_params p1 p2 =
   match p1, p2 with
    | Number n1, Number n2 ->
         n1 = n2
    | ParamList pl1, ParamList pl2 ->
         List.for_all2 equal_params pl1 pl2
    | _ ->
         p1 = p2

let rec equal_term vars t t' =
   match t, t' with
    | { term_op = { op_name = opname1; op_params = [Var v] };
        term_terms = []
      },
      { term_op = { op_name = opname2; op_params = [Var v'] };
        term_terms = []
      } when Opname.eq opname1 var_opname & Opname.eq opname2 var_opname ->
         check_assoc v v' vars
    | { term_op = { op_name = name1; op_params = params1 }; term_terms = bterms1 },
      { term_op = { op_name = name2; op_params = params2 }; term_terms = bterms2 } ->
         (Opname.eq name1 name2)
         & (for_all2 equal_params params1 params2)
         & (equal_bterms vars bterms1 bterms2)
and equal_bterms vars bterms1 bterms2 =
   let equal_bterm = fun
      { bvars = bvars1; bterm = term1 }
      { bvars = bvars2; bterm = term2 } ->
         equal_term (zip_list vars bvars1 bvars2) term1 term2
   in
      for_all2 equal_bterm bterms1 bterms2


let alpha_equal t1 t2 =
   try equal_term [] t1 t2 with Failure _ -> false

let var_subst t t' v =
   let { term_op = { op_name = opname } } = t' in
   let vt = mk_var_term v in
   let rec subst_term = function
      { term_op = { op_name = opname'; op_params = params };
        term_terms = bterms
      } as t ->
         (* Check if this is the same *)
         if Opname.eq opname' opname & alpha_equal t t' then
            vt
         else
            { term_op = { op_name = opname'; op_params = params };
              term_terms = List.map subst_bterm bterms
            }

   and subst_bterm { bvars = vars; bterm = term } =
      if List.mem v vars then
         let av = vars @ (free_vars_list term) in
         let v' = vnewname v (fun v -> List.mem v av) in
         let rename var = if var = v then v' else var in
         let term = subst1 term v (mk_var_term v') in
            { bvars =  smap rename vars; bterm = subst_term term }
      else
         { bvars = vars; bterm = subst_term term }
   in
      subst_term t

let xnil_opname = mk_opname "nil" xperv
let xnil_term = mk_simple_term xnil_opname []
let is_xnil_term = is_no_subterms_term xnil_opname

(*c End of the extraction from Meta-Prl *)

(* Huang's modification: *)
let all_opname = make_opname ["quantifier";"all"]
let is_all_term = is_dep0_dep1_term all_opname
let dest_all = dest_dep0_dep1_term all_opname
let mk_all_term = mk_dep0_dep1_term all_opname

let exists_opname = make_opname ["quantifier";"exst"]
let is_exists_term = is_dep0_dep1_term exists_opname
let dest_exists = dest_dep0_dep1_term exists_opname
let mk_exists_term = mk_dep0_dep1_term exists_opname

let or_opname = make_opname ["connective";"or"]
let is_or_term = is_dep0_dep0_term or_opname
let dest_or = dest_dep0_dep0_term or_opname
let mk_or_term = mk_dep0_dep0_term or_opname

let and_opname = make_opname ["connective";"and"]
let is_and_term = is_dep0_dep0_term and_opname
let dest_and = dest_dep0_dep0_term and_opname
let mk_and_term = mk_dep0_dep0_term and_opname

let cor_opname = make_opname ["connective";"cor"]
let is_cor_term = is_dep0_dep0_term cor_opname
let dest_cor = dest_dep0_dep0_term cor_opname
let mk_cor_term = mk_dep0_dep0_term cor_opname

let cand_opname = make_opname ["connective";"cand"]
let is_cand_term = is_dep0_dep0_term cand_opname
let dest_cand = dest_dep0_dep0_term cand_opname
let mk_cand_term = mk_dep0_dep0_term cand_opname

let implies_opname = make_opname ["connective";"=>"]
let is_implies_term = is_dep0_dep0_term implies_opname
let dest_implies = dest_dep0_dep0_term implies_opname
let mk_implies_term = mk_dep0_dep0_term implies_opname

let iff_opname = make_opname ["connective";"iff"]
let is_iff_term = is_dep0_dep0_term iff_opname
let dest_iff = dest_dep0_dep0_term iff_opname
let mk_iff_term = mk_dep0_dep0_term iff_opname

let not_opname = make_opname ["connective";"not"]
let is_not_term = is_dep0_term not_opname
let dest_not = dest_dep0_term not_opname
let mk_not_term = mk_dep0_term not_opname

let var_ = mk_var_term
let fun_opname = make_opname ["function"]
let fun_ f ts = mk_any_term {op_name = fun_opname; op_params = [String f] } ts

let is_fun_term = function
 | { term_op = { op_name = opname; op_params = [String f] }}
   when Opname.eq opname fun_opname -> true
 | _ ->
      false

let dest_fun = function
 | { term_op = { op_name = opname; op_params = [String f] }; term_terms = ts}
   when Opname.eq opname fun_opname -> (f, List.map (fun { bterm = t } -> t) ts)
 | t ->
   ref_raise(RefineError ("dest_fun", TermMatchError (t, "not a function symbol")))

let const_ c = fun_ c []
let is_const_term = function
 | { term_op = { op_name = opname; op_params = [String f] }; term_terms = [] }
   when Opname.eq opname fun_opname -> true
 | _ ->
      false

let dest_const t =
  let (n, ts) = dest_fun t in n

let pred_opname = make_opname ["predicate"]
let pred_ p ts = mk_any_term {op_name = pred_opname; op_params = [String p] } ts

let not_ = mk_not_term
let and_ = mk_and_term
let or_ = mk_or_term
let imp_ = mk_implies_term
let cand_ = mk_cand_term
let cor_ = mk_cor_term
let iff_ = mk_iff_term
let nil_term = {term_op={op_name=nil_opname; op_params=[]}; term_terms=[] }
let forall v t = mk_all_term v nil_term t
let exists v t= mk_exists_term v nil_term t
let rec wbin op = function
  |  [] ->  raise (Failure "Term.wbin")
  |  [t] -> t
  |  t::r -> op t (wbin op r)

let wand_ = wbin and_
let wor_ = wbin or_
let wimp_ = wbin imp_

(*i let true_opname = make_opname ["bool";"true"]
let is_true_term = is_no_subterms_term true_opname
let true_ = mk_simple_term true_opname []
let false_ = not_ true_

let is_false_term t =
  if is_not_term t then
  let t1 = dest_not t in
    is_true_term t1
  else
    false
i*)

let dummy_false_ = mk_simple_term (make_opname ["bool";"false"]) []
let dummy_true_ = mk_simple_term (make_opname ["bool";"true"]) []
let false_ = and_ (dummy_false_) (not_ dummy_false_)
let true_ = not_ (and_ (dummy_true_) (not_ dummy_true_))

let is_false_term t =
  if (alpha_equal t false_) then true
  else false

let is_true_term t =
  if (alpha_equal t true_) then true
  else false

(* Print a term [t] via the [ostream]: *)
let rec fprint_term ostream t prec =
  let l_print op_prec =
      if (prec > op_prec) then fprintf ostream "(" in
  let r_print op_prec =
      if (prec > op_prec) then fprintf ostream ")" in
  if is_false_term t then                       (* false *)
      fprint_str_list ostream ["False"]
  else if is_true_term t then                   (* true *)
      fprint_str_list ostream ["True"]
  else if is_all_term t then                    (* for all *)
      let v, t1, t2 = dest_all t in
          fprint_str_list ostream ["A."^v];
          fprint_term ostream t2 4
  else if is_exists_term t then                 (* exists *)
      let v, t1, t2 = dest_exists t in
          fprint_str_list ostream ["E."^v];
          fprint_term ostream t2 4              (* implication *)
  else if is_implies_term t then
      let t1, t2 = dest_implies t in
          l_print 0;
          fprint_term ostream t1 1;
          fprint_str_list ostream ["=>"];
          fprint_term ostream t2 0;
          r_print 0
  else if is_and_term t then                    (* logical and *)
      let t1, t2 = dest_and t in
          l_print 3;
          fprint_term ostream t1 3;
          fprint_str_list ostream ["&"];
          fprint_term ostream t2 3;
          r_print 3
  else if is_or_term t then                     (* logical or *)
      let t1, t2 = dest_or t in
          l_print 2;
          fprint_term ostream t1 2;
          fprint_str_list ostream ["|"];
          fprint_term ostream t2 2;
          r_print 2
  else if is_not_term t then                    (* logical not *)
      let t2 = dest_not t in
          fprint_str_list ostream ["~"];
          fprint_term ostream t2 4              (* nil term *)
  else if is_xnil_term t then
          fprint_str_list ostream ["NIL"]
  else match t with                             (* other cases *)
    { term_op = { op_name = opname; op_params = opparm }; term_terms = bterms} ->
        if (Opname.eq opname pred_opname) || (Opname.eq opname fun_opname) then
        begin
           fprint_param_list ostream opparm;
           if bterms != [] then
           begin
              fprintf ostream "(";
              fprint_bterm_list ostream prec bterms;
              fprintf ostream ")";
           end
        end else
        begin
           fprintf ostream "[";
(*           fprint_opname ostream opname;
           fprintf ostream ": "; *)
           fprint_param_list ostream opparm;
           if bterms != [] then
           begin
              fprintf ostream "(";
              fprint_bterm_list ostream prec bterms;
              fprintf ostream ")";
           end;
           fprintf ostream "]"
        end
and fprint_bterm_list ostream prec = function
   |  [] -> ()
   | {bvars=bv; bterm=bt}::r ->
        fprint_str_list ostream bv;
        fprint_term ostream bt prec;
        if (r<>[]) then fprint_str_list ostream [","];
        fprint_bterm_list ostream prec r
;;


let print_term ostream t =
    Format.print_flush ();
    fprint_term ostream t 0;
    Format.print_flush ()

let print_error_msg = function
    | RefineError(s,e) -> print_string ("(module "^s^") ");
      begin
      match e with
       | TermMatchError(t,s) -> print_term stdout t; print_string (s^"\n")
       | StringError s -> print_string (s^"\n")
      end
    | ue -> print_string "Unexpected error for Jp.\n";
           raise ue


(* Naive implementation for [jterm] substitution, unification, etc.: *)
let substitute subst term =
    apply_subst term subst

(* A naive unification algorithm: *)
let compsubst subst1 subst2 =
  (List.map (fun (v, t) -> (v, substitute subst1 t)) subst2) @ subst1
;;

let rec extract_terms = function
    | [] -> []
    | h::r -> let {bvars=_; bterm=bt}=h in bt::extract_terms r

(* Occurs check: *)
let occurs v t =
  let rec occur_rec t =
    if is_var_term t then v=dest_var t
    else let { term_op = _ ; term_terms = bterms} = t in
         let sons = extract_terms bterms in
            List.exists occur_rec sons
  in
  occur_rec t

(* The naive unification algorithm: *)
let rec unify2 (term1,term2) =
  if is_var_term term1 then
    if equal_term [] term1 term2 then []
    else let v1 = dest_var term1 in
            if occurs v1 term2 then raise (RefineError ("unify1", StringError ("1")))
            else [v1,term2]
  else if is_var_term term2 then
    let v2 = dest_var term2 in
       if occurs v2 term1 then raise (RefineError ("unify2", StringError ("2")))
       else [v2,term1]
  else
      let { term_op = { op_name = opname1; op_params = params1 };
            term_terms = bterms1
          } = term1
      in
      let { term_op = { op_name = opname2; op_params = params2 };
            term_terms = bterms2
          } = term2
      in
         if Opname.eq opname1 opname2 & params1 = params2 then
            let sons1 = extract_terms bterms1
            and sons2 = extract_terms bterms2 in
            List.fold_left2
               (fun s t1 t2 -> compsubst
                               (unify2 (substitute s t1, substitute s t2)) s)
               [] sons1 sons2
         else raise (RefineError ("unify3", StringError ("3")))

let unify term1 term2 = unify2 (term1, term2)
let unify_mm term1 term2 _ = unify2 (term1, term2)
