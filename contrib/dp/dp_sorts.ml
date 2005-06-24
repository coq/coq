
open Fol

let term_has_sort x s = Fatom (Pred ("%sort_" ^ s, [x]))

let has_sort x s = term_has_sort (App (x, [])) s

let rec form = function
  | True | False | Fatom _ as f -> f
  | Imp (f1, f2) -> Imp (form f1, form f2)
  | And (f1, f2) -> And (form f1, form f2)
  | Or (f1, f2) -> Or (form f1, form f2)
  | Not f -> Not (form f)
  | Forall (x, ("INT" as t), f) -> Forall (x, t, form f)
  | Forall (x, t, f) -> Forall (x, t, Imp (has_sort x t, form f))
  | Exists (x, ("INT" as t), f) -> Exists (x, t, form f)
  | Exists (x, t, f) -> Exists (x, t, Imp (has_sort x t, form f))

let sort_ax = let r = ref 0 in fun () -> incr r; "sort_ax_" ^ string_of_int !r

let hyp acc = function
  | Assert (id, f) -> 
      (Assert (id, form f)) :: acc
  | DeclVar (id, _, "INT") as d ->
      d :: acc
  | DeclVar (id, [], t) as d -> 
      (Assert (sort_ax (), has_sort id t)) :: d :: acc
  | DeclVar (id, l, t) as d -> 
      let n = ref 0 in
      let xi = 
	List.fold_left 
	  (fun l t -> incr n; ("x" ^ string_of_int !n, t) :: l) [] l
      in
      let f =
	List.fold_left
	  (fun f (x,t) -> if t = "INT" then f else Imp (has_sort x t, f))
	  (term_has_sort 
	     (App (id, List.rev_map (fun (x,_) -> App (x,[])) xi)) t)
	  xi 
      in
      let f = List.fold_left (fun f (x,t) -> Forall (x, t, f)) f xi in
      (Assert (sort_ax (), f)) :: d :: acc
  | DeclPred _ as d ->
      d :: acc
  | DeclType t as d ->
      (DeclPred ("%sort_" ^ t, [t])) :: d :: acc

let query (hyps, f) =
  let hyps' = List.fold_left hyp [] hyps in
  List.rev hyps', form f

