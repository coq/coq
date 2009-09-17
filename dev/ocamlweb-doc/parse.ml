
open Ast

type assoc = L | R | N

let level = function
  | "--" -> 70,L
  | "=" -> 70,N
  | "+" -> 60,L
  | "++" -> 60,R
  | "+++" -> 60,R
  | "-" -> 60,L
  | "*" -> 50,L
  | "/" -> 50,L
  | "**" -> 40,R
  | ":" -> (100,R)
  | "->" -> (90,R)
  | s -> failwith ("unknowm operator '"^s^"'")

let fixity = function
  | "--" -> [L]
  | "=" -> [N]
  | ("+"|"-"|"*"|"/") -> [L;N]
  | "++" -> [R]
  | _ -> [L;N;R]

let ground_oper = function
    ("-"|"+") -> true
  | _ -> false

let is_prefix op = List.mem L (fixity op)
let is_infix op = List.mem N (fixity op)
let is_postfix op = List.mem R (fixity op)

let mk_inf op t1 t2 =
  if not (is_infix op) then failwith (op^" not infix");
  Infix(op,t1,t2)

let mk_post op t =
  if not (is_postfix op) then failwith (op^" not postfix");
  Postfix(op,t)


(* Pb avec ground_oper: pas de diff entre -1 et -(1) *)
let mk_pre op t =
  if not (is_prefix op) then failwith (op^" not prefix");
  if ground_oper op then
    match t with
    | Int i -> Int (op^i)
    | _     -> Prefix(op,t)
  else Prefix(op,t)

(* teste si on peut reduire op suivi d'un op de niveau (n,a)
   si la reponse est false, c'est que l'op (n,a) doit se reduire
   avant *)
let red_left_op (nl,al) (nr,ar) =
  if nl < nr then true
  else
    if nl = nr then
      match al,ar with
        | (L|N), L -> true
        | R, (R|N) -> false
        | R, L ->  failwith "conflit d'assoc: ambigu"
        | (L|N), (R|N) -> failwith "conflit d'assoc: blocage"
    else false


type level = int * assoc
type stack =
  | PrefixOper of string list
  | Term of constr_ast * stack
  | Oper of string list * string * constr_ast * stack

let rec str_ast = function
  | Infix(op,t1,t2) -> str_ast t1 ^ " " ^ op ^ " " ^ str_ast t2
  | Postfix(op,t) -> str_ast t ^ " " ^ op
  | Prefix(op,t) -> op ^ " " ^ str_ast t
  | _ -> "_"

let rec str_stack = function
  | PrefixOper ops -> String.concat " " (List.rev ops)
  | Term (t,s) -> str_stack s ^ " (" ^ str_ast t ^ ")"
  | Oper(ops,lop,t,s) ->
      str_stack (Term(t,s)) ^ " " ^ lop ^ " " ^
      String.concat " " (List.rev ops)

let pps s = prerr_endline (str_stack s)
let err s stk = failwith (s^": "^str_stack stk)


let empty = PrefixOper []

let check_fixity_term stk =
  match stk with
      Term _ -> err "2 termes successifs" stk
    | _ -> ()

let shift_term t stk =
  check_fixity_term stk;
  Term(t,stk)

let shift_oper op stk =
  match stk with
    | Oper(ops,lop,t,s) -> Oper(op::ops,lop,t,s)
    | Term(t,s) -> Oper([],op,t,s)
    | PrefixOper ops -> PrefixOper (op::ops)

let is_reducible lv stk =
  match stk with
    | Oper([],iop,_,_)  -> red_left_op (level iop) lv
    | Oper(op::_,_,_,_) -> red_left_op (level op) lv
    | PrefixOper(op::_) -> red_left_op (level op) lv
    | _                 -> false

let reduce_head (t,stk) =
  match stk with
    | Oper([],iop,t1,s) ->
        (Infix(iop,t1,t), s)
    | Oper(op::ops,lop,t',s) ->
        (mk_pre op t, Oper(ops,lop,t',s))
    | PrefixOper(op::ops) ->
        (Prefix(op,t), PrefixOper ops)
    | _ -> assert false

let rec reduce_level lv (t,s) =
  if is_reducible lv s then reduce_level lv (reduce_head (t, s))
  else (t, s)

let reduce_post op (t,s) =
  let (t',s') = reduce_level (level op) (t,s) in
  (mk_post op t', s')

let reduce_posts stk =
  match stk with
      Oper(ops,iop,t,s) ->
        let pts1 = reduce_post iop (t,s) in
        List.fold_right reduce_post ops pts1
    | Term(t,s) -> (t,s)
    | PrefixOper _ -> failwith "reduce_posts"


let shift_infix op stk =
  let (t,s) = reduce_level (level op) (reduce_posts stk) in
  Oper([],op,t,s)

let is_better_infix op stk =
  match stk with
    | Oper(ops,iop,t,s) ->
        is_postfix iop &&
        List.for_all is_postfix ops &&
        (not (is_prefix op) || red_left_op (level iop) (level op))
    | Term _ -> false
    | _ -> assert false

let parse_oper op stk =
  match stk with
    | PrefixOper _ ->
        if is_prefix op then shift_oper op stk else failwith "prefix_oper"
    | Oper _ ->
        if is_infix op then
          if is_better_infix op stk then shift_infix op stk
          else shift_oper op stk
        else if is_prefix op then shift_oper op stk
        else if is_postfix op then
          let (t,s) = reduce_post op (reduce_posts stk) in
          Term(t,s)
        else assert false
    | Term(t,s) ->
        if is_infix op then shift_infix op stk
        else if is_postfix op then
          let (t2,s2) = reduce_post op (t,s) in Term(t2,s2)
        else failwith "infix/postfix"

let parse_term = shift_term

let rec close_stack stk =
  match stk with
      Term(t,PrefixOper []) -> t
    | PrefixOper _ -> failwith "expression sans atomes"
    | _ ->
        let (t,s) = reduce_head (reduce_posts stk) in
        close_stack (Term(t,s))

