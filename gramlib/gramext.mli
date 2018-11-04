(* camlp5r *)
(* gramext.mli,v *)
(* Copyright (c) INRIA 2007-2017 *)

type 'a parser_t = 'a Stream.t -> Obj.t

type 'te grammar =
  { gtokens : (Plexing.pattern, int ref) Hashtbl.t;
    mutable glexer : 'te Plexing.lexer }

type 'te g_entry =
  { egram : 'te grammar;
    ename : string;
    elocal : bool;
    mutable estart : int -> 'te parser_t;
    mutable econtinue : int -> int -> Obj.t -> 'te parser_t;
    mutable edesc : 'te g_desc }
and 'te g_desc =
    Dlevels of 'te g_level list
  | Dparser of 'te parser_t
and 'te g_level =
  { assoc : g_assoc;
    lname : string option;
    lsuffix : 'te g_tree;
    lprefix : 'te g_tree }
and g_assoc = NonA | RightA | LeftA
and 'te g_symbol =
  | Snterm of 'te g_entry
  | Snterml of 'te g_entry * string
  | Slist0 of 'te g_symbol
  | Slist0sep of 'te g_symbol * 'te g_symbol * bool
  | Slist1 of 'te g_symbol
  | Slist1sep of 'te g_symbol * 'te g_symbol * bool
  | Sopt of 'te g_symbol
  | Sflag of 'te g_symbol
  | Sself
  | Snext
  | Scut
  | Stoken of Plexing.pattern
  | Stree of 'te g_tree
and g_action = Obj.t
and 'te g_tree =
    Node of 'te g_node
  | LocAct of g_action * g_action list
  | DeadEnd
and 'te g_node =
  { node : 'te g_symbol; son : 'te g_tree; brother : 'te g_tree }
and err_fun = unit -> string

type position =
    First
  | Last
  | Before of string
  | After of string
  | Like of string
  | Level of string

val levels_of_rules :
  'te g_entry -> position option ->
    (string option * g_assoc option * ('te g_symbol list * g_action) list)
      list ->
    'te g_level list
val srules : ('te g_symbol list * g_action) list -> 'te g_symbol
external action : 'a -> g_action = "%identity"
val eq_symbol : 'a g_symbol -> 'a g_symbol -> bool

val delete_rule_in_level_list :
  'te g_entry -> 'te g_symbol list -> 'te g_level list -> 'te g_level list

val warning_verbose : bool ref
