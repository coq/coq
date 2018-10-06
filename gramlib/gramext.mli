(* camlp5r *)
(* gramext.mli,v *)
(* Copyright (c) INRIA 2007-2017 *)

type parser_t 'a = Stream.t 'a -> Obj.t;
type fparser_t 'a = Fstream.t 'a -> option (Obj.t * Fstream.t 'a);
type bparser_t 'a = Fstream.bp 'a Obj.t;

type parse_algorithm =
  [ Predictive | Functional | Backtracking | DefaultAlgorithm ];

type grammar 'te =
  { gtokens : Hashtbl.t Plexing.pattern (ref int);
    glexer : mutable Plexing.lexer 'te;
    galgo : mutable parse_algorithm }
;

type g_entry 'te =
  { egram : grammar 'te;
    ename : string;
    elocal : bool;
    estart : mutable int -> parser_t 'te;
    econtinue : mutable int -> int -> Obj.t -> parser_t 'te;
    fstart : mutable int -> err_fun -> fparser_t 'te;
    fcontinue : mutable int -> int -> Obj.t -> err_fun -> fparser_t 'te;
    bstart : mutable int -> err_fun -> bparser_t 'te;
    bcontinue : mutable int -> int -> Obj.t -> err_fun -> bparser_t 'te;
    edesc : mutable g_desc 'te }
and g_desc 'te =
  [ Dlevels of list (g_level 'te)
  | Dparser of parser_t 'te ]
and g_level 'te =
  { assoc : g_assoc;
    lname : option string;
    lsuffix : g_tree 'te;
    lprefix : g_tree 'te }
and g_assoc = [ NonA | RightA | LeftA ]
and g_symbol 'te =
  [ Sfacto of g_symbol 'te
  | Smeta of string and list (g_symbol 'te) and Obj.t
  | Snterm of g_entry 'te
  | Snterml of g_entry 'te and string
  | Slist0 of g_symbol 'te
  | Slist0sep of g_symbol 'te and g_symbol 'te and bool
  | Slist1 of g_symbol 'te
  | Slist1sep of g_symbol 'te and g_symbol 'te and bool
  | Sopt of g_symbol 'te
  | Sflag of g_symbol 'te
  | Sself
  | Snext
  | Scut
  | Stoken of Plexing.pattern
  | Stree of g_tree 'te
  | Svala of list string and g_symbol 'te ]
and g_action = Obj.t
and g_tree 'te =
  [ Node of g_node 'te
  | LocAct of g_action and list g_action
  | DeadEnd ]
and g_node 'te =
  { node : g_symbol 'te; son : g_tree 'te; brother : g_tree 'te }
and err_fun = unit -> string;

type position =
  [ First
  | Last
  | Before of string
  | After of string
  | Like of string
  | Level of string ]
;

value levels_of_rules :
  g_entry 'te -> option position ->
    list
      (option string * option g_assoc *
       list (list (g_symbol 'te) * g_action)) ->
    list (g_level 'te);
value srules : list (list (g_symbol 'te) * g_action) -> g_symbol 'te;
external action : 'a -> g_action = "%identity";
value eq_symbol : g_symbol 'a -> g_symbol 'a -> bool;

value delete_rule_in_level_list :
  g_entry 'te -> list (g_symbol 'te) -> list (g_level 'te) ->
    list (g_level 'te);

value warning_verbose : ref bool;
