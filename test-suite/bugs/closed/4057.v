Require Coq.Strings.String.

Set Implicit Arguments.

Axiom falso : False.
Ltac admit := destruct falso.

Reserved Notation "[ x ]".

Record string_like (CharType : Type) :=
  {
    String :> Type;
    Singleton : CharType -> String where "[ x ]" := (Singleton x);
    Empty : String;
    Concat : String -> String -> String where "x ++ y" := (Concat x y);
    bool_eq : String -> String -> bool;
    bool_eq_correct : forall x y : String, bool_eq x y = true <-> x = y;
    Length : String -> nat
  }.

Delimit Scope string_like_scope with string_like.
Bind Scope string_like_scope with String.
Arguments Length {_%type_scope _} _%string_like.
Infix "++" := (@Concat _ _) : string_like_scope.

Definition str_le {CharType} {String : string_like CharType} (s1 s2 : String)
  := Length s1 < Length s2 \/ s1 = s2.
Infix "â‰¤s" := str_le (at level 70, right associativity).

Module Export ContextFreeGrammar.
  Import Coq.Strings.String.
  Import Coq.Lists.List.

  Section cfg.
    Variable CharType : Type.

    Section definitions.

      Inductive item :=
    | NonTerminal (name : string).

      Definition production := list item.
      Definition productions := list production.

      Record grammar :=
        {
          Start_symbol :> string;
          Lookup :> string -> productions
        }.
    End definitions.

    Section parse.
      Variable String : string_like CharType.
      Variable G : grammar.

      Inductive parse_of : String -> productions -> Type :=
      | ParseHead : forall str pat pats, parse_of_production str pat
                                         -> parse_of str (pat::pats)
      | ParseTail : forall str pat pats, parse_of str pats
                                         -> parse_of str (pat::pats)
      with parse_of_production : String -> production -> Type :=
      | ParseProductionCons : forall str pat strs pats,
                                parse_of_item str pat
                                -> parse_of_production strs pats
                                -> parse_of_production (str ++ strs) (pat::pats)
      with parse_of_item : String -> item -> Type :=
      | ParseNonTerminal : forall name str, parse_of str (Lookup G name)
                                            -> parse_of_item str (NonTerminal 
name).
    End parse.
  End cfg.

End ContextFreeGrammar.
Module Export ContextFreeGrammarProperties.

  Section cfg.
    Context CharType (String : string_like CharType) (G : grammar)
            (P : String.string -> Type).

    Fixpoint Forall_parse_of {str pats} (p : parse_of String G str pats)
      := match p with
           | @ParseHead _ _ _ str pat pats p'
             => Forall_parse_of_production p'
           | @ParseTail _ _ _ _ _ _ p'
             => Forall_parse_of p'
         end
    with Forall_parse_of_production {str pat} (p : parse_of_production String G 
str pat)
         := let Forall_parse_of_item {str it} (p : parse_of_item String G str 
it)
                := match p return Type with
                     | @ParseNonTerminal _ _ _ name str p'
                       => (P name * Forall_parse_of p')%type
                   end in
            match p return Type with
              | @ParseProductionCons _ _ _ str pat strs pats p' p''
                => (Forall_parse_of_item p' * Forall_parse_of_production 
p'')%type
            end.

    Definition Forall_parse_of_item {str it} (p : parse_of_item String G str it)
      := match p return Type with
           | @ParseNonTerminal _ _ _ name str p'
             => (P name * Forall_parse_of p')%type
         end.
  End cfg.

End ContextFreeGrammarProperties.

Module Export DependentlyTyped.
  Import Coq.Strings.String.

  Section recursive_descent_parser.

    Class parser_computational_predataT :=
      { nonterminal_names_listT : Type;
        initial_nonterminal_names_data : nonterminal_names_listT;
        is_valid_nonterminal_name : nonterminal_names_listT -> string -> bool;
        remove_nonterminal_name : nonterminal_names_listT -> string -> 
nonterminal_names_listT }.

  End recursive_descent_parser.

End DependentlyTyped.
Import Coq.Strings.String.
Import Coq.Lists.List.

Section cfg.
  Context CharType (String : string_like CharType) (G : grammar).
  Context (names_listT : Type)
          (initial_names_data : names_listT)
          (is_valid_name : names_listT -> string -> bool)
          (remove_name : names_listT -> string -> names_listT).

  Inductive minimal_parse_of
  : forall (str0 : String) (valid : names_listT)
           (str : String),
      productions -> Type :=
  | MinParseHead : forall str0 valid str pat pats,
                     @minimal_parse_of_production str0 valid str pat
                     -> @minimal_parse_of str0 valid str (pat::pats)
  | MinParseTail : forall str0 valid str pat pats,
                     @minimal_parse_of str0 valid str pats
                     -> @minimal_parse_of str0 valid str (pat::pats)
  with minimal_parse_of_production
       : forall (str0 : String) (valid : names_listT)
                (str : String),
           production -> Type :=
  | MinParseProductionNil : forall str0 valid,
                              @minimal_parse_of_production str0 valid (Empty _) 
nil
  | MinParseProductionCons : forall str0 valid str strs pat pats,
                               str ++ strs â‰¤s str0
                               -> @minimal_parse_of_item str0 valid str pat
                               -> @minimal_parse_of_production str0 valid strs 
pats
                               -> @minimal_parse_of_production str0 valid (str 
++ strs) (pat::pats)
  with minimal_parse_of_item
       : forall (str0 : String) (valid : names_listT)
                (str : String),
           item -> Type :=
  | MinParseNonTerminal
    : forall str0 valid str name,
        @minimal_parse_of_name str0 valid str name
        -> @minimal_parse_of_item str0 valid str (NonTerminal name)
  with minimal_parse_of_name
       : forall (str0 : String) (valid : names_listT)
                (str : String),
           string -> Type :=
  | MinParseNonTerminalStrLt
    : forall str0 valid name str,
        @minimal_parse_of str initial_names_data str (Lookup G name)
        -> @minimal_parse_of_name str0 valid str name
  | MinParseNonTerminalStrEq
    : forall str valid name,
        @minimal_parse_of str (remove_name valid name) str (Lookup G name)
        -> @minimal_parse_of_name str valid str name.
  Definition parse_of_item_name__of__minimal_parse_of_name
  : forall {str0 valid str name} (p : @minimal_parse_of_name str0 valid str 
name),
      parse_of_item String G str (NonTerminal name).
  Proof.
    admit.
  Defined.

End cfg.

Section recursive_descent_parser.
  Context (CharType : Type)
          (String : string_like CharType)
          (G : grammar).
  Context {premethods : parser_computational_predataT}.
  Let P : string -> Prop.
  Proof.
    admit.
  Defined.

  Let mp_parse_nonterminal_name str0 valid str nonterminal_name
    := { p' : minimal_parse_of_name String G initial_nonterminal_names_data 
remove_nonterminal_name str0 valid str nonterminal_name & Forall_parse_of_item 
P (parse_of_item_name__of__minimal_parse_of_name p') }.

  Goal False.
  Proof.
    clear -mp_parse_nonterminal_name.
    subst P.
    simpl in *.
    admit.
  Qed.
