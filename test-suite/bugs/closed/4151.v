Lemma foo (H : forall A, A) : forall A, A.
  Show Universes.
  eexact H.
Qed.

(* File reduced by coq-bug-finder from original input, then from 6390 lines to 397 lines *)
(* coqc version 8.5beta1 (March 2015) compiled on Mar 17 2015 12:34:25 with OCaml 4.01.0
   coqtop version cagnode15:/afs/csail.mit.edu/u/j/jgross/coq-8.5,v8.5 (1b3759e78f227eb85a128c58b8ce8c11509dd8c3) *)
Axiom proof_admitted : False.
Tactic Notation "admit" := case proof_admitted.
Require Import Coq.Lists.SetoidList.
Require Export Coq.Program.Program.

Global Set Implicit Arguments.
Global Set Asymmetric Patterns.

Fixpoint combine_sig_helper {T} {P : T -> Prop} (ls : list T) : (forall x, In x ls -> P x) -> list (sig P).
  admit.
Defined.

Lemma Forall_forall1_transparent_helper_1 {A P} {x : A} {xs : list A} {l : list A}
      (H : Forall P l) (H' : x::xs = l)
: P x.
  admit.
Defined.
Lemma Forall_forall1_transparent_helper_2 {A P} {x : A} {xs : list A} {l : list A}
      (H : Forall P l) (H' : x::xs = l)
: Forall P xs.
  admit.
Defined.

Fixpoint Forall_forall1_transparent {A} (P : A -> Prop) (l : list A) {struct l}
: Forall P l -> forall x, In x l -> P x
  := match l as l return Forall P l -> forall x, In x l -> P x with
       | nil => fun _ _ f => match f : False with end
       | x::xs => fun H x' H' =>
                    match H' with
                      | or_introl H'' => eq_rect x
                                                 P
                                                 (Forall_forall1_transparent_helper_1 H eq_refl)
                                                 _
                                                 H''
                      | or_intror H'' => @Forall_forall1_transparent A P xs (Forall_forall1_transparent_helper_2 H eq_refl) _ H''
                    end
     end.

Definition combine_sig {T P ls} (H : List.Forall P ls) : list (@sig T P)
  := combine_sig_helper ls (@Forall_forall1_transparent T P ls H).
Fixpoint Forall_tails {T} (P : list T -> Type) (ls : list T) : Type
  := match ls with
       | nil => P nil
       | x::xs => (P (x::xs) * Forall_tails P xs)%type
     end.

Record string_like (CharType : Type) :=
  {
    String :> Type;
    Singleton : CharType -> String where "[ x ]" := (Singleton x);
    Empty : String;
    Concat : String -> String -> String where "x ++ y" := (Concat x y);
    bool_eq : String -> String -> bool;
    bool_eq_correct : forall x y : String, bool_eq x y = true <-> x = y;
    Length : String -> nat;
    Associativity : forall x y z, (x ++ y) ++ z = x ++ (y ++ z);
    LeftId : forall x, Empty ++ x = x;
    RightId : forall x, x ++ Empty = x;
    Singleton_Length : forall x, Length (Singleton x) = 1;
    Length_correct : forall s1 s2, Length s1 + Length s2 = Length (s1 ++ s2);
    Length_Empty : Length Empty = 0;
    Empty_Length : forall s1, Length s1 = 0 -> s1 = Empty;
    Not_Singleton_Empty : forall x, Singleton x <> Empty;
    SplitAt : nat -> String -> String * String;
    SplitAt_correct : forall n s, fst (SplitAt n s) ++ snd (SplitAt n s) = s;
    SplitAt_concat_correct : forall s1 s2, SplitAt (Length s1) (s1 ++ s2) = (s1, s2);
    SplitAtLength_correct : forall n s, Length (fst (SplitAt n s)) = min (Length s) n
  }.

Delimit Scope string_like_scope with string_like.
Bind Scope string_like_scope with String.
Arguments Length {_%type_scope _} _%string_like.
Notation "[[ x ]]" := (@Singleton _ _ x) : string_like_scope.
Infix "++" := (@Concat _ _) : string_like_scope.
Infix "=s" := (@bool_eq _ _) (at level 70, right associativity) : string_like_scope.

Definition str_le {CharType} {String : string_like CharType} (s1 s2 : String)
  := Length s1 < Length s2 \/ s1 = s2.
Infix "≤s" := str_le (at level 70, right associativity).

Record StringWithSplitState {CharType} (String : string_like CharType) (split_stateT : String -> Type) :=
  { string_val :> String;
    state_val : split_stateT string_val }.

Module Export ContextFreeGrammar.
  Require Import Coq.Strings.String.

  Section cfg.
    Variable CharType : Type.

    Section definitions.

      Inductive item :=
    | Terminal (_ : CharType)
    | NonTerminal (_ : string).

      Definition production := list item.
      Definition productions := list production.

      Record grammar :=
        {
          Start_symbol :> string;
          Lookup :> string -> productions;
          Start_productions :> productions := Lookup Start_symbol;
          Valid_nonterminals : list string;
          Valid_productions : list productions := map Lookup Valid_nonterminals
        }.
    End definitions.

  End cfg.

End ContextFreeGrammar.
Module Export BaseTypes.
  Import Coq.Strings.String.

  Local Open Scope string_like_scope.

  Inductive any_grammar CharType :=
  | include_item (_ : item CharType)
  | include_production (_ : production CharType)
  | include_productions (_ : productions CharType)
  | include_nonterminal (_ : string).
  Global Coercion include_item : item >-> any_grammar.
  Global Coercion include_production : production >-> any_grammar.

  Section recursive_descent_parser.
    Context {CharType : Type}
            {String : string_like CharType}
            {G : grammar CharType}.

    Class parser_computational_predataT :=
      { nonterminals_listT : Type;
        initial_nonterminals_data : nonterminals_listT;
        is_valid_nonterminal : nonterminals_listT -> string -> bool;
        remove_nonterminal : nonterminals_listT -> string -> nonterminals_listT;
        nonterminals_listT_R : nonterminals_listT -> nonterminals_listT -> Prop;
        remove_nonterminal_dec : forall ls nonterminal,
                                   is_valid_nonterminal ls nonterminal = true
                                   -> nonterminals_listT_R (remove_nonterminal ls nonterminal) ls;
        ntl_wf : well_founded nonterminals_listT_R }.

    Class parser_computational_types_dataT :=
      { predata :> parser_computational_predataT;
        split_stateT : String -> nonterminals_listT -> any_grammar CharType -> String -> Type }.

    Class parser_computational_dataT' `{parser_computational_types_dataT} :=
      { split_string_for_production
        : forall (str0 : String) (valid : nonterminals_listT) (it : item CharType) (its : production CharType) (str : StringWithSplitState String (split_stateT str0 valid (it::its : production CharType))),
            list (StringWithSplitState String (split_stateT str0 valid it)
                  * StringWithSplitState String (split_stateT str0 valid its));
        split_string_for_production_correct
        : forall str0 valid it its str,
            let P f := List.Forall f (@split_string_for_production str0 valid it its str) in
            P (fun s1s2 => (fst s1s2 ++ snd s1s2 =s str) = true) }.
  End recursive_descent_parser.

End BaseTypes.
Import Coq.Strings.String.

Section cfg.
  Context CharType (String : string_like CharType) (G : grammar CharType).
  Context (names_listT : Type)
          (initial_names_data : names_listT)
          (is_valid_name : names_listT -> string -> bool)
          (remove_name : names_listT -> string -> names_listT)
          (names_listT_R : names_listT -> names_listT -> Prop)
          (remove_name_dec : forall ls name,
                               is_valid_name ls name = true
                               -> names_listT_R (remove_name ls name) ls)
          (remove_name_1
           : forall ls ps ps',
               is_valid_name (remove_name ls ps) ps' = true
               -> is_valid_name ls ps' = true)
          (remove_name_2
           : forall ls ps ps',
               is_valid_name (remove_name ls ps) ps' = false
               <-> is_valid_name ls ps' = false \/ ps = ps')
          (ntl_wf : well_founded names_listT_R).

  Inductive minimal_parse_of
  : forall (str0 : String) (valid : names_listT)
           (str : String),
      productions CharType -> Type :=
  | MinParseHead : forall str0 valid str pat pats,
                     @minimal_parse_of_production str0 valid str pat
                     -> @minimal_parse_of str0 valid str (pat::pats)
  | MinParseTail : forall str0 valid str pat pats,
                     @minimal_parse_of str0 valid str pats
                     -> @minimal_parse_of str0 valid str (pat::pats)
  with minimal_parse_of_production
       : forall (str0 : String) (valid : names_listT)
                (str : String),
           production CharType -> Type :=
  | MinParseProductionNil : forall str0 valid,
                              @minimal_parse_of_production str0 valid (Empty _) nil
  | MinParseProductionCons : forall str0 valid str strs pat pats,
                               str ++ strs ≤s str0
                               -> @minimal_parse_of_item str0 valid str pat
                               -> @minimal_parse_of_production str0 valid strs pats
                               -> @minimal_parse_of_production str0 valid (str ++ strs) (pat::pats)
  with minimal_parse_of_item
       : forall (str0 : String) (valid : names_listT)
                (str : String),
           item CharType -> Type :=
  | MinParseTerminal : forall str0 valid x,
                         @minimal_parse_of_item str0 valid [[ x ]]%string_like (Terminal x)
  | MinParseNonTerminal
    : forall str0 valid str name,
        @minimal_parse_of_name str0 valid str name
        -> @minimal_parse_of_item str0 valid str (NonTerminal CharType name)
  with minimal_parse_of_name
       : forall (str0 : String) (valid : names_listT)
                (str : String),
           string -> Type :=
  | MinParseNonTerminalStrLt
    : forall str0 valid name str,
        Length str < Length str0
        -> is_valid_name initial_names_data name = true
        -> @minimal_parse_of str initial_names_data str (Lookup G name)
        -> @minimal_parse_of_name str0 valid str name
  | MinParseNonTerminalStrEq
    : forall str valid name,
        is_valid_name initial_names_data name = true
        -> is_valid_name valid name = true
        -> @minimal_parse_of str (remove_name valid name) str (Lookup G name)
        -> @minimal_parse_of_name str valid str name.
End cfg.

Local Coercion is_true : bool >-> Sortclass.

Local Open Scope string_like_scope.

Section general.
  Context {CharType} {String : string_like CharType} {G : grammar CharType}.

  Class boolean_parser_dataT :=
    { predata :> parser_computational_predataT;
      split_stateT : String -> Type;
      data' :> _ := {| BaseTypes.predata := predata ; BaseTypes.split_stateT := fun _ _ _ => split_stateT |};
      split_string_for_production
      : forall it its,
          StringWithSplitState String split_stateT
          -> list (StringWithSplitState String split_stateT * StringWithSplitState String split_stateT);
      split_string_for_production_correct
      : forall it its (str : StringWithSplitState String split_stateT),
          let P f := List.Forall f (split_string_for_production it its str) in
          P (fun s1s2 =>
               (fst s1s2 ++ snd s1s2 =s str) = true);
      premethods :> parser_computational_dataT'
      := @Build_parser_computational_dataT'
           _ String data'
           (fun _ _ => split_string_for_production)
           (fun _ _ => split_string_for_production_correct) }.

  Definition split_list_completeT `{data : boolean_parser_dataT}
             {str0 valid}
             (str : StringWithSplitState String split_stateT) (pf : str ≤s str0)
             (split_list : list (StringWithSplitState String split_stateT * StringWithSplitState String split_stateT))
             (it : item CharType) (its : production CharType)
    := ({ s1s2 : String * String
                 & (fst s1s2 ++ snd s1s2 =s str)
                   * (minimal_parse_of_item _ G initial_nonterminals_data is_valid_nonterminal remove_nonterminal str0 valid (fst s1s2) it)
                   * (minimal_parse_of_production _ G initial_nonterminals_data is_valid_nonterminal remove_nonterminal str0 valid (snd s1s2) its) }%type)
       -> ({ s1s2 : StringWithSplitState String split_stateT * StringWithSplitState String split_stateT
                    & (In s1s2 split_list)
                      * (minimal_parse_of_item _ G initial_nonterminals_data is_valid_nonterminal remove_nonterminal str0 valid (fst s1s2) it)
                      * (minimal_parse_of_production _ G initial_nonterminals_data is_valid_nonterminal remove_nonterminal str0 valid (snd s1s2) its) }%type).
End general.

Section recursive_descent_parser.
  Context {CharType}
          {String : string_like CharType}
          {G : grammar CharType}.
  Context `{data : @boolean_parser_dataT _ String}.

  Section bool.
    Section parts.
      Definition parse_item
                 (str_matches_nonterminal : string -> bool)
                 (str : StringWithSplitState String split_stateT)
                 (it : item CharType)
      : bool
        := match it with
             | Terminal ch => [[ ch ]] =s str
             | NonTerminal nt => str_matches_nonterminal nt
           end.

      Section production.
        Context {str0}
                (parse_nonterminal
                 : forall (str : StringWithSplitState String split_stateT),
                     str ≤s str0
                     -> string
                     -> bool).

        Fixpoint parse_production
                 (str : StringWithSplitState String split_stateT)
                 (pf : str ≤s str0)
                 (prod : production CharType)
        : bool.
        Proof.
          refine
            match prod with
              | nil =>

                str =s Empty _
              | it::its
                => let parse_production' := fun str pf => parse_production str pf its in
                   fold_right
                     orb
                     false
                     (let mapF f := map f (combine_sig (split_string_for_production_correct it its str)) in
                      mapF (fun s1s2p =>
                              (parse_item
                                 (parse_nonterminal (fst (proj1_sig s1s2p)) _)
                                 (fst (proj1_sig s1s2p))
                                 it)
                                && parse_production' (snd (proj1_sig s1s2p)) _)%bool)
            end;
          revert pf; clear; intros; admit.
        Defined.
      End production.

    End parts.
  End bool.
End recursive_descent_parser.

Section sound.
  Context CharType (String : string_like CharType) (G : grammar CharType).
  Context `{data : @boolean_parser_dataT CharType String}.

  Section production.
    Context (str0 : String)
            (parse_nonterminal : forall (str : StringWithSplitState String split_stateT),
                                   str ≤s str0
                                   -> string
                                   -> bool).

    Definition parse_nonterminal_completeT P
      := forall valid (str : StringWithSplitState String split_stateT) pf nonterminal (H_sub : P str0 valid nonterminal),
           minimal_parse_of_name _ G initial_nonterminals_data is_valid_nonterminal remove_nonterminal str0 valid str nonterminal
           -> @parse_nonterminal str pf nonterminal = true.

    Lemma parse_production_complete
          valid Pv
          (parse_nonterminal_complete : parse_nonterminal_completeT Pv)
          (Hinit : forall str (pf : str ≤s str0) nonterminal,
                     minimal_parse_of_name String G initial_nonterminals_data is_valid_nonterminal remove_nonterminal str0 valid str nonterminal
                     -> Pv str0 valid nonterminal)
          (str : StringWithSplitState String split_stateT) (pf : str ≤s str0)
          (prod : production CharType)
          (split_string_for_production_complete'
           : forall str0 valid str pf,
               Forall_tails
                 (fun prod' =>
                    match prod' return Type with
                      | nil => True
                      | it::its => split_list_completeT (G := G) (valid := valid) (str0 := str0) str pf (split_string_for_production it its str) it its
                    end)
                 prod)
    : minimal_parse_of_production _ G initial_nonterminals_data is_valid_nonterminal remove_nonterminal str0 valid str prod
      -> parse_production parse_nonterminal str pf prod = true.
      admit.
    Defined.
  End production.
  Context (str0 : String)
          (parse_nonterminal : forall (str : StringWithSplitState String split_stateT),
                                 str ≤s str0
                                 -> string
                                 -> bool).

  Goal forall (a : production CharType),
         (forall (str1 : String) (valid : nonterminals_listT)
                 (str : StringWithSplitState String split_stateT)
                 (pf : str ≤s str1),
            Forall_tails
              (fun prod' : list (item CharType) =>
                 match prod' with
                   | [] => True
                   | it :: its =>
                     split_list_completeT (G := G) (valid := valid) str pf
                                          (split_string_for_production it its str) it its
                 end) a) ->
         forall (str : String) (pf : str ≤s str0) (st : split_stateT str),
           parse_production parse_nonterminal
                            {| string_val := str; state_val := st |} pf a = true.
  Proof.
    intros a X **.
    eapply parse_production_complete.
    Focus 3.
    exact X.
    Undo.
    assumption.
    Undo.
    eassumption. (* no applicable tactic *)
