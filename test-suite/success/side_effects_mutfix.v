(* -*- mode: coq; coq-prog-args: ("-emacs" "-q" "-w" "unsupported-attributes" "-w" "-deprecated-native-compiler-option" "-w" "-deprecated-appcontext -notation-overridden" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/fiat_parsers/src" "Fiat" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/fiat_parsers/Bedrock" "Bedrock" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-I" "/github/workspace/builds/coq/coq-failing/_build_ci/fiat_parsers/src/Common/Tactics" "-I" "/github/workspace/builds/coq/coq-failing/_build_ci/fiat_parsers" "-top" "Fiat.Parsers.WellFoundedParseProperties" "-require-import" "Coq.Compat.AdmitAxiom" "-native-compiler" "no") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 92 lines to 56 lines, then from 69 lines to 174 lines, then from 179 lines to 101 lines, then from 114 lines to 520 lines, then from 525 lines to 184 lines, then from 197 lines to 410 lines, then from 414 lines to 198 lines, then from 211 lines to 364 lines, then from 369 lines to 257 lines, then from 270 lines to 462 lines, then from 467 lines to 327 lines, then from 340 lines to 2160 lines, then from 2160 lines to 330 lines, then from 335 lines to 331 lines *)
(* coqc version 8.17+alpha compiled with OCaml 4.09.0
   coqtop version runner-j1aldqxs-project-6138686-concurrent-0:/builds/coq/coq/_build/default,(HEAD detached at 17ffb22) (17ffb2254c18f76ba9834ba17d2609c7b468010f)
   Expected coqc runtime on this file: 0.823 sec *)
   Require Coq.Lists.SetoidList.
   Require Coq.Numbers.Cyclic.Int31.Int31.

   Export Coq.Setoids.Setoid.

   Global Set Implicit Arguments.
   Global Set Asymmetric Patterns.

   Module Export Fiat_DOT_Parsers_DOT_StringLike_DOT_Core_WRAPPED.
   Module Export Core.
   Import Coq.Classes.Morphisms.

   Local Coercion is_true : bool >-> Sortclass.

   Module Export StringLike.
     Class StringLikeMin {Char : Type} :=
       {
         String :> Type;
         char_at_matches : nat -> String -> (Char -> bool) -> bool;
         unsafe_get : nat -> String -> Char;
         length : String -> nat
       }.

     Class StringLike {Char : Type} {HSLM : @StringLikeMin Char} :=
       {
         is_char : String -> Char -> bool;
         take : nat -> String -> String;
         drop : nat -> String -> String;
         get : nat -> String -> option Char;
         bool_eq : String -> String -> bool;
         beq : relation String := fun x y => bool_eq x y
       }.

     Arguments StringLikeMin : clear implicits.
     Arguments StringLike Char {HSLM}.
     Infix "=s" := (@beq _ _ _) (at level 70, no associativity) : type_scope.
     Notation "s ~= [ ch ]" := (is_char s ch) (at level 70, no associativity) : string_like_scope.
     Local Open Scope string_like_scope.

     Class StringLikeProperties (Char : Type) `{StringLike Char} :=
       {
         singleton_unique : forall s ch ch', s ~= [ ch ] -> s ~= [ ch' ] -> ch = ch';
         singleton_exists : forall s, length s = 1 -> exists ch, s ~= [ ch ];
         char_at_matches_correct : forall s n P ch, get n s = Some ch -> (char_at_matches n s P = P ch);
         get_0 : forall s ch, take 1 s ~= [ ch ] <-> get 0 s = Some ch;
         get_S : forall n s, get (S n) s = get n (drop 1 s);
         unsafe_get_correct : forall n s ch, get n s = Some ch -> unsafe_get n s = ch;
         length_singleton : forall s ch, s ~= [ ch ] -> length s = 1;
         bool_eq_char : forall s s' ch, s ~= [ ch ] -> s' ~= [ ch ] -> s =s s';
         is_char_Proper :> Proper (beq ==> eq ==> eq) is_char;
         length_Proper :> Proper (beq ==> eq) length;
         take_Proper :> Proper (eq ==> beq ==> beq) take;
         drop_Proper :> Proper (eq ==> beq ==> beq) drop;
         bool_eq_Equivalence :> Equivalence beq;
         bool_eq_empty : forall str str', length str = 0 -> length str' = 0 -> str =s str';
         take_short_length : forall str n, n <= length str -> length (take n str) = n;
         take_long : forall str n, length str <= n -> take n str =s str;
         take_take : forall str n m, take n (take m str) =s take (min n m) str;
         drop_length : forall str n, length (drop n str) = length str - n;
         drop_0 : forall str, drop 0 str =s str;
         drop_drop : forall str n m, drop n (drop m str) =s drop (n + m) str;
         drop_take : forall str n m, drop n (take m str) =s take (m - n) (drop n str);
         take_drop : forall str n m, take n (drop m str) =s drop m (take (n + m) str);
         bool_eq_from_get : forall str str', (forall n, get n str = get n str') -> str =s str';
         strings_nontrivial : forall n, exists str, length str = n
       }.

     Arguments StringLikeProperties Char {_ _}.
   End StringLike.

   End Core.
   Module Export Fiat.
   Module Export Parsers.
   Module Export StringLike.
   Module Export Core.
   Include Fiat_DOT_Parsers_DOT_StringLike_DOT_Core_WRAPPED.Core.
   End Core.
   Import Coq.Strings.String.
   Import Coq.Lists.List.
   Export Fiat.Parsers.StringLike.Core.

   Local Open Scope string_like_scope.

   Section cfg.
     Context {Char : Type}.

     Section definitions.

       Inductive item :=
       | Terminal (_ : Char -> bool)
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

     Section parse.
       Context {HSLM} {HSL : @StringLike Char HSLM}.
       Variable G : grammar.

       Inductive parse_of (str : String) : productions -> Type :=
       | ParseHead : forall pat pats, parse_of_production str pat
                                      -> parse_of str (pat::pats)
       | ParseTail : forall pat pats, parse_of str pats
                                      -> parse_of str (pat::pats)
       with parse_of_production (str : String) : production -> Type :=
       | ParseProductionNil : length str = 0 -> parse_of_production str nil
       | ParseProductionCons : forall n pat pats,
                                 parse_of_item (take n str) pat
                                 -> parse_of_production (drop n str) pats
                                 -> parse_of_production str (pat::pats)
       with parse_of_item (str : String) : item -> Type :=
       | ParseTerminal : forall ch P, is_true (P ch) -> is_true (str ~= [ ch ]) -> parse_of_item str (Terminal P)
       | ParseNonTerminal : forall nt,
                              List.In nt (Valid_nonterminals G)
                              -> parse_of str (Lookup G nt)
                              -> parse_of_item str (NonTerminal nt).
     End parse.
   End cfg.

   Arguments item _ : clear implicits.
   Arguments production _ : clear implicits.
   Arguments productions _ : clear implicits.
   Arguments grammar _ : clear implicits.
   Definition item_code {Char} (x y : item Char) : Prop.
   exact (match x, y with
          | Terminal P, Terminal Q => forall x, P x = Q x
          | Terminal _, _ => False
          | NonTerminal nt, NonTerminal nt' => nt = nt'
          | NonTerminal _, _ => False
        end).
   Defined.

   Global Instance item_code_Equivalence {Char} : Equivalence (@item_code Char).
   Admitted.
   Definition production_code {Char} : relation (production Char).
   exact (SetoidList.eqlistA item_code).
   Defined.
   Definition productions_code {Char} : relation (productions Char).
   exact (SetoidList.eqlistA production_code).
   Defined.

   Section cfg.
     Context {Char} {HSLM : StringLikeMin Char} {HSL : StringLike Char} {HSLP : StringLikeProperties Char} (G : grammar Char).
   Definition parse_of_item_respectful'
                (parse_of_respectful : forall {str1 str2} (H : str1 =s str2) {pats pats'} (Hpats : productions_code pats pats') (p : parse_of G str1 pats), parse_of G str2 pats')
                {str1 str2} (H : str1 =s str2) {it it'} (Hit : item_code it it') (p : parse_of_item G str1 it)
     : parse_of_item G str2 it'.
   exact (match p in (parse_of_item _ _ it), it' return item_code it it' -> parse_of_item G str2 it' with
            | ParseTerminal ch P pf0 pf1, Terminal P' => fun Hit => ParseTerminal G str2 ch P' (transitivity (symmetry (Hit _)) pf0) (transitivity (eq_sym (is_char_Proper H eq_refl)) pf1)
            | ParseTerminal _ _ _ _, NonTerminal _ => fun Hit => match Hit with end
            | ParseNonTerminal nt H' p', NonTerminal nt'
              => fun Hit
                 => ParseNonTerminal
                      _
                      (match Hit in (_ = nt') return List.In nt' _ with
                         | eq_refl => H'
                       end)
                      (@parse_of_respectful
                         _ _ H (Lookup G nt) (Lookup G nt')
                         (match Hit in (_ = nt') return productions_code (G nt) (G nt') with
                            | eq_refl => reflexivity _
                          end)
                         p')
            | ParseNonTerminal _ _ _, Terminal _ => fun Hit => match Hit with end
          end Hit).
   Defined.

     Section bodies.
       Context (parse_of_respectful : forall {str1 str2} (H : str1 =s str2) {pats pats'} (Hpats : productions_code pats pats') (p : parse_of G str1 pats), parse_of G str2 pats')
               (parse_of_production_respectful : forall {str1 str2} (H : str1 =s str2) {pat pat'} (Hpat : production_code pat pat') (p : parse_of_production G str1 pat), parse_of_production G str2 pat').

       Definition parse_of_respectful_step {str1 str2} (H : str1 =s str2) {pats pats'} (Hpats : productions_code pats pats') (p : parse_of G str1 pats) : parse_of G str2 pats'.
       Proof.
         refine (match p in (parse_of _ _ pats), pats' return productions_code pats pats' -> parse_of G str2 pats' with
                   | ParseHead pat pats p', pat'::pats' => fun Hpats' => ParseHead pats' (@parse_of_production_respectful _ _ H _ _ _ p')
                   | ParseTail pat pats p', pat'::pats' => fun Hpats' => ParseTail pat' (@parse_of_respectful _ _ H _ _ _ p')
                   | ParseHead _ _ _, nil => fun Hpats' => match _ : False with end
                   | ParseTail _ _ _, nil => fun Hpats' => match _ : False with end
                 end Hpats);
         try solve [ clear -Hpats'; abstract inversion Hpats'
                   | clear -Hpats'; inversion Hpats'; subst; assumption ].
       Defined.

       Definition parse_of_production_respectful_step {str1 str2} (H : str1 =s str2) {pat pat'} (Hpat : production_code pat pat') (p : parse_of_production G str1 pat) : parse_of_production G str2 pat'.
       Proof.
         refine (match p in (parse_of_production _ _ pat), pat' return production_code pat pat' -> parse_of_production G str2 pat' with
                   | ParseProductionNil pf, nil => fun Hpat' => ParseProductionNil G str2 (transitivity (eq_sym (length_Proper H)) pf)
                   | ParseProductionCons n pat pats p0 p1, pat'::pats' => fun Hpat' => ParseProductionCons _ n (parse_of_item_respectful' (@parse_of_respectful) (take_Proper eq_refl H) _ p0) (@parse_of_production_respectful _ _ (drop_Proper eq_refl H) _ _ _ p1)
                   | ParseProductionNil _, _::_ => fun Hpat' => match _ : False with end
                   | ParseProductionCons _ _ _ _ _, nil => fun Hpat' => match _ : False with end
                 end Hpat);
         try solve [ clear -Hpat'; abstract inversion Hpat'
                   | clear -Hpat'; inversion Hpat'; subst; assumption ].
       Defined.
     End bodies.

     Fixpoint parse_of_respectful {str1 str2} (H : str1 =s str2) {pats pats'} (Hpats : productions_code pats pats') (p : parse_of G str1 pats) : parse_of G str2 pats'
       := @parse_of_respectful_step (@parse_of_respectful) (@parse_of_production_respectful) _ _ H _ _ Hpats p
     with parse_of_production_respectful {str1 str2} (H : str1 =s str2) {pat pat'} (Hpat : production_code pat pat') (p : parse_of_production G str1 pat) : parse_of_production G str2 pat'
       := @parse_of_production_respectful_step (@parse_of_respectful) (@parse_of_production_respectful) _ _ H _ _ Hpat p.

     Definition parse_of_item_respectful : forall {str1 str2} H {it it'} Hit p, _
       := @parse_of_item_respectful' (@parse_of_respectful).

     End cfg.

   Ltac simpl_parse_of_respectful :=
     repeat match goal with
              | [ |- context[@parse_of_respectful ?Char ?HSLM ?HSL ?HSLP ?G ?str1 ?str2 ?H ?pat ?pat' ?Hpat ?p] ]
                => change (@parse_of_respectful Char HSLM HSL HSLP G str1 str2 H pat pat' Hpat p)
                   with (@parse_of_respectful_step Char HSLM HSL G (@parse_of_respectful Char HSLM HSL HSLP G) (@parse_of_production_respectful Char HSLM HSL HSLP G) str1 str2 H pat pat' Hpat p);
                  simpl @parse_of_respectful_step
              | [ |- context[@parse_of_production_respectful ?Char ?HSLM ?HSL ?HSLP ?G ?str1 ?str2 ?H ?pat ?pat' ?Hpat ?p] ]
                => change (@parse_of_production_respectful Char HSLM HSL HSLP G str1 str2 H pat pat' Hpat p)
                   with (@parse_of_production_respectful_step Char HSLM HSL G (@parse_of_respectful Char HSLM HSL HSLP G) (@parse_of_production_respectful Char HSLM HSL HSLP G) str1 str2 H pat pat' Hpat p);
                  simpl @parse_of_production_respectful_step
              | _ => progress simpl @parse_of_item_respectful
              | _ => progress simpl @parse_of_item_respectful'
            end.

   Section rel.
     Context {Char} {HSLM : StringLikeMin Char} {HSL : StringLike Char} {G : grammar Char}.

     Section size.
       Definition size_of_parse_item'
                  (size_of_parse : forall {str pats} (p : parse_of G str pats), nat)
                  {str it} (p : parse_of_item G str it) : nat
         := match p with
              | ParseTerminal _ _ _ _ => 0
              | ParseNonTerminal _ _ p' => S (size_of_parse p')
            end.

       Section bodies.
         Context (size_of_parse : forall {str pats} (p : parse_of G str pats), nat)
                 (size_of_parse_production : forall {str pat} (p : parse_of_production G str pat), nat).
   Definition size_of_parse_step {str pats} (p : parse_of G str pats) : nat.
   exact (match p with
                | ParseHead _ _ p' => S (@size_of_parse_production _ _ p')
                | ParseTail _ _ p' => S (@size_of_parse _ _ p')
              end).
   Defined.
   Definition size_of_parse_production_step {str pat} (p : parse_of_production G str pat) : nat.
   exact (match p with
                | ParseProductionNil _ => 0
                | ParseProductionCons _ _ _ p' p''
                  => S (size_of_parse_item' (@size_of_parse) p' + @size_of_parse_production _ _ p'')
              end).
   Defined.
       End bodies.

       Fixpoint size_of_parse {str pats} (p : parse_of G str pats) : nat
         := @size_of_parse_step (@size_of_parse) (@size_of_parse_production) str pats p
       with size_of_parse_production {str pat} (p : parse_of_production G str pat) : nat
            := @size_of_parse_production_step (@size_of_parse) (@size_of_parse_production) str pat p.
   Definition size_of_parse_item
                  {str it} (p : parse_of_item G str it) : nat.
   exact (@size_of_parse_item' (@size_of_parse) str it p).
   Defined.
     End size.
   End rel.

   Ltac simpl_size_of_parse :=
     repeat match goal with
              | [ |- context[@size_of_parse ?Char ?HSLM ?HSL ?G ?str ?pat ?p] ]
                => change (@size_of_parse Char HSLM HSL G str pat p)
                   with (@size_of_parse_step Char HSLM HSL G (@size_of_parse Char HSLM HSL G) (@size_of_parse_production Char HSLM HSL G) str pat p);
                  simpl @size_of_parse_step
              | [ |- context[@size_of_parse_production ?Char ?HSLM ?HSL ?G ?str ?pat ?p] ]
                => change (@size_of_parse_production Char HSLM HSL G str pat p)
                   with (@size_of_parse_production_step Char HSLM HSL G (@size_of_parse Char HSLM HSL G) (@size_of_parse_production Char HSLM HSL G) str pat p);
                  simpl @size_of_parse_production_step
            end.
     Context {Char} {HSLM : StringLikeMin Char} {HSL : StringLike Char} {HSLP : StringLikeProperties Char} {G : grammar Char}.

     Fixpoint size_of_parse_respectful {str str' pats pats'} (Hpats : productions_code pats pats') (H : str =s str') (p : parse_of G str pats)
     : size_of_parse p = size_of_parse (parse_of_respectful H Hpats p)
     with size_of_parse_production_respectful {str str' pat pat'} (Hpat : production_code pat pat') (H : str =s str') (p : parse_of_production G str pat)
          : size_of_parse_production p = size_of_parse_production (parse_of_production_respectful H Hpat p)
     with size_of_parse_item_respectful {str str' it it'} (Hit : item_code it it') (H : str =s str') (p : parse_of_item G str it)
          : size_of_parse_item p = size_of_parse_item (parse_of_item_respectful H Hit p).
     Proof.
       {
    refine (match p, pats' return forall Hpats : productions_code _ pats', size_of_parse p = size_of_parse (parse_of_respectful H Hpats p) with
                   | ParseHead _ _ p', _::_ => fun Hpats' => _
                   | ParseTail _ _ p', _::_ => fun Hpats' => _
                   | _, nil => fun Hpats' => match _ : False with end
                 end Hpats);
         try solve [ simpl in *; clear -Hpats'; abstract inversion Hpats' ];
         simpl_parse_of_respectful;
         simpl_size_of_parse;
         apply (f_equal S).
         {
    apply size_of_parse_production_respectful.
   }
         {
    apply size_of_parse_respectful.
   }
    }
       {
    refine (match p, pat' return forall Hpat : production_code _ pat', size_of_parse_production p = size_of_parse_production (parse_of_production_respectful H Hpat p) with
                   | ParseProductionNil _, nil => fun Hpat' => eq_refl
                   | ParseProductionCons _ _ _ _ _, _::_
                     => fun Hpat'
                        => f_equal2 (fun x y => S (x + y))
                                    (@size_of_parse_item_respectful _ _ _ _ _ _ _)
                                    (@size_of_parse_production_respectful _ _ _ _ _ _ _)
                   | _, _ => fun Hpat' => match _ : False with end
                 end Hpat);
         try solve [ simpl in *; clear -Hpat'; abstract inversion Hpat' ].
   }
       {
    refine (match p, it' return forall Hit : item_code _ it', size_of_parse_item p = size_of_parse_item (parse_of_item_respectful H Hit p)  with
                   | ParseTerminal _ _ _ _, Terminal _ => fun Hit' => eq_refl
                   | ParseNonTerminal _ H' p', NonTerminal _ => fun Hit' => f_equal S (@size_of_parse_respectful _ _ _ _ _ H p')
                   | _, _ => fun Hit' => match _ : False with end
                 end Hit);
         try solve [ simpl in *; clear -Hit'; abstract inversion Hit' ].
   }
   Defined.
End StringLike.
End Parsers.
End Fiat.
End Fiat_DOT_Parsers_DOT_StringLike_DOT_Core_WRAPPED.
