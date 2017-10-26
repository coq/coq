Require Export Setoid.

(* Testare:
   +1. due setoidi con ugualianza diversa sullo stesso tipo
   +2. due setoidi sulla stessa uguaglianza
   +3. due morfismi sulla stessa funzione ma setoidi diversi
   +4. due morfismi sulla stessa funzione e stessi setoidi
   +5. setoid_replace
   +6. solo cammini mal tipati
   +7. esempio (f (g (h E1)))
       dove h:(T1,=1) -> T2, g:T2->(T3,=3), f:(T3,=3)->Prop
   +8. test con occorrenze non lineari del pattern
   +9. test in cui setoid_replace fa direttamente fallback su replace
   10. sezioni
  +11. goal con impl
  +12. testare *veramente* setoid_replace (ora testato solamente il caso
       di fallback su replace)

  Incompatibilita':
    1. full_trivial in setoid_replace
    2. "as ..." per "Add Setoid"
    3. ipotesi permutate in lemma di "Add Morphism"
    4. iff invece di if in "Add Morphism" nel caso di predicati
    5. setoid_replace poteva riscrivere sia c1 in c2 che c2 in c1
       (???? o poteva farlo da destra a sinitra o viceversa? ????)

### Come evitare di dover fare "Require Setoid" prima di usare la
    tattica?

??? scelta: quando ci sono piu' scelte dare un warning oppure fallire?
    difficile quando la tattica e' rewrite ed e' usata in tattiche
    automatiche

??? in test4.v il setoid_rewrite non si puo' sostituire con rewrite
    perche' questo ultimo fallisce per via dell'unificazione

??? ??? <-> non e' sottorelazione di ->. Quindi ora puo' capitare
    di non riuscire a provare goal del tipo A /\ B dove (A, <->) e
    (B, ->) (per esempio)

### Nota: il parsing e pretty printing delle relazioni non e' in synch!
    eq contro (ty,eq). Uniformare

### diminuire la taglia dei proof term

??? il messaggio di errore non e' assolutamente significativo quando
    nessuna marcatura viene trovata

### fare in modo che uscendo da una sezione vengano quantificate le
    relazioni e i morfismi. Hugo: paciugare nel discharge.ml

### implementare relazioni/morfismi quantificati con dei LetIn (che palle...)
    decompose_prod da far diventare simile a un Reduction.dest_arity?
    (ma senza riduzione??? e perche' li' c'e' riduzione?)
    Soluzione da struzzo: fare zeta-conversione.

### fare in modo che impl sia espanso nel lemma di compatibilita' del
    morfismo (richiesta di Marco per poter fare Add Hing)

??? snellire la sintassi omettendo "proved by" come proposto da Marco?  ;-(

### non capisce piu' le riscritture con uguaglianze quantificate (almeno
    nell'esempio di Marco)
### Bas Spitters: poter dichiarare che ogni variabile nel contesto di tipo
    un setoid_function e' un morfismo

### unificare le varie check_...
### sostituire a Use_* una sola eccezione Optimize

  Implementare:
   -2. user-defined subrelations && user-proved subrelations
   -1. trucco di Bruno

  Sorgenti di inefficacia:
    1. scelta del setoide di default per un sostegno: per farlo velocemente
       ci vorrebbe una tabella hash; attualmente viene fatta una ricerca
       lineare sul range della setoid_table

  Vantaggi rispetto alla vecchia tattica:
    1. permette di avere setoidi differenti con lo stesso sostegno,
       ma equivalenza differente
    2. accetta setoidi differenti con lo stesso sostegno e stessa
       equivalenza, scegliendo a caso quello da usare (proof irrelevance)
    3. permette di avere morfismi differenti sulla stessa funzione
       se hanno dominio o codominio differenti
    4. accetta di avere morfismi differenti sulla stessa funzione e con
       lo stesso dominio e codominio, scegliendo a caso quello da usare
       (proof irrelevance)
    5. quando un morfismo viene definito, se la scelta del dominio o del
       codominio e' ambigua l'utente puo' esplicitamente disambiguare
       la scelta fornendo esplicitamente il "tipo" del morfismo
    6. permette di gestire riscritture ove ad almeno una funzione venga
       associato piu' di un morfismo. Vengono automaticamente calcolate
       le scelte globali che rispettano il tipaggio.
    7. se esistono piu' scelte globali che rispettano le regole di tipaggio
       l'utente puo' esplicitamente disambiguare la scelta globale fornendo
       esplicitamente la scelta delle side conditions generate.
    8. nel caso in cui la setoid_replace sia stata invocata al posto
       della replace la setoid_replace invoca direttamente la replace.
       Stessa cosa per la setoid_rewrite.
    9. permette di gestire termini in cui il prefisso iniziale dell'albero
       (fino a trovare il termine da riscrivere) non sia formato esclusivamente
       da morfismi il cui dominio e codominio sia un setoide.
       Ovvero ammette anche morfismi il cui dominio e/o codominio sia
       l'uguaglianza di Leibniz. (Se entrambi sono uguaglianze di Leibniz
       allora il setoide e' una semplice funzione).
   10. [setoid_]rewrite ... in ...
       setoid_replace ... in ...
       [setoid_]reflexivity
       [setoid_]transitivity ...
       [setoid_]symmetry
       [setoid_]symmetry in ...
   11. permette di dichiarare dei setoidi/relazioni/morfismi in un module
       type
   12. relazioni, morfismi e setoidi quantificati
*)

Axiom S1: Set.
Axiom eqS1: S1 -> S1 -> Prop.
Axiom SetoidS1 : Setoid_Theory S1 eqS1.
Add Setoid S1 eqS1 SetoidS1 as S1setoid.

Instance eqS1_default : DefaultRelation eqS1.

Axiom eqS1': S1 -> S1 -> Prop.
Axiom SetoidS1' : Setoid_Theory S1 eqS1'.
Axiom SetoidS1'_bis : Setoid_Theory S1 eqS1'.
Add Setoid S1 eqS1' SetoidS1' as S1setoid'.
Add Setoid S1 eqS1' SetoidS1'_bis as S1setoid''.

Axiom S2: Set.
Axiom eqS2: S2 -> S2 -> Prop.
Axiom SetoidS2 : Setoid_Theory S2 eqS2.
Add Setoid S2 eqS2 SetoidS2 as S2setoid.

Axiom f : S1 -> nat -> S2.
Add Morphism f with signature (eqS1 ==> eq ==> eqS2) as f_compat. Admitted.
Add Morphism f with signature (eqS1 ==> eq ==> eqS2) as f_compat2. Admitted.

Theorem test1: forall x y, (eqS1 x y) -> (eqS2 (f x 0) (f y 0)).
 intros.
 rewrite H.
 reflexivity.
Qed.

Theorem test1': forall x y, (eqS1 x y) -> (eqS2 (f x 0) (f y 0)).
 intros.
 setoid_replace x with y.
 reflexivity.
 assumption.
Qed.

Axiom g : S1 -> S2 -> nat.
Add Morphism g with signature (eqS1 ==> eqS2 ==> eq) as g_compat. Admitted.

Axiom P : nat -> Prop.
Theorem test2:
 forall x x' y y', (eqS1 x x') -> (eqS2 y y') -> (P (g x' y')) -> (P (g x y)).
 intros.
 rewrite H.
 rewrite H0.
 assumption.
Qed.

Theorem test3:
 forall x x' y y',
  (eqS1 x x') -> (eqS2 y y') -> (P (S (g x' y'))) -> (P (S (g x y))).
 intros.
 rewrite H.
 rewrite H0.
 assumption.
Qed.

Theorem test4:
 forall x x' y y', (eqS1 x x') -> (eqS2 y y') -> (S (g x y)) = (S (g x' y')).
 intros.
 rewrite H.
 rewrite H0.
 reflexivity.
Qed.

Theorem test5:
 forall x x' y y', (eqS1 x x') -> (eqS2 y y') -> (S (g x y)) = (S (g x' y')).
 intros.
 setoid_replace (g x y) with (g x' y').
 reflexivity.
 rewrite <- H0.
 rewrite H.
 reflexivity.
Qed.

Axiom f_test6 : S2 -> Prop.
Add Morphism f_test6 with signature (eqS2 ==> iff) as f_test6_compat. Admitted.

Axiom g_test6 : bool -> S2.
Add Morphism g_test6 with signature (eq ==> eqS2) as g_test6_compat. Admitted.

Axiom h_test6 : S1 -> bool.
Add Morphism h_test6 with signature (eqS1 ==> eq) as h_test6_compat. Admitted.

Theorem test6:
 forall E1 E2, (eqS1 E1 E2) -> (f_test6 (g_test6 (h_test6 E2))) ->
  (f_test6 (g_test6 (h_test6 E1))).
 intros.
 rewrite  H.
 assumption.
Qed.

Theorem test7:
 forall E1 E2 y y', (eqS1 E1 E2) -> (eqS2 y y') ->
  (f_test6 (g_test6 (h_test6 E2))) ->
   (f_test6 (g_test6 (h_test6 E1))) /\ (S (g E1 y')) = (S (g E2 y')).
  intros.
  rewrite H.
  split; [assumption | reflexivity].
Qed.

Axiom S1_test8: Set.
Axiom eqS1_test8: S1_test8 -> S1_test8 -> Prop.
Axiom SetoidS1_test8 : Setoid_Theory S1_test8 eqS1_test8.
Add Setoid S1_test8 eqS1_test8 SetoidS1_test8 as S1_test8setoid.

Instance eqS1_test8_default : DefaultRelation eqS1_test8.

Axiom f_test8 : S2 -> S1_test8.
Add Morphism f_test8 with signature (eqS2 ==> eqS1_test8) as f_compat_test8. Admitted.

Axiom eqS1_test8': S1_test8 -> S1_test8 -> Prop.
Axiom SetoidS1_test8' : Setoid_Theory S1_test8 eqS1_test8'.
Add Setoid S1_test8 eqS1_test8' SetoidS1_test8' as S1_test8setoid'.

(*CSC: for test8 to be significant I want to choose the setoid
  (S1_test8, eqS1_test8'). However this does not happen and
  there is still no syntax for it ;-( *)
Axiom g_test8 : S1_test8 -> S2.
Add Morphism g_test8 with signature (eqS1_test8 ==> eqS2) as g_compat_test8. Admitted.

Theorem test8:
 forall x x': S2, (eqS2 x x') ->
  (eqS2 (g_test8 (f_test8 x)) (g_test8 (f_test8 x'))).
  intros.
  rewrite H.
Abort.

(*Print Setoids.*)

