Axiom X : forall {T:Type}, T.
Unset Printing Notations.

#[projections(primitive)]
Record bi : Type := Bi
  { bi_car :> Type;
    bi_sep : forall (_ : bi_car) (_ : bi_car), bi_car;
    bi_exist : forall (A : Type) (_ : forall _ : A, bi_car), bi_car; }.


Axiom genv : Set.
Existing Class genv.


Axiom biIndex : Set.
Existing Class biIndex.
Axiom monPred : biIndex -> bi -> Type.

Record seal (A : Type) (f : A) : Type := Build_seal { unseal : A;  seal_eq : unseal = f }.


Axiom monPred_exist_def :
forall (I : biIndex) (PROP : bi) (A : Type) (_ : forall _ : A, monPred I PROP),
monPred I PROP.

Axiom monPred_exist_aux
     : forall (I : biIndex) (PROP : bi), seal _ (@monPred_exist_def I PROP).

Definition monPred_exist
     : forall {I : biIndex} {PROP : bi} (A : Type) (_ : forall _ : A, monPred I PROP),
       monPred I PROP :=
fun (I : biIndex) (PROP : bi) => unseal _ _ (@monPred_exist_aux I PROP).

Axiom monPred_sep_def : forall  {I : biIndex} {PROP : bi}, (monPred I PROP) -> (monPred I PROP) -> monPred I PROP.
Axiom monPred_sep_aux :
forall  {I : biIndex} {PROP : bi}, seal _ (@monPred_sep_def I PROP).
Definition monPred_sep
  : forall  {I : biIndex} {PROP : bi}, (monPred I PROP) -> (monPred I PROP) -> monPred I PROP :=
  fun (I : biIndex) (PROP : bi) => unseal _ _ monPred_sep_aux.

Definition monPredI
     : biIndex -> bi -> bi
  :=
fun (I : biIndex) (PROP : bi) =>
  {|
    bi_car := monPred I PROP;
    bi_exist                  := monPred_exist;
    bi_sep                    := monPred_sep;
  |}.


Axiom gFunctors : Set.
Existing Class gFunctors.

Axiom iProp : bi.

Definition mpredI
     : forall (_ : biIndex) (_ : gFunctors), bi :=
fun (thread_info : biIndex) (Σ : gFunctors) => monPredI thread_info iProp
.

Arguments mpredI {thread_info Σ}.

Definition mpred
  : forall (_ : biIndex) (_ : gFunctors), Type :=
  fun (thread_info : biIndex) (Σ : gFunctors) => bi_car (@mpredI thread_info Σ).
Arguments mpred {thread_info Σ}.



Axiom Timeless : forall {X:Type} (x:X), Prop.
Axiom State : Set.
Axiom ec_kont_t : Set.
Axiom arch : Set.
Axiom ptr : Set.


Axiom cpp_logic : forall (_ : biIndex) (_ : gFunctors), Type.

Axiom GlobalCfg : Type.
Axiom GlobalGName : GlobalCfg -> Set.
Axiom GlobalG : forall  {ti : biIndex} {Σ : gFunctors}, cpp_logic ti Σ -> Set.
Axiom CpuGlobalG : forall  {ti : biIndex} {Σ : gFunctors}, cpp_logic ti Σ -> Set.


Axiom NovaAbsPred : forall  {thread_info : biIndex} {_Σ : gFunctors}, cpp_logic thread_info _Σ -> arch -> Type.

Axiom UserAbsPred : forall  {thread_info : biIndex} {_Σ : gFunctors}, cpp_logic thread_info _Σ -> genv -> Type.
Axiom G : forall  {ti : biIndex} {_Σ : gFunctors} (Σ : cpp_logic ti _Σ) {σ : genv}, GlobalCfg -> @UserAbsPred ti _Σ Σ σ -> Type.
Axiom GName : forall {_ : GlobalCfg} {thread_info : biIndex} {_Σ : gFunctors} {Σ : cpp_logic thread_info _Σ} {σ : genv} {_ : @UserAbsPred thread_info _Σ Σ σ}, Set.
Axiom ecInv :
forall  {H : GlobalCfg} {ti : biIndex} {_Σ : gFunctors} {Σ : cpp_logic ti _Σ} {σ : genv} {arch : arch},
  NovaAbsPred Σ arch -> forall  {H2 : @UserAbsPred ti _Σ Σ σ}, @GName H ti _Σ Σ σ H2 -> ec_kont_t -> bool -> @mpred ti _.

Axiom __at :
forall  {ti : biIndex} {Σ0 : gFunctors} {Σ : cpp_logic ti Σ0},
  ptr -> @mpredI ti _ -> @mpredI ti _.

Goal
  forall
    (Tr : forall PROP : bi, bi_car PROP)
    (H : GlobalCfg) (H0 : GlobalCfg) (ti : biIndex) (_Σ : gFunctors)
    (Σ : cpp_logic ti _Σ) (σ : genv) (arch : arch) (H1 : @NovaAbsPred ti _Σ Σ arch) (H2 : @UserAbsPred ti _Σ Σ σ)
    (H5 : GlobalGName H0) (H7 : @GlobalG ti _Σ Σ) (H8 : @CpuGlobalG ti _Σ Σ)
    (G0 : @G ti _Σ Σ σ H H2) (t3 : @GName H ti _Σ Σ σ H2) (nvs : ec_kont_t)
    (body : mpredI)
    (recall_bit : bool)
    (novastateinv : forall
                      (_ : GlobalGName H0) (_ : @GlobalG ti _Σ Σ)
                      (_ : @CpuGlobalG ti _Σ Σ) (_ : @G ti _Σ Σ σ H H2)
                      (_ : bool) (_ : bool) (_ : bool) (_ : State),
                    @mpred ti _Σ)
    (_ : forall (a1 : ptr) (a3 : bool),
         @Timeless (@mpredI ti _Σ)
           (@bi_sep (@mpredI ti _Σ) (@ecInv H ti _Σ Σ σ arch H1 H2 t3 nvs a3)
              (@bi_exist (@mpredI ti _Σ) State
                 (fun m : State =>
                  @bi_exist (@mpredI ti _Σ) bool
                    (fun about_to_ipc_reply : bool =>
                     @bi_exist (@mpredI ti _Σ) bool
                       (fun past_recall_in_roundup_impl : bool =>
                                (@bi_sep (@mpredI ti _Σ) (Tr (@mpredI ti _Σ))
                                   (@bi_sep (@mpredI ti _Σ) (Tr (@mpredI ti _Σ))
                                      (@bi_sep (@mpredI ti _Σ) (Tr (@mpredI ti _Σ))
                                         (@bi_sep (@mpredI ti _Σ) (Tr (@mpredI ti _Σ))
                                            (@bi_sep (@mpredI ti _Σ)
                                               (novastateinv H5 H7 H8 G0
                                                  about_to_ipc_reply a3 past_recall_in_roundup_impl m)
                                               (@__at ti _Σ Σ  a1
                                                  (Tr _))))))))))))),
  @Timeless (@mpredI ti _Σ)
    (@bi_sep (@mpredI ti _Σ) (@ecInv H ti _Σ Σ σ arch H1 H2 t3 nvs recall_bit)
       (@bi_exist (@mpredI ti _Σ) State
          (fun m : State =>
           @bi_exist (@mpredI ti _Σ) bool
             (fun about_to_ipc_reply : bool =>
              @bi_exist (@mpredI ti _Σ) bool
                (fun past_recall_in_roundup_impl : bool =>
                         (@bi_sep (@mpredI ti _Σ) (Tr (@mpredI ti _Σ))
                            (@bi_sep (@mpredI ti _Σ) (Tr (@mpredI ti _Σ))
                               (@bi_sep (@mpredI ti _Σ) (Tr (@mpredI ti _Σ))
                                  (@bi_sep (@mpredI ti _Σ) (Tr (@mpredI ti _Σ))
                                     (@bi_sep (@mpredI ti _Σ)
                                        (novastateinv H5 H7 H8 G0 about_to_ipc_reply
                                           recall_bit past_recall_in_roundup_impl m) body)))))))))).
Proof.
  intros *.
  intros T.
  Fail progress intros.
  Timeout 1 (
   (with_strategy opaque [bi_sep bi_exist] autoapply T with typeclass_instances)
   || idtac
  ).

  Strategy opaque [
    bi_sep
    bi_exist
  ].
  Timeout 1 (autoapply T with typeclass_instances || idtac).
Abort.
