(** Test hint command locality w.r.t. modules *)

Create HintDb foodb.
Create HintDb bardb.
Create HintDb quxdb.

#[global] Hint Immediate O : foodb.
#[global] Hint Immediate O : bardb.
#[global] Hint Immediate O : quxdb.

Module Test.

#[global] Hint Cut [ _ ] : foodb.
#[global] Hint Mode S ! : foodb.
#[global] Hint Opaque id : foodb.
#[global] Remove Hints O : foodb.

#[local] Hint Cut [ _ ] : bardb.
#[local] Hint Mode S ! : bardb.
#[local] Hint Opaque id : bardb.
#[local] Remove Hints O : bardb.

#[export] Hint Cut [ _ ] : quxdb.
#[export] Hint Mode S ! : quxdb.
#[export] Hint Opaque id : quxdb.
#[export] Remove Hints O : quxdb.

(** All three agree here *)

Print HintDb foodb.
Print HintDb bardb.
Print HintDb quxdb.

End Test.

(** bardb and quxdb agree here *)

Print HintDb foodb.
Print HintDb bardb.
Print HintDb quxdb.

Import Test.

(** foodb and quxdb agree here *)

Print HintDb foodb.
Print HintDb bardb.
Print HintDb quxdb.

(** Test hint command locality w.r.t. sections *)

Create HintDb secdb.

#[global] Hint Immediate O : secdb.

Section Sec.

#[global] Hint Cut [ _ ] : secdb.
#[global] Hint Mode S ! : secdb.
#[global] Hint Opaque id : secdb.
Fail #[global] Remove Hints O : secdb.

#[local] Hint Cut [ _ ] : secdb.
#[local] Hint Mode S ! : secdb.
#[local] Hint Opaque id : secdb.
#[local] Remove Hints O : secdb.

Print HintDb secdb.

End Sec.

Print HintDb secdb.

(** Variant of the above test
    - modes are correctly generalized at section closure
    - non-local section-specific hints trigger a warning
*)

Create HintDb seclocaldb.

Set Warnings "non-local-section-hint".

Section SecLocal.

Variable A : Type.

Definition refl (n : A) : n = n := eq_refl.

Variable prf : forall n : nat, n = 0.

#[export] Hint Mode refl ! : seclocaldb.
#[export] Hint Mode prf ! : seclocaldb.

#[export] Hint Cut [ prf ] : seclocaldb.

#[export] Hint Variables Transparent : seclocaldb.
#[export] Hint Constants Transparent : seclocaldb.
#[export] Hint Opaque prf : seclocaldb.

End SecLocal.

Print HintDb seclocaldb.
