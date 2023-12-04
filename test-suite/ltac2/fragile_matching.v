(* test copied from ocaml's fragile_matching.ml test as of ocaml b02c7ca08 *)

Require Import Ltac2.Ltac2.

(* Tests for stack-overflow crashes caused by a combinatorial
   explosition in fragile pattern checking. *)

Module SyntheticTest.

  Ltac2 Type t := [ A | B ].

  Ltac2 f x :=
    match x with
    | A,A,A,A,A, A,A,A,A,A, A,A,A,A,A, A,A,A => 1
    | (A|B),(A|B),(A|B),(A|B),(A|B),
      (A|B),(A|B),(A|B),(A|B),(A|B),
      (A|B),(A|B),(A|B),(A|B),(A|B),
      (A|B),(A|B),(A|B) =>  2
    end.

End SyntheticTest.

Module RealCodeTest.
  (* from Alex Fedoseev *)

  Ltac2 Type ('a,'b) result := [ Ok ('a) | Err ('b) ].

  Ltac2 Type visibility := [Shown | Hidden].

  Ltac2 Type ('outputValue, 'message) fieldStatus :=
  [ Pristine
  | Dirty (('outputValue, 'message) result, visibility) ].

  Ltac2 Type message := string.

  Ltac2 Type rec fieldsStatuses := {
    iaasStorageConfigurations :
      iaasStorageConfigurationFieldsStatuses array;
  }

  with iaasStorageConfigurationFieldsStatuses := {
    startDate : (int, message) fieldStatus;
    term : (int, message) fieldStatus;
    rawStorageCapacity : (int, message) fieldStatus;
    diskType : (string option, message) fieldStatus;
    connectivityMethod : (string option, message) fieldStatus;
    getRequest : (int option, message) fieldStatus;
    getRequestUnit : (string option, message) fieldStatus;
    putRequest : (int option, message) fieldStatus;
    putRequestUnit : (string option, message) fieldStatus;
    transferOut : (int option, message) fieldStatus;
    transferOutUnit : (string option, message) fieldStatus;
    region : (string option, message) fieldStatus;
    cloudType : (string option, message) fieldStatus;
    description : (string option, message) fieldStatus;
    features : (string array, message) fieldStatus;
    accessTypes : (string array, message) fieldStatus;
    certifications : (string array, message) fieldStatus;
    additionalRequirements : (string option, message) fieldStatus;
  }.

  Ltac2 Type interface := { dirty : unit -> bool }.

  Ltac2 useForm () := {
    dirty := fun () =>
      Array.for_all
        (fun item =>
          match item with
          | {
              additionalRequirements := Pristine;
              certifications := Pristine;
              accessTypes := Pristine;
              features := Pristine;
              description := Pristine;
              cloudType := Pristine;
              region := Pristine;
              transferOutUnit := Pristine;
              transferOut := Pristine;
              putRequestUnit := Pristine;
              putRequest := Pristine;
              getRequestUnit := Pristine;
              getRequest := Pristine;
              connectivityMethod := Pristine;
              diskType := Pristine;
              rawStorageCapacity := Pristine;
              term := Pristine;
              startDate := Pristine;
            } =>
            false
          | {
              additionalRequirements := Pristine | Dirty _ _;
              certifications := Pristine | Dirty _ _;
              accessTypes := Pristine | Dirty _ _;
              features := Pristine | Dirty _ _;
              description := Pristine | Dirty _ _;
              cloudType := Pristine | Dirty _ _;
              region := Pristine | Dirty _ _;
              transferOutUnit := Pristine | Dirty _ _;
              transferOut := Pristine | Dirty _ _;
              putRequestUnit := Pristine | Dirty _ _;
              putRequest := Pristine | Dirty _ _;
              getRequestUnit := Pristine | Dirty _ _;
              getRequest := Pristine | Dirty _ _;
              connectivityMethod := Pristine | Dirty _ _;
              diskType := Pristine | Dirty _ _;
              rawStorageCapacity := Pristine | Dirty _ _;
              term := Pristine | Dirty _ _;
              startDate := Pristine | Dirty _ _;
            } =>
            true
          end)
        Array.empty
    }.

End RealCodeTest.
