(* Syntax test - all possible kinds of module parameters *)

Module Type SIG.
End SIG.

Module Type FSIG (X: SIG).
End FSIG.

Module F (X: SIG).
End F.

Module Q.
End Q.

(*
#trace Nametab.push;;
#trace Nametab.push_short_name;;
#trace Nametab.freeze;;
#trace Nametab.unfreeze;;
#trace Nametab.exists_cci;;
*)

Module M01. End M01.
Module M02 (X: SIG). End M02.
Module M03 (X Y: SIG). End M03.
Module M04 (X: SIG) (Y: SIG). End M04.
Module M05 (X Y: SIG) (Z1 Z: SIG). End M05.
Module M06 (X: SIG) (Y: SIG). End M06.
Module M07 (X Y: SIG) (Z1 Z: SIG). End M07.
Module M08 : SIG. End M08.
Module M09 (X: SIG) : SIG. End M09.
Module M10 (X Y: SIG) : SIG. End M10.
Module M11 (X: SIG) (Y: SIG) : SIG. End M11.
Module M12 (X Y: SIG) (Z1 Z: SIG) : SIG. End M12.
Module M13 (X: SIG) (Y: SIG) : SIG. End M13.
Module M14 (X Y: SIG) (Z1 Z: SIG) : SIG. End M14.
Module M15 := F Q.
Module M16 (X: FSIG) := X Q.
Module M17 (X Y: FSIG) := X Q.
Module M18 (X: FSIG) (Y: SIG) := X Y.
Module M19 (X Y: FSIG) (Z1 Z: SIG) := X Z.
Module M20 (X: FSIG) (Y: SIG) := X Y.
Module M21 (X Y: FSIG) (Z1 Z: SIG) := X Z.
Module M22 : SIG := F Q.
Module M23 (X: FSIG) : SIG := X Q.
Module M24 (X Y: FSIG) : SIG := X Q.
Module M25 (X: FSIG) (Y: SIG) : SIG := X Y.
Module M26 (X Y: FSIG) (Z1 Z: SIG) : SIG := X Z.
Module M27 (X: FSIG) (Y: SIG) : SIG := X Y.
Module M28 (X Y: FSIG) (Z1 Z: SIG) : SIG := X Z.
