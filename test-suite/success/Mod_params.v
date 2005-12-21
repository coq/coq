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

Module M.
Reset M.
Module M (X: SIG).
Reset M.
Module M (X Y: SIG).
Reset M.
Module M (X: SIG) (Y: SIG).
Reset M.
Module M (X Y: SIG) (Z1 Z: SIG).
Reset M.
Module M (X: SIG) (Y: SIG).
Reset M.
Module M (X Y: SIG) (Z1 Z: SIG).
Reset M.
Module M : SIG.
Reset M.
Module M (X: SIG) : SIG.
Reset M.
Module M (X Y: SIG) : SIG.
Reset M.
Module M (X: SIG) (Y: SIG) : SIG.
Reset M.
Module M (X Y: SIG) (Z1 Z: SIG) : SIG.
Reset M.
Module M (X: SIG) (Y: SIG) : SIG.
Reset M.
Module M (X Y: SIG) (Z1 Z: SIG) : SIG.
Reset M.
Module M := F Q.
Reset M.
Module M (X: FSIG) := X Q.
Reset M.
Module M (X Y: FSIG) := X Q.
Reset M.
Module M (X: FSIG) (Y: SIG) := X Y.
Reset M.
Module M (X Y: FSIG) (Z1 Z: SIG) := X Z.
Reset M.
Module M (X: FSIG) (Y: SIG) := X Y.
Reset M.
Module M (X Y: FSIG) (Z1 Z: SIG) := X Z.
Reset M.
Module M : SIG := F Q.
Reset M.
Module M (X: FSIG) : SIG := X Q.
Reset M.
Module M (X Y: FSIG) : SIG := X Q.
Reset M.
Module M (X: FSIG) (Y: SIG) : SIG := X Y.
Reset M.
Module M (X Y: FSIG) (Z1 Z: SIG) : SIG := X Z.
Reset M.
Module M (X: FSIG) (Y: SIG) : SIG := X Y.
Reset M.
Module M (X Y: FSIG) (Z1 Z: SIG) : SIG := X Z.
Reset M.
