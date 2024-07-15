Attributes deprecated(note="This library is useless.", since="XX YY").

(* unsupported attributes *)
Fail Attributes local.

Section Sec.
Fail Attributes deprecated(note="No library attributes in sections.").
End Sec.

Module Mod.
Fail Attributes deprecated(note="No library attributes in modules.").
End Mod.

Fail Attributes deprecated(note="This library is already deprecated.").
Attributes warn(note="This library is dangerous.", cats="dangerous library").
Attributes warn(note="This library is tricky.", cats="dangerous library, tricky library").
