Module Type T.
  #[projections(primitive)]
  Record t := of_unit { to_unit : unit }.
End T.

Module M.
  Include T.
  Print to_unit.
  Definition foo x := to_unit x.
  Print foo.
End M.
