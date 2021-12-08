Require Extraction.

Inductive t (sig: list nat) :=
| T (k: nat).

Record pkg :=
  { _sig: list nat;
    _t : t _sig }.

Definition map (f: nat -> nat) (p: pkg) :=
  {| _sig := p.(_sig);
     _t := match p.(_t) with
          | T _ k => T p.(_sig) (f k)
          end |}.

Extraction Implicit Build_pkg [_sig].
Extraction TestCompile map.
