{ ocamlPackages, ssreflect, coq-ext-lib, simple-io }:
{
  buildInputs = [ ssreflect coq-ext-lib simple-io ]
  ++ (with ocamlPackages; [ ocaml findlib ocamlbuild num ]);
}
