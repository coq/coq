{ ocamlPackages, ssreflect, coq-ext-lib, simple-io }:
{
  buildInputs = with ocamlPackages; [ ocaml findlib ocamlbuild num ];
  coqBuildInputs = [ ssreflect coq-ext-lib simple-io ];
}
