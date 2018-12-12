# How to use?

# If you have Nix installed, you can get in an environment with everything
# needed to compile Coq and CoqIDE by running:
# $ nix-shell
# at the root of the Coq repository.

# How to tweak default arguments?

# nix-shell supports the --arg option (see Nix doc) that allows you for
# instance to do this:
# $ nix-shell --arg ocamlPackages "(import <nixpkgs> {}).ocaml-ng.ocamlPackages_4_05" --arg buildIde false

# You can also compile Coq and "install" it by running:
# $ make clean # (only needed if you have left-over compilation files)
# $ nix-build
# at the root of the Coq repository.
# nix-build also supports the --arg option, so you will be able to do:
# $ nix-build --arg doInstallCheck false
# if you want to speed up things by not running the test-suite.
# Once the build is finished, you will find, in the current directory,
# a symlink to where Coq was installed.

{ pkgs ?
    (import (fetchTarball {
      url = "https://github.com/NixOS/nixpkgs/archive/060a98e9f4ad879492e48d63e887b0b6db26299e.tar.gz";
      sha256 = "1lzvp3md0hf6kp2bvc6dbzh40navlyd51qlns9wbkz6lqk3lgf6j";
    }) {})
, ocamlPackages ? pkgs.ocaml-ng.ocamlPackages_4_06
, buildIde ? true
, buildDoc ? true
, doInstallCheck ? true
, shell ? false
  # We don't use lib.inNixShell because that would also apply
  # when in a nix-shell of some package depending on this one.
}:

with pkgs;
with stdenv.lib;

stdenv.mkDerivation rec {

  name = "coq";

  buildInputs = [
    hostname
    python2 time # coq-makefile timing tools
  ]
  ++ (with ocamlPackages; [ ocaml findlib camlp5_strict num ])
  ++ optional buildIde ocamlPackages.lablgtk
  ++ optionals buildDoc [
    # Sphinx doc dependencies
    pkgconfig (python3.withPackages
      (ps: [ ps.sphinx ps.sphinx_rtd_theme ps.pexpect ps.beautifulsoup4
             ps.antlr4-python3-runtime ps.sphinxcontrib-bibtex ]))
    antlr4
  ]
  ++ optionals doInstallCheck (
    # Test-suite dependencies
    # ncurses is required to build an OCaml REPL
    optional (!versionAtLeast ocaml.version "4.07") ncurses
    ++ [ ocamlPackages.ounit rsync which ]
  )
  ++ optionals shell (
    [ jq curl git gnupg ] # Dependencies of the merging script
    ++ (with ocamlPackages; [ merlin ocp-indent ocp-index ]) # Dev tools
  );

  src =
    if shell then null
    else
      with builtins; filterSource
        (path: _:
           !elem (baseNameOf path) [".git" "result" "bin" "_build_ci"]) ./.;

  prefixKey = "-prefix ";

  buildFlags = [ "world" "byte" ] ++ optional buildDoc "doc-html";

  installTargets =
    [ "install" "install-byte" ] ++ optional buildDoc "install-doc-html";

  inherit doInstallCheck;

  preInstallCheck = ''
    patchShebangs dev/tools/
    patchShebangs tools/
    patchShebangs test-suite/
  '';

  installCheckTarget = [ "check" ];

  passthru = { inherit ocamlPackages; };

  meta = {
    description = "Coq proof assistant";
    longDescription = ''
      Coq is a formal proof management system.  It provides a formal language
      to write mathematical definitions, executable algorithms and theorems
      together with an environment for semi-interactive development of
      machine-checked proofs.
    '';
    homepage = http://coq.inria.fr;
    license = licenses.lgpl21;
  };

}
