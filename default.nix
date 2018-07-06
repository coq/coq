# How to use?

# If you have Nix installed, you can get in an environment with everything
# needed to compile Coq and CoqIDE by running:
# $ nix-shell
# at the root of the Coq repository.

# How to tweak default arguments?

# nix-shell supports the --arg option (see Nix doc) that allows you for
# instance to do this:
# $ nix-shell --arg ocamlPackages "(import <nixpkgs> {}).ocamlPackages_latest" --arg buildIde false

# You can also compile Coq and "install" it by running:
# $ make clean # (only needed if you have left-over compilation files)
# $ nix-build
# at the root of the Coq repository.
# nix-build also supports the --arg option, so you will be able to do:
# $ nix-build --arg doCheck false
# if you want to speed up things by not running the test-suite.
# Once the build is finished, you will find, in the current directory,
# a symlink to where Coq was installed.

{ pkgs ?
    (import (fetchTarball
      "https://github.com/NixOS/nixpkgs/archive/4345a2cef228a91c1d6d4bf626a0f933eb8cc4f9.tar.gz")
    {})
, ocamlPackages ? pkgs.ocamlPackages
, buildIde ? true
, buildDoc ? true
, doCheck ? true
}:

with pkgs;
with stdenv.lib;

stdenv.mkDerivation rec {

  name = "coq";

  buildInputs = (with ocamlPackages; [

    # Coq dependencies
    ocaml
    findlib
    camlp5_strict
    num

  ]) ++ (if buildIde then [

    # CoqIDE dependencies
    ocamlPackages.lablgtk

  ] else []) ++ (if buildDoc then [

    # Sphinx doc dependencies
    pkgconfig (python3.withPackages
      (ps: [ ps.sphinx ps.sphinx_rtd_theme ps.pexpect ps.beautifulsoup4
             ps.antlr4-python3-runtime ps.sphinxcontrib-bibtex ]))
     antlr4

  ] else []) ++ (if doCheck then

    # Test-suite dependencies
    # ncurses is required to build an OCaml REPL
    optional (!versionAtLeast ocaml.version "4.07") ncurses
    ++ [
    python
    rsync
    which

  ] else []) ++ (if lib.inNixShell then [
    ocamlPackages.merlin
    ocamlPackages.ocp-indent
    ocamlPackages.ocp-index
  ] else []);

  src =
    if lib.inNixShell then null
    else
      with builtins; filterSource
        (path: _: !elem (baseNameOf path) [".git" "result" "bin"]) ./.;

  prefixKey = "-prefix ";

  buildFlags = optionals buildDoc [ "world" "sphinx" ];

  installTargets = [ "install" ] ++ optional buildDoc "install-doc-sphinx";

  inherit doCheck;

}
