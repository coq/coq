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

{ pkgs ? import ./dev/nixpkgs.nix {}
, ocamlPackages ? pkgs.ocamlPackages
, buildIde ? true
, buildDoc ? true
, doInstallCheck ? true
, shell ? false
  # We don't use lib.inNixShell because that would also apply
  # when in a nix-shell of some package depending on this one.
, coq-version ? "8.10-git"
}:

with pkgs;
with stdenv.lib;

let packages = [ "coq" "coqide-server" ]
++ optional buildIde "coqide"
++ optional buildDoc "coq-refman"
; in

stdenv.mkDerivation rec {

  name = "coq";

  buildInputs = [
    hostname
    python2 # update-compat.py
    python3 time # coq-makefile timing tools
    dune
  ]
  ++ (with ocamlPackages; [ ocaml findlib num ])
  ++ optionals buildIde [
    ocamlPackages.lablgtk3-sourceview3
    glib gnome3.defaultIconTheme wrapGAppsHook
  ]
  ++ optionals buildDoc [
    # Sphinx doc dependencies
    pkgconfig (python3.withPackages
      (ps: [ ps.sphinx ps.sphinx_rtd_theme ps.pexpect ps.beautifulsoup4
             ps.antlr4-python3-runtime ps.sphinxcontrib-bibtex ]))
    antlr4
    ocamlPackages.odoc
  ]
  ++ optionals doInstallCheck (
    # Test-suite dependencies
    # ncurses is required to build an OCaml REPL
    optional (!versionAtLeast ocaml.version "4.07") ncurses
    ++ [ ocamlPackages.ounit rsync which ]
  )
  ++ optionals shell (
    [ jq curl gitFull gnupg ] # Dependencies of the merging script
    ++ (with ocamlPackages; [ merlin ocp-indent ocp-index utop ]) # Dev tools
    ++ [ graphviz ] # Useful for STM debugging
  );

  src =
    if shell then null
    else
      with builtins; filterSource
        (path: _:
           !elem (baseNameOf path) [".git" "result" "bin" "_build" "_build_ci" "nix"]) ./.;

  preConfigure = ''
    patchShebangs tools/
    patchShebangs dev/tools/
    configureFlagsArray+=("-libdir" "$OCAMLFIND_DESTDIR"coq "-native-compiler" "no")
  '' + optionalString doInstallCheck ''
    patchShebangs test-suite/
  '' + optionalString buildDoc ''
    patchShebangs doc/tools/
  '';

  prefixKey = "-prefix ";

  makefile = "Makefile.dune";

  createFindlibDestdir = !shell;

  buildFlags = [ "voboot" ];

  postBuild = ''
    for package in ${toString packages}
    do
      dune build $package.install
    done
  '';

  installPhase = ''
    runHook preInstall
    for package in ${toString packages}
    do
      dune install --prefix=$out --libdir=$OCAMLFIND_DESTDIR $package
    done
    runHook postInstall
  '';

  inherit doInstallCheck;

  preInstallCheck = ''
    export OCAMLPATH=$OCAMLFIND_DESTDIR:$OCAMLPATH
  '';

  installCheckTarget = [ "test-suite" ];

  passthru = {
    inherit coq-version ocamlPackages;
    dontFilter = true; # Useful to use mkCoqPackages from <nixpkgs>
  };

  setupHook = writeText "setupHook.sh" "
    addCoqPath () {
      if test -d \"$1/lib/coq/${coq-version}/user-contrib\"; then
        export COQPATH=\"$COQPATH\${COQPATH:+:}$1/lib/coq/${coq-version}/user-contrib/\"
      fi
    }

    addEnvHooks \"$targetOffset\" addCoqPath
  ";

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
    platforms = platforms.unix;
  };

}
