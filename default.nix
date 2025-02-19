# How to use?

# If you have Nix installed, you can get in an environment with everything
# needed to compile Rocq and RocqIDE by running:
# $ nix-shell
# at the root of the Rocq repository.

# How to tweak default arguments?

# nix-shell supports the --arg option (see Nix doc) that allows you for
# instance to do this:
# $ nix-shell --arg ocamlPackages "(import <nixpkgs> {}).ocaml-ng.ocamlPackages_4_09" --arg buildIde false

# You can also compile Rocq and "install" it by running:
# $ make clean # (only needed if you have left-over compilation files)
# $ nix-build
# at the root of the Rocq repository.
# nix-build also supports the --arg option, so you will be able to do:
# $ nix-build --arg doInstallCheck false
# if you want to speed up things by not running the test-suite.
# Once the build is finished, you will find, in the current directory,
# a symlink to where Rocq was installed.

{ pkgs ? import ./dev/nixpkgs.nix {}
, ocamlPackages ? pkgs.ocaml-ng.ocamlPackages_4_14
, buildIde ? true
, buildDoc ? true
, doInstallCheck ? true
, shell ? false
  # We don't use lib.inNixShell because that would also apply
  # when in a nix-shell of some package depending on this one.
, coq-version ? "8.14-git"
}:

with pkgs;
with pkgs.lib;

stdenv.mkDerivation rec {

  name = "coq";

  buildInputs = [
    hostname
    python311
    ocamlPackages.yojson
    ocamlPackages.camlzip
    # coq-makefile timing tools
    time
    dune_3
  ]
  ++ optionals buildIde [
    ocamlPackages.lablgtk3-sourceview3
    glib
    gnome.adwaita-icon-theme
    wrapGAppsHook
  ]
  ++ optionals buildDoc [
    # Sphinx doc dependencies
    pkg-config (python311.withPackages
      (ps: [ ps.sphinx ps.sphinx_rtd_theme ps.pexpect ps.beautifulsoup4
             (ps.antlr4-python3-runtime.override {antlr4 = pkgs.antlr4_9;}) ps.sphinxcontrib-bibtex ]))
    antlr4_9
    ocamlPackages.odoc
  ]
  ++ optionals doInstallCheck [
    # Test-suite dependencies
    ocamlPackages.ounit
    rsync
    which
  ]
  ++ optionals shell (
    [ # Dependencies of the merging script
      jq
      curl
      gitFull
      gnupg
    ]
    ++ (with ocamlPackages; [
      # Dev tools
      ocaml-lsp
      merlin
      ocp-indent
      ocp-index
      utop
      ocamlformat
      ])
    ++ [
      # Useful for STM debugging
      graphviz
    ]
  );

  # OCaml and findlib are needed so that native_compute works
  # This follows a similar change in the nixpkgs repo (cf. NixOS/nixpkgs#101058)
  # ocamlfind looks for zarith when building plugins
  # This follows a similar change in the nixpkgs repo (cf. NixOS/nixpkgs#94230)
  propagatedBuildInputs = with ocamlPackages; [ ocaml findlib zarith ];

  propagatedUserEnvPkgs = with ocamlPackages; [ ocaml findlib ];

  src =
    if shell then null
    else
      with builtins; filterSource
        (path: _:
           !elem (baseNameOf path) [".git" "result" "bin" "_build" "_build_ci" "_build_vo" "nix"]) ./.;

  preConfigure = ''
    patchShebangs dev/tools/ doc/corelib
  '';

  prefixKey = "-prefix ";

  enableParallelBuilding = true;

  buildFlags = [ "world" ] ++ optional buildIde "rocqide";

  # TODO, building of documentation package when not in dev mode
  # https://github.com/coq/coq/issues/16198
  # buildFlags = [ "world" ] ++ optional buildDoc "refman-html";

  # From https://github.com/NixOS/nixpkgs/blob/master/pkgs/build-support/ocaml/dune.nix
  installPhase = ''
    runHook preInstall
    dune install --prefix $out --libdir $OCAMLFIND_DESTDIR rocq-runtime coq-core rocq-core coqide-server ${optionalString buildIde "rocqide"}
    runHook postInstall
  '';

  # installTargets =
  #   [ "install" ];
    # fixme, do we have to do a target, or can we just do a copy?
    # ++ optional buildDoc "install-doc-html";

  createFindlibDestdir = !shell;

  postInstall = "ln -s $out/lib/rocq-runtime $OCAMLFIND_DESTDIR/rocq-runtime && ln -s $out/lib/coq-core $OCAMLFIND_DESTDIR/coq-core";

  inherit doInstallCheck;

  preInstallCheck = ''
    patchShebangs tools/
    patchShebangs test-suite/
    export OCAMLPATH=$OCAMLFIND_DESTDIR:$OCAMLPATH
  '';

  installCheckTarget = [ "check" ];

  passthru = {
    inherit coq-version ocamlPackages;
    dontFilter = true; # Useful to use mkCoqPackages from <nixpkgs>
  };

  setupHook = writeText "setupHook.sh" "
    addCoqPath () {
      if test -d \"$1/lib/coq/${coq-version}/user-contrib\"; then
        export ROCQPATH=\"\${ROCQPATH-}\${ROCQPATH:+:}$1/lib/coq/${coq-version}/user-contrib/\"
      fi
    }

    addEnvHooks \"$targetOffset\" addCoqPath
  ";

  meta = {
    description = "Rocq Prover";
    longDescription = ''
      The Rocq Prover is an interactive theorem prover, or proof assistant.  It provides a formal language
      to write mathematical definitions, executable algorithms and theorems
      together with an environment for semi-interactive development of
      machine-checked proofs.
    '';
    homepage = http://coq.inria.fr;
    license = licenses.lgpl21;
    platforms = platforms.unix;
  };

}
