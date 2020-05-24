{ pkgs ? null
, ocamlPackages ? null
, buildDoc ? null
, doInstallCheck ? null
, coq-version ? null
} @ args: import ./default.nix (args // { shell = true; })
