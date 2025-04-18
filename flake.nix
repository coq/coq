{
  inputs.flake-utils.url = "github:numtide/flake-utils";

  outputs = { flake-utils, ... }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import ./dev/nixpkgs.nix { inherit system; };
      in {
        packages.default = import ./default.nix { inherit pkgs; };
        devShell = import ./default.nix { inherit pkgs; shell = true; };
      }
    );
}
