{
  inputs.flake-utils.url = "github:numtide/flake-utils";

  outputs = { self, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        nixpkgs = import ./dev/nixpkgs.nix { system = system; };
      in {
        packages = nixpkgs.coq.override { version = ./.; };
        defaultPackage = self.packages.${system};
        devShell = import ./default.nix { pkgs = nixpkgs; shell = true; };
      }
    );
}
