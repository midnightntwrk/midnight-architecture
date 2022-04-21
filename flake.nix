{
  description = "Flake for the midnight-architecture";

  inputs = {
    devshell = {
      url = "github:numtide/devshell";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    utils.url = "github:numtide/flake-utils";
    alejandra = {
      url = "github:kamadorueda/alejandra";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    cicero = {
      url = "github:input-output-hk/cicero";
      inputs = {
        nixpkgs.follows = "nixpkgs";
        utils.follows = "utils";
      };
    };
  };

  outputs = {
    nixpkgs,
    utils,
    devshell,
    alejandra,
    cicero,
    ...
  }:
    utils.lib.eachSystem ["x86_64-linux" "x86_64-darwin" "aarch64-darwin"]
    (system: let
      pkgs = nixpkgs.legacyPackages.${system};
    in rec {
      packages = {
        plantuml = pkgs.plantuml.overrideAttrs (old: rec {
          version = "1.2022.3";
          src = pkgs.fetchurl {
            url = "https://github.com/plantuml/plantuml/releases/download/v${version}/plantuml-pdf-${version}.jar";
            hash = "sha256-6ad6CUz1UAvNkhdUJhOME7OsLpIXiBoERfTmowzTz64=";
          };
        });

        midnight-architecture = pkgs.stdenv.mkDerivation {
          name = "midnight-architecture";
          src = ./.;
          buildInputs = [ packages.plantuml ];
          installPhase = ''
            mkdir -p $out
          '';
        };
      };

      defaultPackage = packages.midnight-architecture;

      devShell = devshell.legacyPackages.${system}.mkShell {
        commands = [
          {
            package = "treefmt";
            category = "formatter";
          }
          {
            package = alejandra.defaultPackage.${system};
            category = "formatter";
          }
        ];
      };
    })
    // {
      ciceroActions =
        cicero.lib.callActionsWithExtraArgs
        rec {
          inherit (cicero.lib) std;
          inherit (nixpkgs) lib;
          actionLib = import "${cicero}/action-lib.nix" {inherit std lib;};
        }
        ./cicero;
    };
}
