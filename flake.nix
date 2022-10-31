{
  description = "Flake for the midnight-architecture";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/release-22.05";
    devshell = {
      url = "github:numtide/devshell";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    utils = {
      url = "github:numtide/flake-utils";
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
    self,
    nixpkgs,
    utils,
    devshell,
    cicero,
    ...
  }:
    utils.lib.eachSystem ["x86_64-linux" "x86_64-darwin" "aarch64-darwin"]
    (system: let
      pkgs = nixpkgs.legacyPackages.${system};
      plantuml-pdf = pkgs.plantuml.overrideAttrs (old: rec {
        version = "1.2022.3";
        src = pkgs.fetchurl {
          url = "https://github.com/plantuml/plantuml/releases/download/v${version}/plantuml-pdf-${version}.jar";
          hash = "sha256-6ad6CUz1UAvNkhdUJhOME7OsLpIXiBoERfTmowzTz64=";
        };
      });
    in rec {
      packages.midnight-architecture = pkgs.stdenv.mkDerivation {
        name = "midnight-architecture";
        src = ./.;
        buildInputs = [
          plantuml-pdf
        ];
        installPhase = ''
          make -p \
          | grep '^default:' \
          | cut -d ' ' -f 2- --output-delimiter $'\n' \
          | while read -r; do
            mkdir -p $out/"$(dirname "$REPLY")"
            mv "$REPLY" $out/"$REPLY"
          done
        '';
      };

      defaultPackage = packages.midnight-architecture;

      devShell = devshell.legacyPackages.${system}.mkShell {
        # graphviz and setting GRAPHVIZ_DOT environment variables are needed for editors integration, though it doesn't work quite well
        packages = [pkgs.graphviz pkgs.jdk];
        env = [
          {
            name = "GRAPHVIZ_DOT";
            value = pkgs.graphviz + "/bin/dot";
          }
          {
            name = "JAVA_HOME";
            value = pkgs.jdk;
          }
        ];
        commands = [
          {
            package = "adrgen";
            category = "ADR";
          }
          {
            package = "treefmt";
            category = "formatter";
          }
          {
            package = pkgs.alejandra;
            category = "formatter";
          }
          {
            package = plantuml-pdf;
            category = "diagram generator";
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
