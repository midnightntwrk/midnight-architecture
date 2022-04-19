{
  description = "Flake for the midnight-architecture";

  inputs = {
    devshell.url = "github:numtide/devshell";
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    utils.url = "github:numtide/flake-utils";
    alejandra.url = "github:kamadorueda/alejandra";
    cicero = {
      url = "github:input-output-hk/cicero";
      inputs = {
        nixpkgs.follows = "nixpkgs";
        utils.follows = "utils";
      };
    };
  };

  outputs = { nixpkgs, utils, devshell, alejandra, cicero, ... }:
  let
    supportedSystems = ["x86_64-linux" "x86_64-darwin" "aarch64-darwin"];
  in
    utils.lib.eachSystem supportedSystems
      (system:
        let
          pkgs = nixpkgs.legacyPackages.${system};
          packages = {

            midnight-architecture = pkgs.stdenv.mkDerivation {
              name = "midnight-architecture";
              src = ./.;
              buildInputs = with pkgs; [
                plantuml
                jre
              ];
              buildPhase = ''
                function generate_png {

                  local filename=$1
                  local fileWithoutSuffix=$(filename%".puml")

                  java -jar ${pkgs.plantuml}/lib/plantuml.jar $(filename) -tpng > $(fileWithoutSuffix).png
                }

                 # TODO enable pdf support for plantuml: https://plantuml.com/pdf
                function generate_pdf {

                  local filename=$1
                  local fileWithoutSuffix=$(filename%".puml")

                  java -jar ${pkgs.plantuml}/lib/plantuml.jar $(filename) -tpdf > $(fileWithoutSuffix).pdf
                }

                generate_png flowlets/example.puml
              '';

              installPhase = ''
                mkdir -p $out
                cp --parents flowlets/example.png $out
              '';
            };
          };

        in {
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

          defaultPackage = packages.midnight-architecture;

          ciceroActions = cicero.lib.callActionsWithExtraArgs
            rec {
              inherit (cicero.lib) std;
              inherit (nixpkgs) lib;
              actionLib = import "${cicero}/action-lib.nix" { inherit std lib; };
            }./cicero;
      });
}
