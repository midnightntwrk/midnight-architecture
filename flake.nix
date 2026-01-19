{
  description = "Flake for the midnight-architecture";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-25.11";
    devshell = {
      url = "github:numtide/devshell";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    utils = {
      url = "github:numtide/flake-utils";
    };
  };

  outputs = {
    self,
    nixpkgs,
    utils,
    devshell,
    ...
  }:
    utils.lib.eachSystem ["x86_64-linux" "x86_64-darwin" "aarch64-darwin"]
    (
      system: let
        pkgs = nixpkgs.legacyPackages.${system};
        plantuml = pkgs.plantuml;
      in {
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
              package = pkgs.nodejs_22;
              category = "runtime";
            }
            {
              package = plantuml;
              category = "diagram generator";
            }
          ];
        };
      }
    );
}
