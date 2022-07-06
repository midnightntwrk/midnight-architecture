{
  description = "Flake for the midnight-architecture";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/release-22.05";
    devshell = {
      url = "github:numtide/devshell";
    };
    utils = {
      url = "github:numtide/flake-utils";
    };
    cicero = {
      url = "github:input-output-hk/cicero";
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

      inherit (pkgs.lib.trivial) pipe;

      plantLib = import ./nix/plantuml.nix {
        pkgs = pkgs;
      };
    in rec {
      packages.puml-renders = pipe ./. [(plantLib.collectFiles) (plantLib.renderFiles)];
      defaultPackage = packages.puml-renders;

      apps.render-pumls = {
        type = "app";
        program = plantLib.renderPumlsScript + "/bin/render-pumls";
      };

      apps.watch = let
        watcher = pkgs.writeShellApplication {
          name = "watch-pumls";
          runtimeInputs = [plantLib.renderPumlsScript pkgs.watchman];
          text = ''
            set -euxo pipefail

            if [ -v 1 ]; then
              dir=$1
            else
              dir=$(pwd)
            fi

            echo "Starting watchman to watch over *.puml files"
            watchman --foreground -j <<-EOT
              ["trigger", "$dir", {
                "name": "pumls",
                "expression": ["pcre", "\\\\.puml$"],
                "command": ["update-puml-renders", "$dir"]
              }]
            EOT
          '';
        };
      in {
        type = "app";
        program = watcher + "/bin/watch-pumls";
      };

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
            package = pkgs.plantuml;
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
