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
    self,
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
      plantuml-pdf = pkgs.plantuml.overrideAttrs (old: rec {
        version = "1.2022.3";
        src = pkgs.fetchurl {
          url = "https://github.com/plantuml/plantuml/releases/download/v${version}/plantuml-pdf-${version}.jar";
          hash = "sha256-6ad6CUz1UAvNkhdUJhOME7OsLpIXiBoERfTmowzTz64=";
        };
      });

      inherit (pkgs.lib) hasSuffix mapAttrsToList drop splitString remove flatten;
      inherit (builtins) concatStringsSep readFile isString match path readDir;
      inherit (pkgs.lib.strings) sanitizeDerivationName;

      # plantuml ext => args
      transforms = {
        svg = "-tsvg";
        pdf = "-tpdf -Sshadowing=false";
        png = "-tpng";
      };

      transform = parent: name:
        pkgs.runCommandNoCC "transform-${sanitizeDerivationName name}" {
          buildInputs = [pkgs.moreutils plantuml-pdf];
          src = let
            content = readFile (parent + "/${name}");
            lines = splitString "\n" content;
            maybeIncludes =
              map (
                line:
                  if isString line
                  then match "!include (.+)" line
                  else null
              )
              lines;
            includes = [name] ++ (flatten ((remove null) maybeIncludes));
            toPath = include: {
              name = include;
              path = path {
                name = sanitizeDerivationName include;
                path = parent + "/${include}";
              };
            };
          in
            pkgs.linkFarm "includes" (map toPath includes);

          XDG_CONFIG_HOME = let
            fonts = with pkgs; [dejavu_fonts];
            cachedir = pkgs.makeFontsCache {fontDirectories = fonts;};
          in
            pkgs.writeTextDir "fontconfig/fonts.conf" ''
              <?xml version='1.0'?>
              <!DOCTYPE fontconfig SYSTEM 'urn:fontconfig:fonts.dtd'>
              <fontconfig>
                ${concatStringsSep "\n" (map (font: "<dir>${font}</dir>") fonts)}
                <cachedir>${cachedir}</cachedir>
              </fontconfig>
            '';
        } ''
          set -euo pipefail

          mkdir -p "$out"

          from="$src/${name}"
          to="$out/$(basename -s .puml "${name}")"

          ${concatStringsSep "\n" (mapAttrsToList (ext: args: ''
              echo "generate $to.${ext}"
              plantuml -failfast2 -pipe -charset UTF-8 -filedir "$src" ${args} < "$from" | sponge "$to.${ext}"
            '')
            transforms)}
        '';

      allPumls = parent:
        mapAttrsToList (
          name: type:
            if type == "directory"
            then allPumls (parent + "/${name}")
            else if (hasSuffix ".puml" name)
            then transform parent name
            else null
        ) (readDir parent);

      pumls = remove null (flatten (allPumls ./.));

      getName = s: concatStringsSep "/" (drop 4 (splitString "/" s));
    in rec {
      packages.pumls = pkgs.symlinkJoin {
        name = "pumls";
        paths = pumls;
      };

      packages.midnight-architecture = pkgs.stdenv.mkDerivation {
        name = "midnight-architecture";
        src = ./.;
        buildInputs = [plantuml-pdf];
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
        # graphviz and setting GRAPHVIZ_DOT environment variables are needed for IntelliJ integration, though it doesn't work quite well
        packages = [pkgs.graphviz];
        env = [
          {
            name = "GRAPHVIZ_DOT";
            value = "${pkgs.graphviz}/bin/dot";
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
            package = alejandra.defaultPackage.${system};
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
