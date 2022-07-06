{pkgs}: let
  inherit (pkgs) lib;
  inherit (lib) trivial debug;

  collectFiles = startPath:
    debug.traceValSeq (trivial.pipe (debug.traceValSeq startPath) [
      (lib.sources.cleanSource)
      (src: lib.sources.sourceFilesBySuffices src [".puml"])
    ]);

  renderPumlsDerivation = source:
    pkgs.runCommand "render pumls" {buildInputs = [pkgs.plantuml];} ''
      set -euxo pipefail
      mkdir -p $out
      cp -R ${source.outPath}/ $out
      chmod -R 755 $out
      plantuml -tsvg "$out/**/*.puml"
      find $out -type f -name '*.puml' | xargs rm
    '';

  renderPumlsScript = pkgs.writeShellApplication {
    name = "render-pumls";
    runtimeInputs = [pkgs.plantuml];
    text = ''
      if [ -v 1 ]; then
        dir=$1
      else
        dir=$(pwd)
      fi

      spec=$(find "$dir" -type d -d 1 | grep -v '\/\.[[:alnum:]]' | sed 's/$/\/\*\*\/\*.puml/g' | tr '\n' ' ')

      echo "Rendering PlantUML diagrams at $spec"
      plantuml -tsvg "$spec"
    '';
  };
in {
  inherit collectFiles renderPumlsDerivation renderPumlsScript;
}
