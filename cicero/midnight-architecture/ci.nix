{ name, std, lib, actionLib, ... } @ args:

{

  inputs.start = ''
    "${name}": start: {
      // from both std/ci/{pr,push}
      sha: string
      clone_url: string
      statuses_url?: string

      // only from std/ci/push
      ref?: "refs/heads/\(default_branch)"
      default_branch?: string
    }
  '';

  output = { start }:
    let cfg = start.value.${name}.start; in
    {
      success.${name} = {
        ok = true;
        revision = cfg.sha;
      } // lib.optionalAttrs (cfg ? ref) {
        inherit (cfg) ref default_branch;
      };
    };

  job = { start }:
    let cfg = start.value.${name}.start; in
    std.chain args [
      actionLib.simpleJob
      (std.github.reportStatus cfg.statuses_url or null)
      {
        template = std.data-merge.append [{
          destination = "secrets/netrc";
          data = ''
            machine github.com
            login git
            password {{with secret "kv/data/cicero/github"}}{{.Data.data.token}}{{end}}
          '';
        }];
      }

      {
        config.packages = std.data-merge.append [
          "github:nixos/nixpkgs#plantuml"
        ];
      }

      (std.git.clone cfg)

      (std.script "bash" ''
        set -x

        function generate_png {
          local filename=$1
          java -jar /lib/plantuml.jar $(filename).puml -tpng > $(filename).png
        }

         # TODO enable pdf support for plantuml: https://plantuml.com/pdf
        function generate_pdf {
          local filename=$1
          java -jar /lib/plantuml.jar $(filename).puml -tpdf > $(filename).pdf
        }

        mkdir -p $out
        local unique_filenames=$(git diff --name-only | sed -n -E 's/.(png|puml)$//gp' | uniq -u)
        #local unique_filenames=$(git diff --name-only HEAD HEAD~1 | sed -n -E 's/.(png|puml)$//gp' | uniq -u)
        for line in $unique_filenames
        do
          generate_png $line
        done
      '')
    ];
}
