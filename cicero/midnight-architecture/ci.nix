{
  name,
  std,
  lib,
  actionLib,
  ...
} @ args: {
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

  output = {start}: let
    cfg = start.value.${name}.start;
  in {
    success.${name} =
      {
        ok = true;
        revision = cfg.sha;
      }
      // lib.optionalAttrs (cfg ? ref) {
        inherit (cfg) ref default_branch;
      };
  };

  job = {start}: let
    cfg = start.value.${name}.start;
  in
    std.chain args [
      actionLib.simpleJob
      (std.github.reportStatus cfg.statuses_url or null)
      {
        template = std.data-merge.append [
          {
            destination = "secrets/netrc";
            data = ''
              machine github.com
              login git
              password {{with secret "kv/data/cicero/github"}}{{.Data.data.token}}{{end}}
            '';
          }
        ];
      }

      {
        config.packages = std.data-merge.append [
          "github:input-output-hk/midnight-architecture?ref=cic-147#plantuml_jar"
          "github:nixos/nixpkgs#fontconfig"
          "github:nixos/nixpkgs#go-font"
          "github:nixos/nixpkgs#gnumake"
          "github:nixos/nixpkgs#bash"
        ];
      }

      (std.git.clone cfg)

      {
        resources = {
          memory = 1024 * 3;
        };
      }

      {
        template = std.data-merge.append [{
          destination = "/local/.fonts.conf";
          data  = ''
            <!DOCTYPE fontconfig SYSTEM "fonts.dtd">
            <fontconfig>
           <dir>/share/fonts/truetype</dir>
           </fontconfig>
          '';
        }];

        env."HOME" = "/local";
        env."FONTCONFIG_PATH" = "/local/";
        env."FONTCONFIG_FILE" = "/local/.fonts.conf";
      }

      (std.script "bash" ''
        set -euxo
        plantuml -p -tpdf < flowlets/example.puml > flowlets/example.pdf
        ls -ahl
        ls -ahl flowlets/
        ls -ahl components/WalletBackend/
        git status
        make
        git status
      '')
    ];
}
