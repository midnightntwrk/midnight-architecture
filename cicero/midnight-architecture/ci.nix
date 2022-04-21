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

        resources = {
          cpu = 800;
          memory = 1024 / 2;
        };
      }

      {
        config.packages = std.data-merge.append [
          "github:nixos/nixpkgs#rsync"
          "github:nixos/nixpkgs#gnugrep"
          "github:nixos/nixpkgs#gnupg"
        ];
      }

      (std.git.clone cfg)

      std.nix.build

      (std.script "bash" ''
        set -euxo

        rsync -r result/ .

        if [[ -z "$(git status --porcelain)" ]]; then
          exit 0
        fi

        git status --porcelain \
        | grep -E '*.(png|pdf)' \
        | cut -d ' ' -f 2 \
        | xargs git add

        git config user.name iohk-devops
        git config user.email devops@iohk.io
        git config commit.gpgSign true

        git commit --all --message render
        git show # just for the log

        git push origin HEAD:cic-147
      '')
    ];
}
