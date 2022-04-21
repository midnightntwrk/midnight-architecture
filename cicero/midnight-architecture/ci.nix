{
  name,
  std,
  lib,
  actionLib,
  rev,
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
          {
            destination = "/local/.fonts.conf";
            data = ''
              <!DOCTYPE fontconfig SYSTEM "fonts.dtd">
              <fontconfig>
              <dir>/share/fonts/truetype</dir>
              </fontconfig>
            '';
          }
          {
            destination = "/local/.gitconfig";
            data = ''
              [user]
                name = iohk-devops
                email = devops@iohk.io

              [commit]
                gpgsign = true
            '';
          }
        ];

        resources.memory = 1024 * 3;

        env."HOME" = "/local";
        env."FONTCONFIG_PATH" = "/local/";
        env."FONTCONFIG_FILE" = "/local/.fonts.conf";
        env."GIT_CONFIG_GLOBAL" = "/local/.gitconfig";
      }

      {
        config.packages = std.data-merge.append [
          "github:input-output-hk/midnight-architecture/${rev}#plantuml"
          "github:nixos/nixpkgs#fontconfig"
          "github:nixos/nixpkgs#go-font"
          "github:nixos/nixpkgs#gnumake"
          "github:nixos/nixpkgs#gnugrep"
          "github:nixos/nixpkgs#gnupg"
          "github:nixos/nixpkgs#findutils"
          "github:nixos/nixpkgs#bash"
        ];
      }

      (std.git.clone cfg)

      (std.script "bash" ''
        set -euxo
        make
        git status --porcelain | grep -E '*.(png|pdf)' | cut -d ' ' -f 2 | xargs git add
        git commit -am "Generate missing png and pdf files"
        git push origin HEAD:cic-147
      '')
    ];
}
