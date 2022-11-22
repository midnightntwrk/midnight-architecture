{
  CI = {config, ...}: {
    preset = {
      nix.enable = true;

      github = let
        enable = config.actionRun.facts != {};
        repository = "input-output-hk/midnight-architecture";
        revision = config.preset.github.lib.readRevision "GitHub event" "";
      in {
        ci = {
          inherit enable repository revision;
        };
        status = {
          inherit enable repository revision;
          enableActionName = false;
        };
      };
    };

    dependencies = [
      "github:nixos/nixpkgs#rsync"
      "github:nixos/nixpkgs#gnugrep"
      "github:nixos/nixpkgs#findutils"
      "github:nixos/nixpkgs#gnupg"
    ];

    command.text = ''
      set -euxo

      nix build -L

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

      git commit --all --message render
      git show # just for the log

      # Commenting to check the rest - this expectedly fails
      # git push origin HEAD:$ {lib.escapeShellArg (lib.removePrefix "refs/heads/" cfg.ref)}
    '';

    memory = 1024 * 8;
    nomad = {
      resources.cpu = 5000;
      templates = [
        {
          destination = "${config.env.HOME}/.netrc";
          data = ''
            machine github.com
            login git
            password {{with secret "kv/data/cicero/github"}}{{.Data.data.token}}{{end}}

            machine api.github.com
            login git
            password {{with secret "kv/data/cicero/github"}}{{.Data.data.token}}{{end}}

            machine nexus.p42.at
            {{with secret "kv/data/cicero/nexus" -}}
              {{with .Data.data -}}
                login {{.user}}{{"\n" -}}
                password {{.password}}
              {{- end}}
            {{- end}}
          '';
        }
      ];

      env.NIX_CONFIG = "netrc-file = ${config.env.HOME}/.netrc";
    };
  };
}
