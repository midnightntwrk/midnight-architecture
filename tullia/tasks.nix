{
  CI = {config, pkgs, ...}: let
    ghLib = config.preset.github.lib;
  in {
    preset = {
      nix.enable = true;

      github = let
        enable = config.actionRun.facts != {};
        repository = "input-output-hk/midnight-architecture";
        revision = ghLib.readRevision "GitHub event" "";
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

    dependencies = with pkgs; [
      rsync
      gnugrep
      findutils
      gnupg
    ];

    command.text = ''
      set -euxo

      nix build -L

      rsync -r result/ .

      if [[ -z "$(git status --porcelain)" ]]; then
        exit 0
      fi

      //In case it doesn't find anything
      git config advice.addEmptyPathspec false

      git status --porcelain \
      | grep -E '\*.(png|pdf)' \
      | cut -d ' ' -f 2 \
      | xargs git add

      git config user.name iohk-devops
      git config user.email devops@iohk.io

      git commit --all --message render
      git show # just for the log

      # Commenting for now
      # git push origin HEAD:$ {ghLib.escapeShellArg (ghLib.removePrefix "refs/heads/" ghLib.ref)}
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
          '';
        }
      ];

      env.NIX_CONFIG = "netrc-file = ${config.env.HOME}/.netrc";
    };
  };
}
