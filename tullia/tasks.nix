{
  CI = {config, pkgs, lib, ...}: let
    ghLib = config.preset.github.lib;
    getBranch = factName: let
      fact = config.actionRun.facts.${factName};
    in
      fact.value.github_body.pull_request.head.ref;
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

      # disable octal utf8 display
      git config core.quotepath off

      if [[ -z "$(git status --porcelain)" ]]; then
        exit 0
      fi

      git config advice.addEmptyPathspec false

      git status --porcelain \
      | grep -E '.*.(png|pdf)' \
      | cut -d ' ' -f 2 \
      | xargs git add \
      || echo "Nothing to add"

      git config user.name iohk-devops
      git config user.email devops@iohk.io

      if git commit --all --message render; then
        git show # just for the log
        git push origin HEAD:${lib.escapeShellArg (getBranch "GitHub event")}
      else
        echo "Nothing to do"
      fi
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
