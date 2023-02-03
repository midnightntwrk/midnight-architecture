{
  "midnight-architecture/ci" = {
    task = "CI";
    io = ''
      let github = {
        #input: "GitHub Push or PR"
        #repo: "input-output-hk/midnight-architecture"
      }

      #lib.merge
      #ios: [
        #lib.io.github_push & github & {#default_branch: true},
        #lib.io.github_pr   & github,
      ]
    '';
  };
}
