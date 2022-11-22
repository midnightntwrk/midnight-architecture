{
  "midnight-architecture/ci" = {
    task = "CI";
    io = ''
      let github = {
        #input: "GitHub event"
        #repo: "input-output-hk/midnight-architecture"
      }
      #lib.merge
      #ios: [
        #lib.io.github_push & github,
        #lib.io.github_pr   & github,
      ]
    '';
  };
}
