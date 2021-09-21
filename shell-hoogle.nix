# shell-hoogle.nix
let
  project = import ./default.nix;
in
  project.shellFor {
      packages = ps: [ps.decorated-cospans];
      withHoogle = true;
  }