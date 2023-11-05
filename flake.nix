{
  description = "Linear Algebra in Agda";

  inputs.flake-utils.url = "github:numtide/flake-utils";
  inputs.flake-compat = {
    url = "github:edolstra/flake-compat";
    flake = false;
  };

  outputs = { self, flake-utils, flake-compat, nixpkgs }:
    let
        linear-algebra-overlay = prev: next: with next.agdaPackages;
          {
            agdaPackages = next.agdaPackages // {
                linear-algebra = mkDerivation {
                pname = "agda-dimensional-stdlib";
                version = "1.0.0";
                src = ./.;
                everythingFile = "src/EverythingUseful.agda";
                buildInputs = [ standard-library ];
                LC_ALL = "en_US.UTF-8";
                nativeBuildInputs = [ prev.glibcLocales ];
                meta = {};
              };
            };
          };
        overlays = import ./nix/overlay.nix nixpkgs.lib ++ [ linear-algebra-overlay ];
    in
    flake-utils.lib.eachDefaultSystem (system:
        let pkgs = import nixpkgs { inherit system overlays; };
        agda-all = pkgs.agda.withPackages (p: with p; [ standard-library ]);
        linear-algebra = pkgs.agdaPackages.linear-algebra;
    in rec {
      packages = {
        inherit agda-all linear-algebra;
      };
      defaultPackage = packages.linear-algebra;
    }) // { inherit overlays; };
}
