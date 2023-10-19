{
  description = "Linear Algebra in Agda";

  inputs.flake-utils.url = "github:numtide/flake-utils";
  inputs.flake-compat = {
    url = "github:edolstra/flake-compat";
    flake = false;
  };

  outputs = { self, flake-utils, flake-compat, nixpkgs }:
    flake-utils.lib.eachDefaultSystem (system:
    let overlays = import ./nix/overlay.nix nixpkgs.lib;
        pkgs = import nixpkgs { inherit system overlays; };
        agda-all = pkgs.agda.withPackages (with pkgs.agdaPackagesNew; [ standard-library ]);
    in rec {
      packages = {
        inherit agda-all;
        linear-algebra = with pkgs; with agdaPackagesNew;
          agdaPackages.mkDerivation {
            pname = "agda-dimensional-stdlib";
            version = "1.0.0";
            src = ./src;
            everythingFile = "Everything.agda";
            buildInputs = [ standard-library ];
            LC_ALL = "en_US.UTF-8";
            nativeBuildInputs = [ glibcLocales ];
            meta = {};
          };
      };
      defaultPackage = packages.linear-algebra;
    });
}
