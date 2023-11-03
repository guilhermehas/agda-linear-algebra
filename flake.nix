{
  description = "Linear Algebra in Agda";

  inputs.flake-utils.url = "github:numtide/flake-utils";
  inputs.flake-compat = {
    url = "github:edolstra/flake-compat";
    flake = false;
  };

  outputs = { self, flake-utils, flake-compat, nixpkgs }:
    let overlays = import ./nix/overlay.nix nixpkgs.lib; in
    flake-utils.lib.eachDefaultSystem (system:
        let pkgs = import nixpkgs { inherit system overlays; };
        agda-all = pkgs.agda.withPackages (p: with p; [ standard-library ]);
    in rec {
      packages = {
        inherit agda-all;
        linear-algebra = with pkgs; with agdaPackages;
          agdaPackages.mkDerivation {
            pname = "agda-dimensional-stdlib";
            version = "1.0.0";
            src = ./.;
            everythingFile = "src/EverythingUseful.agda";
            buildInputs = [ standard-library ];
            LC_ALL = "en_US.UTF-8";
            nativeBuildInputs = [ glibcLocales ];
            meta = {};
          };
      };
      defaultPackage = packages.linear-algebra;
    });
}
