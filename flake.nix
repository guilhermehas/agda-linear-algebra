{
  description = "Linear Algebra in Agda";

  inputs.flake-utils.url = "github:numtide/flake-utils";
  inputs.flake-compat = {
    url = "github:edolstra/flake-compat";
    flake = false;
  };

  outputs = { self, flake-utils, flake-compat, nixpkgs }:
    let
        linear-algebra-overlay = final: prev: with prev.agdaPackages;
          {
            agdaPackages = prev.agdaPackages // {
                linear-algebra = mkDerivation {
                pname = "agda-dimensional-stdlib";
                version = "1.0.0";
                src = with lib; cleanSourceWith {
                  filter = name: type:
                    !(hasSuffix ".nix" name) && (name != "flake.lock")
                  ;
                  src = ./.;
                };
                everythingFile = "src/EverythingUseful.agda";
                buildInputs = [ standard-library ];
                LC_ALL = "en_US.UTF-8";
                nativeBuildInputs = [ final.glibcLocales ];
                meta = {};
              };
            };
          };
        standard-library-overlay = builtins.elemAt (import ./nix/overlay.nix nixpkgs.lib) 0;
        overlays = [ standard-library-overlay linear-algebra-overlay ];
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
    }) // rec {
      overlays = {
        inherit standard-library-overlay linear-algebra-overlay;
        default = linear-algebra-overlay;
      };
    };
}
