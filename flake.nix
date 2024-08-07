{
  description = "Linear Algebra in Agda";

  inputs.flake-utils.url = "github:numtide/flake-utils";
  inputs.flake-compat = {
    url = "github:edolstra/flake-compat";
    flake = false;
  };

  outputs = { self, flake-utils, flake-compat, nixpkgs }:
    let
      filterL = lib: with lib; with builtins; name: type:
                  !(hasSuffix ".nix" name && type == "regular") &&
                  !(baseNameOf name == "flake.lock" && type == "regular") &&
                  !(baseNameOf name == "nix" && type == "directory");
      srcL = lib: with lib; cleanSourceWith {
          filter = filterL lib;
          src = ./.;
        };
        linear-algebra-overlay = final: prev: with prev.agdaPackages;
          let src = srcL lib; in
          {
            agdaPackages = prev.agdaPackages // {
                linear-algebra = mkDerivation {
                  pname = "linear-algebra";
                  version = "1.0.0";
                  inherit src;
                  everythingFile = "src/EverythingUseful.agda";
                  buildInputs = [ standard-library ];
                  LC_ALL = "en_US.UTF-8";
                  nativeBuildInputs = [ final.glibcLocales ];
                  meta = {};
                };
            };
            agda-linear-algebra-src = prev.stdenv.mkDerivation {
                name = "agda-linear-algebra-src";
                inherit src;
                phases = [ "unpackPhase" "installPhase" ];
                installPhase = ''
                  cp -r $src $out
                '';
              };
          };
        standard-library-overlay = builtins.elemAt (import ./nix/overlay.nix nixpkgs.lib) 0;
        overlays = [ linear-algebra-overlay ];
    in
    flake-utils.lib.eachDefaultSystem (system:
        let pkgs = import nixpkgs { inherit system overlays; };
        agda-all = pkgs.agda.withPackages (p: with p; [ standard-library ]);
        agda-with-linear-algebra = pkgs.agda.withPackages (p: with p; [ standard-library linear-algebra ]);
        linear-algebra = pkgs.agdaPackages.linear-algebra;
    in rec {
      packages = {
        inherit agda-all linear-algebra agda-with-linear-algebra;
        inherit (pkgs) agda-linear-algebra-src;
        html = pkgs.stdenv.mkDerivation {
          name = "html";
          buildInputs = [ agda-all ];

          src = srcL nixpkgs.lib;
          buildPhase = "agda --html src/EverythingUseful.agda";
          installPhase = "mv html $out";
        };
      };
      defaultPackage = packages.linear-algebra;
    }) // rec {
      overlays = {
        inherit standard-library-overlay linear-algebra-overlay;
        default = linear-algebra-overlay;
      };
    };
}
