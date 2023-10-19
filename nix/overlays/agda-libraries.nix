prev: next:
let
  generated = import ../_sources/generated.nix;
  gen = prev.callPackage generated {};
in with gen; {
  agdaPackagesNew = {
    standard-library = prev.agdaPackages.standard-library.overrideAttrs (_: {src = agda-stdlib.src;});
    cubical = prev.agdaPackages.cubical.overrideAttrs (_: {src = cubical.src;});
  };
}
