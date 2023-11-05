final: prev:
let
  generated = import ../_sources/generated.nix;
  gen = prev.callPackage generated {};
in with gen; {
  agdaPackages = prev.agdaPackages // {
    standard-library = prev.agdaPackages.standard-library.overrideAttrs (_: { inherit (agda-stdlib) src;});
  };
}
