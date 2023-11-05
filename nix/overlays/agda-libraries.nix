prev: super:
let
  generated = import ../_sources/generated.nix;
  gen = super.callPackage generated {};
in with gen; {
  agdaPackages = super.agdaPackages // {
    standard-library = super.agdaPackages.standard-library.overrideAttrs (_: { inherit (agda-stdlib) src;});
  };
}
