prev: next:
let
  generated = import ../_sources/generated.nix;
  gen = prev.callPackage generated {};
in with gen; {
  agdaPackages = next.agdaPackages // {
    standard-library = next.agdaPackages.standard-library.overrideAttrs (_: { inherit (agda-stdlib) src;});
    cubical = next.agdaPackages.cubical.overrideAttrs (_: { inherit (cubical) src;});
  };
}
