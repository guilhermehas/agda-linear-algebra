lib:
let
  folder = ./overlays;
  toImport = name: value: folder + ("/" + name);
  filterCaches = key: value: value == "regular" && lib.hasSuffix ".nix" key;
  overlaysToImport = lib.mapAttrsToList toImport (lib.filterAttrs filterCaches (builtins.readDir folder));
  overlays = map import overlaysToImport;
in overlays
