let
  pkgs = import <nixpkgs> { };

in
  { hkd-lens = pkgs.haskellPackages.callPackage ./hkd-lens.nix { };
  }
