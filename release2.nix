let
  pkgs = import <nixpkgs> { };

in
  { generic-lens-HKD = pkgs.haskellPackages.callPackage ./generic-lens-HKD.nix { };
  }
