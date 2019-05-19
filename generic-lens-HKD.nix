{ mkDerivation, base, lens, one-liner, stdenv }:
mkDerivation {
  pname = "generic-lens-HKD";
  version = "0.0.0.0";
  src = ./.;
  libraryHaskellDepends = [ base lens one-liner ];
  homepage = "https://github.com/trevorcook/generic-lens-HKD";
  description = "Generic lenses/prisms/traversals kinded data";
  license = stdenv.lib.licenses.bsd3;
}
