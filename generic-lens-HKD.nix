{ mkDerivation, base, lens, stdenv }:
mkDerivation {
  pname = "generic-lens-HKD";
  version = "0.0.0.0";
  src = ./.;
  libraryHaskellDepends = [ base lens ];
  homepage = "https://github.com/trevorcook/generic-lens-HKD";
  description = "Generic lenses/prisms/traversals kinded data";
  license = stdenv.lib.licenses.bsd3;
}
