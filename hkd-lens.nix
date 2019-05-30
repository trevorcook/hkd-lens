{ mkDerivation, base, stdenv }:
mkDerivation {
  pname = "hkd-lens";
  version = "0.0.0.0";
  src = ./.;
  libraryHaskellDepends = [ base ];
  homepage = "https://github.com/trevorcook/hkd-lens";
  description = "Generic lense/prism/traversal-kinded data";
  license = stdenv.lib.licenses.bsd3;
}
