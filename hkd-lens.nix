{ mkDerivation, base, lens, one-liner, stdenv }:
mkDerivation {
  pname = "hkd-lens";
  version = "0.0.1";
  src = ./.;
  libraryHaskellDepends = [ base lens one-liner ];
  homepage = "https://github.com/trevorcook/hkd-lens";
  description = "Generic lens/prism/traversal-kinded data";
  license = stdenv.lib.licenses.bsd3;
}
