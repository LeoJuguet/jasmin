{ stdenv
, fetchFromGitLab
, ocamlPackages
, clang
, libclang
, libllvm
, flint
, mpfr
, rocmPackages
, pplite
, libffi
, gmp
}:

let inherit (ocamlPackages) ocaml findlib dune_3 menhir apron camlidl yojson zarith; in

stdenv.mkDerivation {
  pname = "mopsa";
  version = "2024-07-26";

  src = fetchFromGitLab {
    owner = "mopsa";
    repo = "mopsa-analyzer";
    rev = "3f5ca06292ace41c167dd066f214fb4c4184593c";
    hash = "sha256-DDnD9R4uTXPKQ0PStvEuntCLzlKweroTJFmYrb1KAY4=";
  };

  postPatch = ''
    patchShebangs bin
  '';

  nativeBuildInputs = [
    ocaml
    findlib
    dune_3
    menhir
    libllvm
    clang
    libffi
    gmp
  ];

  buildInputs = [
    camlidl
    libclang
    clang
    flint
    pplite
    mpfr
    libffi
    gmp
  ];

  propagatedBuildInputs = [
    apron
    yojson
    zarith
    libclang
    flint
    pplite
    mpfr
    libffi
    gmp
  ];

  configureFlags = [
    # "--disable-c"
    # "--disable-python"
  ];

  buildPhase = ''
    runHook preBuild
    dune build --profile release -p mopsa
    runHook postBuild
  '';

  installPhase = ''
    runHook preInstall
    dune install --profile release --prefix=$out --libdir=$OCAMLFIND_DESTDIR
    runHook postInstall
  '';

  strictDeps = true;

  meta = {
  };
}
