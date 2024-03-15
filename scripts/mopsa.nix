{ stdenv
, fetchFromGitLab
, ocamlPackages
, clang
, libclang
, libllvm
, flint
, mpfr
, pplite
}:

let inherit (ocamlPackages) ocaml findlib dune_3 menhir apron camlidl yojson zarith; in

stdenv.mkDerivation {
  pname = "mopsa";
  version = "2024-02-21";

  src = fetchFromGitLab {
    owner = "mopsa";
    repo = "mopsa-analyzer";
    rev = "5e4d8376716bc9ceae81be1f9e00b83a9615f1ab";
    hash = "sha256-q9h3WGg9kHeldRaYfBG8Lctl9ZmUHSBGmSsnDoVM00o=";
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
  ];

  buildInputs = [
    camlidl
    libclang
    flint
    pplite
    mpfr
  ];

  propagatedBuildInputs = [
    apron
    yojson
    zarith
  ];

  configureFlags = [
    #"--disable-c"
    "--disable-python"
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
