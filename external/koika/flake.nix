{
  description = "Koika version based on the SUSHI fork (https://gitlab.inria.fr/SUSHI-public/FMH/koika/).";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        name = "koika";

        pkgs = nixpkgs.legacyPackages.${system};

        coqPackages = pkgs.coqPackages_8_19;
        # This uses ocaml 4.14, while koika-sushi uses 5.11. If anything breaks consider updating 
        ocamlPackages = coqPackages.coq.ocamlPackages; 
        
        nativeBuildInputs = [
            pkgs.makeWrapper
            pkgs.gnumake
            pkgs.gpp

            ocamlPackages.ocaml
            ocamlPackages.dune_3
          ];
        
        buildInputs = [
            ocamlPackages.base
            ocamlPackages.core
            ocamlPackages.stdio
            ocamlPackages.parsexp
            ocamlPackages.hashcons
            ocamlPackages.zarith
            ocamlPackages.core_unix
            ocamlPackages.ppx_jane
            ocamlPackages.ppx_sexp_conv
            ocamlPackages.findlib # Required to make nix-managed ocaml libraries visible

            coqPackages.coq
            coqPackages.coq-record-update

            pkgs.boost
          ];

      in {

        ocamlPackages = ocamlPackages;
        coqPackages = coqPackages;

        packages.default = pkgs.coqPackages_8_19.mkCoqDerivation {
          pname = name;
          version = self.shortRev or "dev";
          src = self;

          overrideNativeBuildInputs = nativeBuildInputs;
          overrideBuildInputs = buildInputs;

          propagatedBuildInputs = buildInputs;

          useDune = true;
          opam-name = name;
          setCOQBIN = false;
        };

        devShell = pkgs.mkShell {
          nativeBuildInputs = nativeBuildInputs;
          buildInputs = buildInputs;
        };
      });
}
