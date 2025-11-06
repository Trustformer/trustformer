{
  description = "Trustformer";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    koika.url = "github:Trustformer/koika";
  };

  outputs = { self, nixpkgs, flake-utils, koika }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        name = "trustformer";

        pkgs = nixpkgs.legacyPackages.${system};
        ocamlPackages = koika.ocamlPackages.${system};
        coqPackages = koika.coqPackages.${system};

        z3_tptp = pkgs.writeScriptBin "z3_tptp" ''
          #!/bin/sh
          exec ${pkgs.z3-tptp}/bin/z3-tptp "$@"
        '';

        nativeBuildInputs = [
            ocamlPackages.ocaml
            ocamlPackages.dune_3

            koika.packages.${system}.default

            coqPackages.vscoq-language-server
            coqPackages.coq-hammer
            coqPackages.coq-hammer-tactics
            coqPackages.smtcoq

            pkgs.vampire
            pkgs.veriT
            pkgs.zchaff
            pkgs.cvc4
            pkgs.eprover
            pkgs.z3-tptp
            z3_tptp

            pkgs.yosys
          ];

        buildInputs = [
                   
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
