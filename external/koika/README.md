# Kôika

This is a fork of [Kôika-SUSHI](https://gitlab.inria.fr/SUSHI-public/FMH/koika/) ([original home](https://github.com/mit-plv/koika)). 
Kôika is a rule-based Hardware Design Language embedded within Coq. 

## What's different from [Kôika-SUSHI](https://gitlab.inria.fr/SUSHI-public/FMH/koika/)?
* Packaged using [nix](https://nixos.org/)
* Typechecking changes required by Trustformer

## Installation

To use this packaged koika library you can add it to your `flake.nix` file, for example:

```nix
{
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    koika.url = "path:./external/koika";
  };

  outputs = { self, nixpkgs, flake-utils, koika }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};

        # The set of packages compatible with & used by koika
        ocamlPackages = koika.ocamlPackages.${system};
        coqPackages = koika.coqPackages.${system};

        nativeBuildInputs = [
            ocamlPackages.ocaml
            ocamlPackages.dune_3

            koika.packages.${system}.default
          ];

        buildInputs = [ ];

      in {
        devShell = pkgs.mkShell {
          nativeBuildInputs = nativeBuildInputs;
          buildInputs = buildInputs;
        };
      });
}
```

## Developing

To contribute to this koika fork you can run `nix develop` in the project directory to enter a development shell with all dependencies.
