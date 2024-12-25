{ pkgs ? import <nixpkgs> {} }:

pkgs.mkShell {
  buildInputs = [
    (pkgs.agda.withPackages (ps: [ ps.standard-library ps.cubical ]))
  ];
}
