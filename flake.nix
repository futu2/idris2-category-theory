{
  description = "category theory in idris2";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";

    mission-control.url = "github:Platonic-Systems/mission-control";
    flake-root.url = "github:srid/flake-root";
  };

  outputs = inputs@{ flake-parts, ... }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      imports = [
        inputs.mission-control.flakeModule
        inputs.flake-root.flakeModule
      ];
      systems = [ "x86_64-linux" "aarch64-darwin" "x86_64-darwin" ];
      perSystem = { config, self', inputs', pkgs, system, ... }: {
        devShells.default = pkgs.mkShell {
          nativeBuildInputs = with pkgs; [ idris2 idris2Packages.idris2Lsp ];
          inputsFrom = [ config.mission-control.devShell config.flake-root.devShell ];
        };
        mission-control = {
          wrapperName = "run";
          scripts = {
            build = {
              description = "build idris2 project";
              exec = ''
                idris2 --build "$FLAKE_ROOT"/*.ipkg
              '';
              category = "Development";
            };
          };
        };
      };
    };
}
