{
  description = "A Sudoku formalization in Lean";

  inputs = {
    lean = {
      url = github:leanprover/lean4;
    };
    nixpkgs.url = github:nixos/nixpkgs/nixos-21.05;
    flake-utils = {
      url = github:numtide/flake-utils;
      inputs.nixpkgs.follows = "nixpkgs";
    };
    # A lean dependency
    lean-ipld = {
      url = github:yatima-inc/lean-ipld;
      inputs.lean.follows = "lean";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = { self, lean, flake-utils, nixpkgs, lean-ipld }:
    let
      supportedSystems = [
        # "aarch64-linux"
        # "aarch64-darwin"
        "i686-linux"
        "x86_64-darwin"
        "x86_64-linux"
      ];
    in
    flake-utils.lib.eachSystem supportedSystems (system:
      let
        leanPkgs = lean.packages.${system};
        pkgs = nixpkgs.legacyPackages.${system};
        name = "Sudoku";  # must match the name of the top-level .lean file
        Sudoku = leanPkgs.buildLeanPackage {
          inherit name;
          # deps = with leanPkgs; [ Init Lean ];#lean-ipld.project.${system} ];
          # Where the lean files are located
          src = ./src;
        };
        cli = leanPkgs.buildLeanPackage {
          name = "Sudoku.Cli";
          deps = [ Sudoku ];
          src = ./src;
        };
        test = leanPkgs.buildLeanPackage {
          name = "Tests";
          deps = [ Sudoku ];
          # Where the lean files are located
          src = ./test;
        };
        joinDepsDerivations = getSubDrv:
          pkgs.lib.concatStringsSep ":" (map (d: (builtins.tryEval "${getSubDrv d}").value) ([ ] ++ Sudoku.allExternalDeps));
      in
      {
        inherit Sudoku test;
        packages = {
          ${name} = Sudoku.sharedLib;
          cli = cli.executable;
          test = test.executable;
        };

        checks.test = test.executable;

        defaultPackage = self.packages.${system}.cli;
        devShell = pkgs.mkShell {
          buildInputs = with pkgs; [
            leanPkgs.lean
          ];
          LEAN_PATH = joinDepsDerivations (d: d.modRoot);
          LEAN_SRC_PATH = "./src:./test:" + joinDepsDerivations (d: d.src);
        };
      });
}
