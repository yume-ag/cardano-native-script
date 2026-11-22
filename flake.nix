{
  description = "nsa: a formally verified Cardano native-script analyser";

  # Prebuilt lean-tui / lean-prism binaries (otherwise they build from source).
  # Nix asks before using a substituter declared by a flake.
  nixConfig = {
    extra-substituters = [ "https://wvhulle.cachix.org" ];
    extra-trusted-public-keys = [ "wvhulle.cachix.org-1:heXx8DZMiRsKUx6l1TxNoF+Nmtmz66QEdsonQzc1ir0=" ];
  };

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";

    # Lean-Prism: a language-server plugin that computes proof graphs.
    # It supports exactly one Lean version per branch; `main` is v4.35.0,
    # which is why ./lean-toolchain is pinned there.
    lean-prism.url = "git+https://codeberg.org/wvhulle/lean-prism?ref=main";

    # lean-tui: a terminal front-end for Lean-Prism.
    lean-tui = {
      url = "git+https://codeberg.org/wvhulle/lean-tui?ref=main";
      inputs.lean-prism.follows = "lean-prism";
    };
  };

  outputs = { self, nixpkgs, lean-prism, lean-tui }:
    let
      systems = [ "x86_64-linux" "aarch64-linux" "x86_64-darwin" "aarch64-darwin" ];
      forAllSystems = f: nixpkgs.lib.genAttrs systems (s: f s nixpkgs.legacyPackages.${s});
      # lean-tui is packaged for Linux, lean-prism for x86_64-linux only;
      # on other systems the shell just leaves them out.
      optionalPkg = flake: name: system:
        nixpkgs.lib.optional ((flake.packages or { }) ? ${system}) flake.packages.${system}.${name};
    in {
      # elan reads ./lean-toolchain and fetches the pinned Lean release,
      # so Lake stays in charge of the toolchain.
      devShells = forAllSystems (system: pkgs: {
        default = pkgs.mkShell {
          packages = [ pkgs.elan pkgs.python3 ]
            ++ optionalPkg lean-tui "lean-tui" system
            ++ optionalPkg lean-prism "lean-prism" system;
        };
      });
    };
}
