## Installing UniMath (Coq)

Exercises can be done on paper or using the UniMath library in the Coq proof assistant. (Or other libraries in other proof assistants if you dare!) Here are instructions for installing/using the UniMath library in the Coq proof assistant in order from easiest to hardest.

1. Use an in-browser implementation: https://unimath.github.io/live/

- This may or may not work because of some recent problem with browsers. If it doesn't work, use option 2. If it does load, but there are any problems, it would be appreciated if you could report them here: https://github.com/UniMath/UniMath/discussions/1729

2. Use the UniMath binaries and the CoqIDE both provided by the Coq Platform: https://github.com/rocq-prover/platform/releases/tag/2024.10.1

- Note that you *must* use the 2024.10.1 version, newer versions do not have Unimath.

3. Run the [Rocq platform scripts](https://rocq-prover.org/install) to install Rocq. Then install Unimath as per the instructions [here](https://rocq-prover.org/docs/using-opam#installing-rocq-packages). The name of the Unimath package is `coq-unimath`.

4. Use the UniMath binaries provided with recent distributions of Coq + VSCode: https://docs.google.com/document/d/1KWSugPK-sJ67pL-P4EtoKZ6HMzewmzewLNkR_arXauY/edit?usp=sharing

- Note that where there are paths like `/Applications/Coq-Platform~8.15~2022.04.app/Contents/Resources/bin` you need to check that this is where Coq is installed on your computer. In particular, if you have installed it recently, it will be something more like `Coq-Platform~8.16~2022.09.app`.
- To easily type unicode symbols, install the "Unicode Latex" extension for VSCode.
- Also make sure that the custom VS Code settings are not being applied whenever you want to work with vanilla Coq. This should be the case because the instructions have you apply them to a particular workspace.

5. Compile UniMath yourself + use Emacs: https://github.com/UniMath/UniMath/blob/master/INSTALL.md

- It is possible to mix up the instructions in 2 and 3, i.e. to compile UniMath yourself and use VSCode, or use the provided UniMath binaries with Emacs.
- You will need to put the files that you work on _within_ the `UniMath/UniMath` directory on your computer, to use their Emacs configuration files (or you can copy the Emacs configuration files).

6. Compile/install Coq and UniMath + use [(Neo)Vim](https://neovim.io/):

- first, either [compile or install Coq and UniMath](https://github.com/UniMath/UniMath/blob/master/INSTALL.md);
- then, install the [Coqtail vim plugin](https://github.com/whonore/Coqtail)
  (some Neovim distributions, such as
  [Visimp](https://github.com/lucat1/visimp), may already feature Coqtail
  support). As an experimental alternative, Neovim plugins
  [vscoq.nvim](https://github.com/tomtomjhj/vscoq.nvim) and
  [coq.lsp](https://github.com/tomtomjhj/coq-lsp.nvim) are clients for the
  [VsCoq 2](https://github.com/coq-community/vscoq) and the
  [coq-lsp](https://github.com/ejgallego/coq-lsp/) language servers,
  respectively.

7. Installing UniMath using [Nix](https://nixos.org/). The following instructions will assume familiarity with the Nix package manager.

   UniMath is not currently available in [nixpkgs](https://github.com/NixOS/nixpkgs/), and the only derivation I could find online was more than 11 years old. Thankfully, nixpkgs does contain infrastructure for building Rocq packages (see [the relevant section of the nixpkgs manual](https://nixos.org/manual/nixpkgs/unstable/index.html#sec-language-rocq) for reference). Indeed, one can build a copy of UniMath using the following derivation:

   ```nix
   { mkCoqDerivation, coq }:
   mkCoqDerivation {
     pname = "UniMath";
     owner = "UniMath";
     version = "v20250923";
     release."v20250923".sha256 = "sha256-NFBK/0ghMNxOZaLDjcToAUGyQnKT7KflLjTxFh7/4JQ=";
     nativeBuildInputs = [ coq ];
   }
   ```

   Instead of installing UniMath as a standalone package, one should prefer using `pkgs.coq.withPackages` (thus ensuring things like language servers have access to the library). As an example, one can make a UniMath-enabled rocq installation available together with the `vsrocq-language-server` (for use with things like the aforementioned [vscoq.nvim](https://github.com/tomtomjhj/vscoq.nvim) Neovim plugin) by using a Nix shell like the following:

   ```nix
   pkgs.mkShell {
     packages = [
       (pkgs.coq.withPackages (
         ps: with ps; [
           # Replace `import ./uni-math.nix` with any expression that evaluates to the
           # derivation above. For example, one could keep the derivation as part of
           # the same file by using a `let uni-math = ...; in ...` block.
           (callPackage (import ./uni-math.nix) { })
           vsrocq-language-server
         ]
       ))
     ];
   }
   ```

   Note that the above might take a fair bit to build the first time around (about an hour on my laptop).
