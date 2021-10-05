# decorated-cospans

[![GitHub CI](https://github.com/o1lo01ol1o/decorated-cospans/workflows/ci.yml/badge.svg)](https://github.com/o1lo01ol1o/decorated-cospans/actions)
[![Hackage](https://img.shields.io/hackage/v/decorated-cospans.svg?logo=haskell)](https://hackage.haskell.org/package/decorated-cospans)

## Hacking

### Nix

If you're on `darwin` or `linux`, you can just [download nix](https://nixos.org/download.html)

If you're one windows, you'll need to install a WSL container for ubuntu or similar and then download nix there.

Pay attention to the end of the installation, you will likely need to add a configuration line to your shell environment.

### Haskell.nix

We're using Haskell.nix. [Make sure you add the IOHK binary cache to your subsituters.](https://input-output-hk.github.io/haskell.nix/tutorials/getting-started/)

### Cachix

Build arefacts are cached by [cachix](https://www.cachix.org/). You should download the client and then tell it to use these caches:

```bash
cachix use decorated-cospans
cachix use iohk
```

So long as there have been build artefacts already built for your system and pushed to the cache, you should see nix download them from `foo.cachix.org` during build or shell instantiation.

### VSCode

Install vs code and haskell language support vie the Haskell IDE engine (ID: `haskell.haskell`).

clone this repo to `somewhere/` and then enter a nix-shell and start code:

```bash
cd somewhere/
nix-shell
code .
```

### Hoogle

You can spawn a local hoogle server with documentation if you run the following _from outside a nix-shell_:

```bash
./scripts/hoogle
```
