let upstream =
      https://raw.githubusercontent.com/purescript/package-sets/prepare-0.15/src/packages.dhall
        sha256:d0da137c6c055afed41b301bcbcaecbf43ee7e553f4e7218241aeeab02cd59ed

in  upstream
  with metadata.version = "v0.15.0-alpha-02"
