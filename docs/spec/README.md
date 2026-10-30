# The fir specification

The rendered spec is published at <https://p.ocmatos.com/funk/>. It is
rebuilt and deployed from every push to `main`, and each page names the
commit it was built from (ADR-2026-10-30-1031, ADR-2026-10-30-1046).

fir's specification is literate Lean, rendered with Verso
(ADR-2026-10-29-2015). Its chapters are the Lean modules of the package `fir`
in [`lean/`](../../lean), where each definition sits beside its prose. This
directory is the Verso document that renders them:
[`FirSpec.lean`](FirSpec.lean) gives the order of the chapters and the prose
that belongs to no definition.

Build the Lean code and render the document with:

```sh
scripts/build-spec.sh            # writes docs/spec/_out/html-multi/index.html
scripts/build-spec.sh --update   # for a toolchain bump: lake update, then build
```

The toolchain, the dependencies and the build are recorded in
ADR-2026-10-29-2135. The rendered document is a build output and is not
committed.
